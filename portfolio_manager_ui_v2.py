from __future__ import annotations

import datetime as dt
import json
import importlib.util
import math
import re
import shutil
import sys
import tempfile
import threading
import time
import tkinter as tk
import zipfile
from dataclasses import dataclass
from pathlib import Path
from queue import Empty, Queue
from tkinter import filedialog, messagebox, ttk
from xml.etree import ElementTree as ET

_YF_MODULE = None
_NP_MODULE = None
_PD_MODULE = None
_OPENPYXL_LOAD_WORKBOOK = None


def _load_yfinance():
    global _YF_MODULE
    if _YF_MODULE is not None:
        return _YF_MODULE

    spec = importlib.util.find_spec("yfinance")
    if spec is None or spec.loader is None:  # pragma: no cover - runtime only
        _YF_MODULE = False
        return None

    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    _YF_MODULE = module
    return module


def _load_numpy():
    global _NP_MODULE
    if _NP_MODULE is not None:
        return _NP_MODULE
    import numpy as np  # type: ignore

    _NP_MODULE = np
    return np


def _load_pandas():
    global _PD_MODULE
    if _PD_MODULE is not None:
        return _PD_MODULE
    import pandas as pd  # type: ignore

    _PD_MODULE = pd
    return pd


def _load_workbook_loader():
    global _OPENPYXL_LOAD_WORKBOOK
    if _OPENPYXL_LOAD_WORKBOOK is not None:
        return _OPENPYXL_LOAD_WORKBOOK
    from openpyxl import load_workbook

    _OPENPYXL_LOAD_WORKBOOK = load_workbook
    return load_workbook


META_FILE_SUFFIX = "108nodes new meta.xlsx"
META_DATE_RE = re.compile(r"(?P<date>\d{2}\.\d{2}\.\d{4})\s+108nodes new meta\.xlsx$", re.IGNORECASE)
META_START_DATE = dt.date(2026, 4, 24)
META_SHEET_NAME = "basic"
META_START_ROW = 6
META_COLS_MULTI = {
    "ticker": "B",
    "1w_pred": "BW", "1w_std": "CG",
    "4w_pred": "BY", "4w_std": "CH",
    "13w_pred": "CA", "13w_std": "CI",
    "26w_pred": "CC", "26w_std": "CJ",
    "52w_pred": "CE", "52w_std": "CK"
}


@dataclass
class StockRecord:
    ticker: str
    sharpe: float
    forecast_pct: float
    std_pct: float
    upside_pct: float = 0.0
    is_synthetic: bool = False
    horizon_data: dict | None = None



@dataclass
class TradeLine:
    ticker: str
    current_czk: float
    target_czk: float
    delta_czk: float
    action: str
    sharpe: float
    forecast_pct: float
    std_pct: float
    upside_pct: float = 0.0
    horizon_data: dict | None = None


@dataclass
class OptimizationResult:
    records: list[StockRecord]
    weights: np.ndarray
    sharpe: float
    expected_return: float
    volatility: float
    sold_czk: float
    penalty_czk: float
    invested_czk: float
    trades: list[TradeLine]
    target_total_czk: float
    current_total_czk: float
    extra_cash_czk: float
    position_changes: int
    min_trade_czk: float


def _safe_float(value, default: float = 0.0) -> float:
    if value is None:
        return default
    if isinstance(value, str):
        cleaned = value.replace("%", "").replace(" ", "").replace(",", ".").strip()
        if not cleaned:
            return default
        return float(cleaned)
    return float(value)


def _project_to_simplex(weights: np.ndarray) -> np.ndarray:
    np = _load_numpy()
    vector = np.asarray(weights, dtype=float)
    if vector.size == 0:
        return vector
    vector = np.nan_to_num(vector, nan=0.0, posinf=0.0, neginf=0.0)
    vector = np.maximum(vector, 0.0)
    total = vector.sum()
    if total <= 0:
        return np.ones_like(vector) / len(vector)
    if abs(total - 1.0) < 1e-12:
        return vector

    u = np.sort(vector)[::-1]
    cssv = np.cumsum(u)
    rho = np.nonzero(u * np.arange(1, len(u) + 1) > (cssv - 1.0))[0]
    if len(rho) == 0:
        return np.ones_like(vector) / len(vector)
    rho_idx = rho[-1]
    theta = (cssv[rho_idx] - 1.0) / (rho_idx + 1)
    projected = np.maximum(vector - theta, 0.0)
    projected_sum = projected.sum()
    if projected_sum <= 0:
        return np.ones_like(vector) / len(vector)
    return projected / projected_sum


def _safe_covariance_matrix(stds: np.ndarray, corr: np.ndarray) -> np.ndarray:
    np = _load_numpy()
    corr = np.asarray(corr, dtype=float)
    if corr.size == 0:
        return corr
    corr = np.nan_to_num(corr, nan=0.0, posinf=0.0, neginf=0.0)
    np.fill_diagonal(corr, 1.0)
    shrink = 0.15
    corr = (1.0 - shrink) * corr + shrink * np.eye(len(corr))
    stds = np.asarray(stds, dtype=float).reshape(-1, 1)
    cov = corr * (stds @ stds.T)
    cov += np.eye(len(stds)) * 1e-8
    return cov


def _resolve_target_amounts_after_penalty(
    weights: np.ndarray,
    current_amounts: np.ndarray,
    total_capital: float,
    sale_penalty_rate: float,
    max_iter: int = 100,
) -> tuple[np.ndarray, float, float, float]:
    np = _load_numpy()
    weights = _project_to_simplex(weights)
    current_amounts = np.asarray(current_amounts, dtype=float)

    invested_capital = float(total_capital)
    for _ in range(max_iter):
        target_amounts = weights * invested_capital
        sold_amount = float(np.maximum(current_amounts - target_amounts, 0.0).sum())
        penalty_czk = sold_amount * sale_penalty_rate
        next_invested_capital = max(0.0, float(total_capital) - penalty_czk)
        if abs(next_invested_capital - invested_capital) < 1e-8:
            invested_capital = next_invested_capital
            break
        invested_capital = next_invested_capital

    target_amounts = weights * invested_capital
    sold_amount = float(np.maximum(current_amounts - target_amounts, 0.0).sum())
    penalty_czk = sold_amount * sale_penalty_rate
    invested_capital = max(0.0, float(total_capital) - penalty_czk)
    target_amounts = weights * invested_capital
    sold_amount = float(np.maximum(current_amounts - target_amounts, 0.0).sum())
    penalty_czk = sold_amount * sale_penalty_rate
    return target_amounts, invested_capital, sold_amount, penalty_czk


def _objective_from_target_amounts(
    target_amounts: np.ndarray,
    expected_returns: np.ndarray,
    cov: np.ndarray,
    current_amounts: np.ndarray,
    sale_penalty_rate: float,
    dropped_czk: float = 0.0,
) -> tuple[float, float, float, float, float]:
    np = _load_numpy()
    target_amounts = np.asarray(target_amounts, dtype=float)
    current_amounts = np.asarray(current_amounts, dtype=float)
    expected_returns = np.asarray(expected_returns, dtype=float)
    sold_amount = dropped_czk + float(np.maximum(current_amounts - target_amounts, 0.0).sum())
    penalty_czk = sold_amount * sale_penalty_rate
    expected_profit_czk = float(target_amounts @ expected_returns) - penalty_czk
    risk_czk = float(np.sqrt(max(float(target_amounts @ cov @ target_amounts), 0.0)))
    if risk_czk <= 1e-12:
        return -1e9, expected_profit_czk, risk_czk, sold_amount, penalty_czk
    objective = expected_profit_czk / risk_czk
    return objective, expected_profit_czk, risk_czk, sold_amount, penalty_czk


def _portfolio_objective(
    weights: np.ndarray,
    expected_returns: np.ndarray,
    cov: np.ndarray,
    current_amounts: np.ndarray,
    total_capital: float,
    sale_penalty_rate: float,
    dropped_czk: float = 0.0,
) -> tuple[float, float, float, float]:
    target_amounts = _project_to_simplex(weights) * total_capital
    objective, expected_profit_czk, risk_czk, sold_amount, _ = _objective_from_target_amounts(
        target_amounts,
        expected_returns,
        cov,
        current_amounts,
        sale_penalty_rate,
        dropped_czk,
    )
    effective_return = expected_profit_czk / max(total_capital, 1e-12)
    effective_volatility = risk_czk / max(total_capital, 1e-12)
    return objective, effective_return, effective_volatility, sold_amount


def _optimize_weights_with_sale_penalty(
    expected_returns: np.ndarray,
    corr_matrix: np.ndarray,
    stds: np.ndarray,
    current_amounts: np.ndarray,
    total_capital: float,
    sale_penalty_rate: float,
    synthetic_flags: np.ndarray | None = None,
    stop_event: threading.Event | None = None,
    max_seconds: float = 15.0,
    dropped_czk: float = 0.0,
) -> tuple[np.ndarray, float, float, float]:
    np = _load_numpy()
    import scipy.optimize as sco
    n = len(expected_returns)
    if n == 0:
        return np.array([]), 0.0, 0.0, 0.0

    cov = _safe_covariance_matrix(stds, corr_matrix.copy())
    current_weights = np.asarray(current_amounts, dtype=float) / max(total_capital, 1e-12)

    def obj_func(w):
        obj, _, _, _ = _portfolio_objective(
            w, expected_returns, cov, current_amounts, total_capital, sale_penalty_rate, dropped_czk
        )
        return -obj

    seeds = []
    seeds.append(_project_to_simplex(np.maximum(expected_returns, 0.0)))
    seeds.append(np.ones(n) / n)
    if current_weights.sum() > 0:
        boosted_current = current_weights + np.maximum(expected_returns, 0.0) * max(0.0, 1.0 - current_weights.sum())
        seeds.append(_project_to_simplex(boosted_current))
    else:
        seeds.append(_project_to_simplex(np.maximum(expected_returns, 0.0) + 1.0))

    try:
        inv_cov = np.linalg.pinv(cov)
        seeds.append(_project_to_simplex(inv_cov @ expected_returns))
    except np.linalg.LinAlgError:
        pass

    best_weights = seeds[0]
    best_objective, best_ret, best_vol = -1e9, 0.0, 0.0

    deadline = time.monotonic() + max_seconds
    constraints = {"type": "eq", "fun": lambda w: np.sum(w) - 1.0}
    
    bounds_list = []
    for i in range(n):
        if synthetic_flags is not None and synthetic_flags[i]:
            bounds_list.append([0.0, max(1e-6, float(current_weights[i]))])
        else:
            bounds_list.append([0.0, 1.0])
            
    max_sum = sum(b[1] for b in bounds_list)
    if max_sum < 1.0:
        scale = 1.0 / max_sum
        for b in bounds_list:
            b[1] = min(1.0, b[1] * scale)
            
    bounds = tuple(tuple(b) for b in bounds_list)

    for seed in seeds:
        if stop_event is not None and stop_event.is_set():
            break
        if time.monotonic() >= deadline:
            break

        res = sco.minimize(
            obj_func,
            seed,
            method="SLSQP",
            bounds=bounds,
            constraints=constraints,
            options={"maxiter": 200, "ftol": 1e-6, "disp": False}
        )
        
        w_res = _project_to_simplex(res.x)
        obj, ret, vol, _ = _portfolio_objective(
            w_res, expected_returns, cov, current_amounts, total_capital, sale_penalty_rate, dropped_czk
        )
        if obj > best_objective:
            best_objective = obj
            best_ret = ret
            best_vol = vol
            best_weights = w_res.copy()

    return best_weights, best_objective, best_ret, best_vol


def _optimize_extra_cash_without_sells(
    expected_returns: np.ndarray,
    corr_matrix: np.ndarray,
    stds: np.ndarray,
    current_amounts: np.ndarray,
    total_capital: float,
    stop_event: threading.Event | None = None,
    max_seconds: float = 12.0,
) -> tuple[np.ndarray, float, float, float]:
    np = _load_numpy()
    n = len(expected_returns)
    if n == 0:
        return np.array([]), 0.0, 0.0, 0.0

    current_amounts = np.asarray(current_amounts, dtype=float)
    base_weights = current_amounts / max(total_capital, 1e-12)
    extra_cash = max(0.0, total_capital - float(current_amounts.sum()))
    if extra_cash <= 1e-12:
        weights = _project_to_simplex(base_weights)
        cov = _safe_covariance_matrix(stds, corr_matrix.copy())
        obj, gross_ret, vol, _ = _portfolio_objective(weights, expected_returns, cov, current_amounts, total_capital, 0.0)
        return weights, obj, gross_ret, vol

    alpha = extra_cash / max(total_capital, 1e-12)
    cov = _safe_covariance_matrix(stds, corr_matrix.copy())

    def weights_from_extra(extra_weights: np.ndarray) -> np.ndarray:
        return base_weights + alpha * extra_weights

    seeds = [
        np.ones(n) / n,
        _project_to_simplex(np.maximum(expected_returns, 0.0)),
    ]
    try:
        seeds.append(_project_to_simplex(np.linalg.pinv(cov) @ expected_returns))
    except np.linalg.LinAlgError:
        pass

    rng = np.random.default_rng(42)
    for _ in range(4):
        seeds.append(_project_to_simplex(rng.random(n)))

    deadline = time.monotonic() + max_seconds
    best_extra = seeds[0]
    best_weights = weights_from_extra(best_extra)
    best_obj, best_ret, best_vol, _ = _portfolio_objective(best_weights, expected_returns, cov, current_amounts, total_capital, 0.0)

    for seed in seeds:
        if stop_event is not None and stop_event.is_set():
            break
        if time.monotonic() >= deadline:
            break

        extra_alloc = _project_to_simplex(seed)
        local_step = 0.12

        for _ in range(350):
            if stop_event is not None and stop_event.is_set():
                break
            if time.monotonic() >= deadline:
                break

            weights = weights_from_extra(extra_alloc)
            obj, gross_ret, vol, _ = _portfolio_objective(weights, expected_returns, cov, current_amounts, total_capital, 0.0)
            if obj > best_obj + 1e-10:
                best_obj = obj
                best_ret = gross_ret
                best_vol = vol
                best_extra = extra_alloc.copy()
                best_weights = weights.copy()

            cov_w = cov @ weights
            grad_w = expected_returns / max(vol, 1e-12) - (gross_ret / max(vol**3, 1e-12)) * cov_w
            grad_extra = alpha * grad_w
            extra_alloc = _project_to_simplex(extra_alloc + local_step * grad_extra)
            local_step *= 0.997

    return best_weights, best_obj, best_ret, best_vol


def _objective_gradient(
    weights: np.ndarray,
    expected_returns: np.ndarray,
    cov: np.ndarray,
    current_amounts: np.ndarray,
    total_capital: float,
    sale_penalty_rate: float,
) -> np.ndarray:
    np = _load_numpy()
    weights = _project_to_simplex(weights)
    target_amounts = weights * total_capital
    sold_mask = (current_amounts - target_amounts) > 1e-9
    penalty_gradient_czk = np.where(sold_mask, sale_penalty_rate * total_capital, 0.0)
    net_returns_czk = total_capital * expected_returns - penalty_gradient_czk
    risk_czk = float(np.sqrt(max(float(target_amounts @ cov @ target_amounts), 1e-18)))
    if risk_czk <= 1e-12:
        return np.zeros_like(weights)
    net_profit_czk = float(target_amounts @ expected_returns) - float(
        np.maximum(current_amounts - target_amounts, 0.0).sum() * sale_penalty_rate
    )
    risk_grad = (total_capital * (cov @ weights)) / risk_czk
    return net_returns_czk / risk_czk - (net_profit_czk / max(risk_czk**2, 1e-18)) * risk_grad


class ReturnCache:
    def __init__(self):
        self.cache: dict[str, object] = {}

    def get_returns(self, ticker: str, log_fn):
        pd = _load_pandas()
        if ticker in self.cache:
            return self.cache[ticker]

        yf = _load_yfinance()
        if yf is None:
            log_fn(f"yfinance není dostupné, korelace pro {ticker} nastavena na 0.")
            self.cache[ticker] = pd.Series(dtype=float)
            return self.cache[ticker]

        try:
            data = yf.download(ticker, period="6mo", interval="1wk", progress=False, auto_adjust=True)
            close = data["Close"] if "Close" in data else pd.Series(dtype=float)
            series = close.squeeze() if isinstance(close, pd.DataFrame) else close
            returns = pd.Series(series).pct_change().dropna()
        except Exception as exc:  # pragma: no cover - depends on runtime/network
            log_fn(f"Nepodařilo se stáhnout korelace pro {ticker}: {exc}. Použiji nulovou korelaci.")
            returns = pd.Series(dtype=float)

        self.cache[ticker] = returns
        return returns


def build_correlation_matrix(tickers: list[str], cache: ReturnCache, log_fn) -> np.ndarray:
    np = _load_numpy()
    pd = _load_pandas()
    if not tickers:
        return np.zeros((0, 0))

    series_map: dict[str, object] = {}
    for ticker in tickers:
        series_map[ticker] = cache.get_returns(ticker, log_fn)

    aligned = pd.concat(series_map, axis=1).dropna(how="all") if series_map else pd.DataFrame()
    if aligned.empty:
        log_fn("Není dost dat pro odhad korelací, použiji nulovou korelační matici.")
        return np.zeros((len(tickers), len(tickers)))

    aligned.columns = tickers
    corr = aligned.corr().reindex(index=tickers, columns=tickers).fillna(0.0)
    return corr.values


def find_all_meta_workbooks_since(base_dir: Path, start_date: dt.date) -> list[tuple[dt.date, Path]]:
    candidates = list(base_dir.glob(f"*{META_FILE_SUFFIX}"))
    candidates.extend(base_dir.joinpath("other").glob(f"*{META_FILE_SUFFIX}"))
    unique_candidates = {path.resolve(): path for path in candidates}.values()
    dated: list[tuple[dt.date, Path]] = []

    for path in unique_candidates:
        match = META_DATE_RE.search(path.name)
        if not match:
            continue
        file_date = dt.datetime.strptime(match.group("date"), "%d.%m.%Y").date()
        if file_date >= start_date:
            dated.append((file_date, path))

    dated.sort(key=lambda item: item[0])
    return dated


def _xlsx_column_index(column_letters: str) -> int:
    value = 0
    for char in column_letters.upper():
        value = value * 26 + (ord(char) - ord("A") + 1)
    return value


def _parse_cell_reference(reference: str) -> tuple[int, int]:
    match = re.match(r"([A-Z]+)(\d+)$", reference.upper())
    if not match:
        raise ValueError(f"Neplatná reference buňky: {reference}")
    return int(match.group(2)), _xlsx_column_index(match.group(1))


def _load_shared_strings(archive: zipfile.ZipFile) -> list[str]:
    shared_path = "xl/sharedStrings.xml"
    if shared_path not in archive.namelist():
        return []

    namespace = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
    strings: list[str] = []
    with archive.open(shared_path) as handle:
        for _, elem in ET.iterparse(handle, events=("end",)):
            if elem.tag == f"{namespace}si":
                parts = []
                for node in elem.iter():
                    if node.tag == f"{namespace}t" and node.text is not None:
                        parts.append(node.text)
                strings.append("".join(parts))
                elem.clear()
    return strings


def _resolve_sheet_path(archive: zipfile.ZipFile, sheet_name: str) -> str | None:
    workbook_ns = {
        "main": "http://schemas.openxmlformats.org/spreadsheetml/2006/main",
        "rel": "http://schemas.openxmlformats.org/officeDocument/2006/relationships",
        "pkg": "http://schemas.openxmlformats.org/package/2006/relationships",
    }
    workbook_root = ET.fromstring(archive.read("xl/workbook.xml"))
    rel_root = ET.fromstring(archive.read("xl/_rels/workbook.xml.rels"))

    rel_id = None
    for sheet in workbook_root.findall("main:sheets/main:sheet", workbook_ns):
        if sheet.attrib.get("name") == sheet_name:
            rel_id = sheet.attrib.get("{http://schemas.openxmlformats.org/officeDocument/2006/relationships}id")
            break

    if rel_id is None:
        return None

    target = None
    for rel in rel_root.findall("pkg:Relationship", workbook_ns):
        if rel.attrib.get("Id") == rel_id:
            target = rel.attrib.get("Target")
            break

    if not target:
        return None

    target = target.lstrip("/")
    if target.startswith("xl/"):
        return target
    return f"xl/{target}"


def _copy_to_temp_for_read(path: Path) -> Path:
    suffix = path.suffix or ".tmp"
    temp_file = tempfile.NamedTemporaryFile(prefix="portfolio_manager_", suffix=suffix, delete=False)
    temp_path = Path(temp_file.name)
    temp_file.close()
    try:
        shutil.copyfile(path, temp_path)
    except Exception:
        try:
            temp_path.unlink(missing_ok=True)
        except Exception:
            pass
        raise
    return temp_path


def _fast_load_raw_data_from_meta(path: Path) -> dict[str, dict[str, float]]:
    namespace = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
    col_indices = {key: _xlsx_column_index(val) for key, val in META_COLS_MULTI.items()}
    wanted_cols = set(col_indices.values())
    ticker_col = col_indices["ticker"]

    with zipfile.ZipFile(path) as archive:
        sheet_path = _resolve_sheet_path(archive, META_SHEET_NAME)
        if sheet_path is None:
            raise RuntimeError(f"List '{META_SHEET_NAME}' v souboru {path.name} neexistuje.")

        shared_strings = _load_shared_strings(archive)
        results: dict[str, dict[str, float]] = {}

        with archive.open(sheet_path) as handle:
            current_row = None
            row_values: dict[int, object] = {}
            cell_type = None
            cell_ref = None
            inline_parts: list[str] = []
            value_text = None

            def finalize_row():
                nonlocal row_values, current_row
                if current_row is None or current_row < META_START_ROW:
                    row_values = {}
                    return

                ticker_val = row_values.get(ticker_col)
                if not ticker_val:
                    row_values = {}
                    return
                ticker_text = str(ticker_val).strip().upper()
                if not ticker_text:
                    row_values = {}
                    return

                metrics = {}
                for key, c_idx in col_indices.items():
                    if key == "ticker": continue
                    val = row_values.get(c_idx)
                    try:
                        metrics[key] = float(val) if val is not None else 0.0
                    except Exception:
                        metrics[key] = 0.0

                results[ticker_text] = metrics
                row_values = {}

            for event, elem in ET.iterparse(handle, events=("start", "end")):
                if event == "start":
                    if elem.tag == f"{namespace}row":
                        current_row = int(elem.attrib.get("r", "0"))
                        row_values = {}
                    elif elem.tag == f"{namespace}c":
                        cell_type = elem.attrib.get("t")
                        cell_ref = elem.attrib.get("r")
                        inline_parts = []
                        value_text = None
                    continue

                if elem.tag == f"{namespace}v":
                    value_text = elem.text
                elif elem.tag == f"{namespace}t":
                    if cell_type == "inlineStr" and elem.text is not None:
                        inline_parts.append(elem.text)
                elif elem.tag == f"{namespace}c":
                    if cell_ref:
                        row_idx, col_idx = _parse_cell_reference(cell_ref)
                        if row_idx >= META_START_ROW and col_idx in wanted_cols:
                            cell_value: object = None
                            if cell_type == "s" and value_text is not None:
                                try:
                                    cell_value = shared_strings[int(value_text)]
                                except Exception:
                                    cell_value = value_text
                            elif cell_type == "inlineStr":
                                cell_value = "".join(inline_parts)
                            else:
                                cell_value = value_text
                            row_values[col_idx] = cell_value
                    elem.clear()
                elif elem.tag == f"{namespace}row":
                    finalize_row()
                    elem.clear()

        return results


def _load_prediction_csv_paired_with_sim(csv_path: Path, base_dir: Path, file_date: dt.date, log_fn) -> dict[str, dict[str, float]]:
    pd = _load_pandas()
    try:
        df_pred = pd.read_csv(csv_path)
    except Exception as e:
        log_fn(f"Chyba při čtení CSV {csv_path.name}: {e}")
        return {}
        
    tickers = None
    # Podpora pro nové CSV ze sítě (nn108n_v3) s nativním sloupcem Ticker
    if 'ticker' in df_pred.columns:
        tickers = df_pred['ticker'].astype(str).tolist()
    elif 'Ticker' in df_pred.columns:
        tickers = df_pred['Ticker'].astype(str).tolist()
        
    # Původní fallback logika pro starší predikce bez Tickeru
    if tickers is None:
        num_rows = len(df_pred)
        sim_dir = base_dir / "processed"
        date_str = file_date.strftime("%d.%m.%Y")
        expected_sim_path = sim_dir / f"{date_str} sim.xlsx"
        
        sim_path_to_use = None
        if expected_sim_path.exists():
            try:
                df_test = pd.read_excel(expected_sim_path)
                if len(df_test) == num_rows:
                    sim_path_to_use = expected_sim_path
            except Exception:
                pass
                
        if sim_path_to_use is None:
            candidates = []
            for p in sim_dir.glob("* sim.xlsx"):
                try:
                    df_test = pd.read_excel(p)
                    if len(df_test) == num_rows:
                        candidates.append((p.stat().st_mtime, p, df_test))
                except Exception:
                    continue
            if candidates:
                candidates.sort(key=lambda x: x[0], reverse=True)
                sim_path_to_use = candidates[0][1]
                df_sim = candidates[0][2]
            else:
                log_fn(f"Varování: Nenašel se vhodný sim.xlsx pro {csv_path.name} (očekáváno {num_rows} řádků).")
                return {}
        else:
            df_sim = pd.read_excel(sim_path_to_use)
            
        if 'Ticker' not in df_sim.columns:
            log_fn(f"Varování: {sim_path_to_use.name} neobsahuje sloupec 'Ticker'.")
            return {}
            
        tickers = df_sim['Ticker'].astype(str).tolist()
        log_fn(f"Použito párování {csv_path.name} <-> {sim_path_to_use.name}")
    else:
        log_fn(f"Použit nativní Ticker sloupec z {csv_path.name}")
        
    results: dict[str, dict[str, float]] = {}
    
    for idx, row in df_pred.iterrows():
        ticker = tickers[idx].strip().upper()
        if not ticker:
            continue
            
        metrics = {}
        for horizon in ['1w', '4w', '13w', '26w', '52w']:
            # Podpora pro nový formát procent (nn108n_v3)
            stred_col = f'stred_{horizon}_%'
            q10_col = f'q10_{horizon}_%'
            q90_col = f'q90_{horizon}_%'
            
            # Starý formát reziduí
            mean_col = f'mean_{horizon}'
            q10_old = f'q10_{horizon}'
            q90_old = f'q90_{horizon}'
            
            if stred_col in df_pred.columns:
                val = row[stred_col]
                mean_val = float(val) / 100.0 if pd.notna(val) else 0.0
                metrics[f'{horizon}_pred'] = mean_val
                
                # Downside riziko: absolutní hodnota CVaR 10 (reálný tail-risk)
                cvar10_col = f'cvar10_{horizon}_%'
                if cvar10_col in df_pred.columns:
                    cvar10_val = float(row[cvar10_col]) / 100.0 if pd.notna(row[cvar10_col]) else 0.0
                    metrics[f'{horizon}_std'] = abs(cvar10_val)
                elif q10_col in df_pred.columns:
                    # Fallback na q10 pokud cvar10 chybí
                    q10_val = float(row[q10_col]) / 100.0 if pd.notna(row[q10_col]) else 0.0
                    metrics[f'{horizon}_std'] = max(0.0, mean_val - q10_val)
                else:
                    metrics[f'{horizon}_std'] = 0.0
                    
                # Upside potenciál: q90 - stred
                if q90_col in df_pred.columns:
                    q90_val = float(row[q90_col]) / 100.0 if pd.notna(row[q90_col]) else 0.0
                    metrics[f'{horizon}_up'] = max(0.0, q90_val - mean_val)
                else:
                    metrics[f'{horizon}_up'] = 0.0
                    
            elif mean_col in df_pred.columns:
                val = row[mean_col]
                mean_val = float(val) if pd.notna(val) else 0.0
                metrics[f'{horizon}_pred'] = mean_val
                
                if q10_old in df_pred.columns:
                    metrics[f'{horizon}_std'] = abs(float(row[q10_old])) if pd.notna(row[q10_old]) else 0.0
                else:
                    metrics[f'{horizon}_std'] = 0.0
                    
                if q90_old in df_pred.columns:
                    metrics[f'{horizon}_up'] = max(0.0, float(row[q90_old])) if pd.notna(row[q90_old]) else 0.0
                else:
                    metrics[f'{horizon}_up'] = 0.0
                
        if metrics:
            results[ticker] = metrics
            
    log_fn(f"Úspěšně zpracováno {len(results)} tickerů z {csv_path.name}")
    return results

def find_all_prediction_csvs(base_dir: Path, start_date: dt.date) -> list[tuple[dt.date, Path]]:
    candidates = list(base_dir.glob("predictions_*.csv"))
    dated: list[tuple[dt.date, Path]] = []
    
    import re
    date_re = re.compile(r"predictions_(\d{4})(\d{2})(\d{2})_")
    
    for path in candidates:
        match = date_re.search(path.name)
        if match:
            y, m, d = int(match.group(1)), int(match.group(2)), int(match.group(3))
            try:
                file_date = dt.date(y, m, d)
                if file_date >= start_date:
                    dated.append((file_date, path))
            except ValueError:
                pass
                
    dated.sort(key=lambda item: item[0])
    return dated


def load_historical_meta_and_calculate_ema(base_dir: Path, alphas: dict[str, float], log_fn) -> list[StockRecord]:
    np = _load_numpy()
    yf = _load_yfinance()
    pd = _load_pandas()
    
    file_list = find_all_meta_workbooks_since(base_dir, META_START_DATE)
    
    # 24. 4. 2026 byl nasazen nový systém CSV predikcí metasítě
    pred_list = find_all_prediction_csvs(base_dir, dt.date(2026, 4, 24))
    
    if not file_list and not pred_list:
        raise FileNotFoundError(f"Nenalezen žádný meta soubor ani csv predikce od {META_START_DATE.strftime('%d.%m.%Y')}.")
        
    import pickle
    cache_path = base_dir / "ema_cache.pkl"
    
    emas: dict[str, dict[str, float]] = {}
    prev_actuals: dict[str, dict[str, float]] = {}
    is_synth_latest: dict[str, bool] = {}
    last_seen_date: dict[str, dt.date] = {}
    prev_date = None

    loaded_from_cache = False
    if cache_path.exists():
        try:
            with open(cache_path, "rb") as f:
                c_data = pickle.load(f)
            if c_data.get("alphas") == alphas:
                emas = c_data["emas"]
                prev_actuals = c_data["prev_actuals"]
                last_seen_date = c_data["last_seen_date"]
                prev_date = c_data["prev_date"]
                is_synth_latest = c_data.get("is_synth_latest", {})
                loaded_from_cache = True
                log_fn("Úspěšně načtena vyrovnávací paměť EMA (shodné alfa hodnoty).")
        except Exception as e:
            log_fn(f"Nelze načíst cache: {e}. Počítám od nuly.")

    if loaded_from_cache and prev_date is not None:
        file_list = [(d, p) for (d, p) in file_list if d > prev_date]
        pred_list = [(d, p) for (d, p) in pred_list if d > prev_date]
        if not file_list and not pred_list:
            log_fn("Nevidím žádné novější Excel soubory ani nové CSV predikce. Používám vyčištěnou RAM cache.")
        else:
            log_fn(f"Smyčka hrdě naváže pro {len(file_list)} nových Excelů a {len(pred_list)} CSV predikcí do historie.")
    else:
        log_fn(f"Zjištěno {len(file_list)} Excelů a {len(pred_list)} CSV souborů pro hrubou sekvenční analýzu (vše odznova).")
        
    # Zpracování historických meta Excelů
    for file_date, path in file_list:
        log_fn(f"Zpracovávám (Excel): {path.name} ({file_date.strftime('%d.%m.%Y')})")
        try:
            raw_data = _fast_load_raw_data_from_meta(path)
        except Exception as e:
            log_fn(f"Varování: Přeskakuji {path.name} kvůli chybě: {e}")
            continue
        
        missing_tickers = [
            t for t in emas.keys() 
            if t not in raw_data and t in last_seen_date
        ]
        
        returns_cache = {}
        if missing_tickers and prev_date is not None and yf:
            import re
            yf_tickers = [t for t in missing_tickers if re.match(r"^[A-Z][A-Z\-\.]*$", t)]
            if yf_tickers:
                start_d = prev_date - dt.timedelta(days=2)
                end_d = file_date + dt.timedelta(days=1)
                try:
                    df = yf.download(yf_tickers, start=start_d, end=end_d, auto_adjust=False, progress=False)
                    if not df.empty and 'Close' in df:
                        closes = df['Close']
                        if isinstance(closes, pd.DataFrame):
                            for t in yf_tickers:
                                if t in closes.columns:
                                    series = closes[t].dropna()
                                    if len(series) >= 2:
                                        returns_cache[t] = float(series.iloc[-1] / series.iloc[0] - 1.0)
                        elif isinstance(closes, pd.Series):
                            t = yf_tickers[0]
                            series = closes.dropna()
                            if len(series) >= 2:
                                returns_cache[t] = float(series.iloc[-1] / series.iloc[0] - 1.0)
                except Exception as e:
                    pass
                
        all_tickers_today = set(raw_data.keys()).union(emas.keys())
        for ticker in all_tickers_today:
            if ticker in raw_data:
                metrics = raw_data[ticker]
                
                # Přizpůsobení staré směrodatné odchylky na úroveň 10% kvantilu (1.28 násobek)
                # Kvantilová metasíť nasazena koncem dubna 2026
                if file_date < dt.date(2026, 4, 25):
                    for mk in list(metrics.keys()):
                        if 'std' in mk:
                            metrics[mk] *= 1.28
                            
                is_synth = False
                last_seen_date[ticker] = file_date
            else:
                base_metrics = prev_actuals.get(ticker, emas.get(ticker, {}))
                ret = returns_cache.get(ticker, 0.0)
                metrics = {}
                for key in base_metrics:
                    if 'pred' in key:
                        metrics[key] = base_metrics[key] - ret
                    elif 'std' in key or 'up' in key:
                        metrics[key] = base_metrics[key] * 1.10
                is_synth = True
                
            is_synth_latest[ticker] = is_synth
            prev_actuals[ticker] = metrics.copy()
            
            if ticker not in emas:
                emas[ticker] = metrics.copy()
            else:
                for metric_key, val in metrics.items():
                    a = 1.0
                    for win in ["1w", "4w", "13w", "26w", "52w"]:
                        if metric_key.startswith(win):
                            a = alphas.get(win, 1.0)
                            break
                    emas[ticker][metric_key] = a * val + (1.0 - a) * emas[ticker].get(metric_key, val)
        
        prev_date = file_date
        
    # Zpracování nových CSV predikcí ze sítě
    for file_date, path in pred_list:
        log_fn(f"Zpracovávám (CSV): {path.name} ({file_date.strftime('%d.%m.%Y')})")
        try:
            raw_data = _load_prediction_csv_paired_with_sim(path, base_dir, file_date, log_fn)
            if not raw_data:
                continue
        except Exception as e:
            log_fn(f"Varování: Přeskakuji {path.name} kvůli chybě: {e}")
            continue
            
        missing_tickers = [
            t for t in emas.keys() 
            if t not in raw_data and t in last_seen_date
        ]
        
        returns_cache = {}
        if missing_tickers and prev_date is not None and yf:
            import re
            yf_tickers = [t for t in missing_tickers if re.match(r"^[A-Z][A-Z\-\.]*$", t)]
            if yf_tickers:
                start_d = prev_date - dt.timedelta(days=2)
                end_d = file_date + dt.timedelta(days=1)
                try:
                    df = yf.download(yf_tickers, start=start_d, end=end_d, auto_adjust=False, progress=False)
                    if not df.empty and 'Close' in df:
                        closes = df['Close']
                        if isinstance(closes, pd.DataFrame):
                            for t in yf_tickers:
                                if t in closes.columns:
                                    series = closes[t].dropna()
                                    if len(series) >= 2:
                                        returns_cache[t] = float(series.iloc[-1] / series.iloc[0] - 1.0)
                        elif isinstance(closes, pd.Series):
                            t = yf_tickers[0]
                            series = closes.dropna()
                            if len(series) >= 2:
                                returns_cache[t] = float(series.iloc[-1] / series.iloc[0] - 1.0)
                except Exception as e:
                    pass
                
        all_tickers_today = set(raw_data.keys()).union(emas.keys())
        for ticker in all_tickers_today:
            if ticker in raw_data:
                metrics = raw_data[ticker]
                # Nové predikce z CSV jsou již ve formátu 10. percentilu, násobit 1.28x není potřeba
                is_synth = False
                last_seen_date[ticker] = file_date
            else:
                base_metrics = prev_actuals.get(ticker, emas.get(ticker, {}))
                ret = returns_cache.get(ticker, 0.0)
                metrics = {}
                for key in base_metrics:
                    if 'pred' in key:
                        metrics[key] = base_metrics[key] - ret
                    elif 'std' in key or 'up' in key:
                        metrics[key] = base_metrics[key] * 1.10
                is_synth = True
                
            is_synth_latest[ticker] = is_synth
            prev_actuals[ticker] = metrics.copy()
            
            if ticker not in emas:
                emas[ticker] = metrics.copy()
            else:
                for metric_key, val in metrics.items():
                    a = 1.0
                    for win in ["1w", "4w", "13w", "26w", "52w"]:
                        if metric_key.startswith(win):
                             a = alphas.get(win, 1.0)
                             break
                    emas[ticker][metric_key] = a * val + (1.0 - a) * emas[ticker].get(metric_key, val)
        
        prev_date = file_date
        
    records = []
    for ticker, metrics in emas.items():
        try:
            agg_pred = 1.0
            agg_std = 1.0
            agg_up = 1.0
            horizon_data = {}
            for win in ["1w", "4w", "13w", "26w", "52w"]:
                p = metrics.get(f"{win}_pred", 0.0)
                s = metrics.get(f"{win}_std", 0.0)  # CVaR10 (abs)
                u = metrics.get(f"{win}_up", s)  # Fallback na symetrii
                horizon_data[win] = (p, s, u)
                agg_pred *= (1.0 + p)
                agg_std *= (1.0 + s)
                agg_up *= (1.0 + u)
                
            agg_pred = math.pow(max(0.0, agg_pred), 0.2) - 1.0
            agg_std = math.pow(max(0.0, agg_std), 0.2) - 1.0
            agg_up = math.pow(max(0.0, agg_up), 0.2) - 1.0
            
            agg_std = max(agg_std, 1e-6)
            
            # Return/CVaR ratio: čistý poměr výnosu vůči tail-risku
            if agg_pred <= 0:
                sharpe = -999.0  # Tvrdé vyřazení záporných výnosů z nákupního poolu
            else:
                sharpe = agg_pred / max(abs(agg_std), 1e-6)
            
            if np.isfinite(sharpe) and np.isfinite(agg_pred) and np.isfinite(agg_std):
                records.append(StockRecord(
                    ticker=ticker,
                    sharpe=sharpe,
                    forecast_pct=agg_pred,
                    std_pct=agg_std,
                    upside_pct=agg_up,
                    is_synthetic=is_synth_latest.get(ticker, False),
                    horizon_data=horizon_data,
                ))
        except Exception:
            pass
            
    if file_list:
        try:
            c_data = {
                "alphas": alphas,
                "emas": emas,
                "prev_actuals": prev_actuals,
                "last_seen_date": last_seen_date,
                "prev_date": prev_date,
                "is_synth_latest": is_synth_latest
            }
            with open(cache_path, "wb") as f:
                pickle.dump(c_data, f)
            log_fn("Kulatý stav EMA analýzy bezpečně uložen do cache na disk.")
        except Exception as e:
            log_fn(f"Nepodařilo se uložit cache: {e}")

    if not records:
        raise RuntimeError("Vygenerováno 0 validních záznamů po spojení EMA.")
    return records


def parse_holdings_text(text: str) -> dict[str, float]:
    holdings: dict[str, float] = {}
    lines = [line.strip() for line in text.splitlines() if line.strip()]

    for line in lines:
        parts = [part for part in re.split(r"[;\t, ]+", line) if part]
        if len(parts) < 2:
            raise ValueError(f"Řádek '{line}' nemá formát TICKER ČÁSTKA.")

        ticker = parts[0].strip().upper()
        amount_text = "".join(parts[1:]).replace("Kc", "").replace("CZK", "").replace("czk", "")
        amount = _safe_float(amount_text)
        if amount < 0:
            raise ValueError(f"Řádek '{line}' obsahuje zápornou částku.")
        holdings[ticker] = holdings.get(ticker, 0.0) + amount

    return holdings


class PortfolioManager:
    def __init__(
        self,
        records: list[StockRecord],
        current_holdings_czk: dict[str, float],
        extra_cash_czk: float,
        target_positions: int,
        sale_penalty_rate: float,
        max_turnover_czk: float | None,
        max_position_replacements: int | None,
        min_trade_czk: float,
        log_fn=print,
        stop_event: threading.Event | None = None,
    ):
        self.record_map = {record.ticker: record for record in records}
        self.records = sorted(records, key=lambda rec: rec.sharpe, reverse=True)
        self.current_holdings_czk = {ticker.upper(): float(amount) for ticker, amount in current_holdings_czk.items() if amount > 0}
        self.extra_cash_czk = float(extra_cash_czk)
        self.target_positions = max(1, int(target_positions))
        self.sale_penalty_rate = max(0.0, float(sale_penalty_rate))
        self.max_turnover_czk = None if max_turnover_czk is None else max(0.0, float(max_turnover_czk))
        self.max_position_replacements = None if max_position_replacements is None else max(0, int(max_position_replacements))
        self.min_trade_czk = max(0.0, float(min_trade_czk))
        self.log = log_fn
        self.stop_event = stop_event
        self.cache = ReturnCache()

    def _should_stop(self) -> bool:
        return self.stop_event is not None and self.stop_event.is_set()

    def _eligible_current_holdings(self) -> dict[str, float]:
        eligible: dict[str, float] = {}
        for ticker, amount in self.current_holdings_czk.items():
            if ticker in self.record_map:
                eligible[ticker] = amount
            else:
                self.log(f"Ticker {ticker} není v posledním meta souboru, proto ho nebudu optimalizovat.")
        return eligible

    def _build_candidate_pool(self, current_holdings: dict[str, float]) -> list[StockRecord]:
        positive = [record for record in self.records if record.sharpe > 0 and record.forecast_pct > 0]
        if not positive:
            positive = [record for record in self.records if record.sharpe > 0]
        if not positive:
            positive = self.records[:]

        current_tickers = set(current_holdings)
        pool: list[StockRecord] = []
        added: set[str] = set()

        for ticker in current_tickers:
            record = self.record_map.get(ticker)
            if record is not None and ticker not in added:
                pool.append(record)
                added.add(ticker)

        for record in positive[: max(self.target_positions * 6, 180)]:
            if record.ticker not in added:
                pool.append(record)
                added.add(record.ticker)

        if len(pool) < self.target_positions:
            for record in self.records:
                if record.ticker not in added:
                    pool.append(record)
                    added.add(record.ticker)
                if len(pool) >= self.target_positions:
                    break

        return pool

    def _no_sell_mode(self) -> bool:
        return False

    def _evaluate_subset(
        self,
        subset: list[StockRecord],
        current_holdings: dict[str, float],
        total_capital: float,
    ) -> tuple[float, np.ndarray, float, float, float]:
        np = _load_numpy()
        tickers = [record.ticker for record in subset]
        corr = build_correlation_matrix(tickers, self.cache, self.log)
        expected_returns = np.array([record.forecast_pct for record in subset], dtype=float)
        stds = np.array([record.std_pct for record in subset], dtype=float)
        current_amounts = np.array([current_holdings.get(ticker, 0.0) for ticker in tickers], dtype=float)

        dropped_czk = sum(amt for t, amt in current_holdings.items() if t not in tickers)
        synth_flags = np.array([record.is_synthetic for record in subset], dtype=bool)

        weights, objective, gross_return, volatility = _optimize_weights_with_sale_penalty(
            expected_returns,
            corr,
            stds,
            current_amounts,
            total_capital,
            self.sale_penalty_rate,
            dropped_czk=dropped_czk,
            synthetic_flags=synth_flags,
            stop_event=self.stop_event,
        )

        sold_czk = dropped_czk + float(np.maximum(current_amounts - weights * total_capital, 0.0).sum())
        return objective, weights, gross_return, volatility, sold_czk

    def _is_feasible_subset(self, subset_tickers: set[str], current_tickers: set[str]) -> bool:
        if self.max_position_replacements is None:
            return True
        sold_out = len(current_tickers - subset_tickers)
        return sold_out <= self.max_position_replacements

    def _initial_subset(self, pool: list[StockRecord], current_holdings: dict[str, float]) -> list[StockRecord]:
        current_sorted = sorted(
            (self.record_map[ticker] for ticker in current_holdings if ticker in self.record_map),
            key=lambda rec: (current_holdings.get(rec.ticker, 0.0), rec.sharpe),
            reverse=True,
        )
        subset: list[StockRecord] = []
        added: set[str] = set()
        effective_target = self.target_positions

        for record in current_sorted:
            if len(subset) >= effective_target:
                break
            subset.append(record)
            added.add(record.ticker)

        for record in pool:
            if len(subset) >= effective_target:
                break
            if record.ticker in added:
                continue
            subset.append(record)
            added.add(record.ticker)

        return subset[: effective_target]


    def optimize(self) -> OptimizationResult:
        np = _load_numpy()
        current_holdings = self._eligible_current_holdings()
        current_total = sum(current_holdings.values())
        total_capital = current_total + self.extra_cash_czk
        if total_capital <= 0:
            raise ValueError("Celkový kapitál musí být kladný.")

        pool = self._build_candidate_pool(current_holdings)
        if not pool:
            raise RuntimeError("Nejsou dostupní žádní kandidáti pro optimalizaci.")

        current_tickers = set(current_holdings)
        subset = self._initial_subset(pool, current_holdings)
        if not subset:
            raise RuntimeError("Nepodařilo se sestavit počáteční portfolio.")

        self.log(f"Načteno {len(self.records)} akcií, pro výběr používám pool {len(pool)} kandidátů.")
        self.log(f"Stávající portfolio obsahuje {len(current_holdings)} použitelných pozic, cílem je {self.target_positions} pozic.")

        best_subset = subset
        best_objective, best_weights, best_return, best_vol, best_sold = self._evaluate_subset(best_subset, current_holdings, total_capital)

        ordered_pool = sorted(pool, key=lambda record: record.sharpe, reverse=True)
        improvement = True
        iteration = 0
        global_deadline = time.monotonic() + 30.0
        while improvement and iteration < 6:
            if self._should_stop() or time.monotonic() >= global_deadline:
                break
            improvement = False
            iteration += 1
            ranked_subset = sorted(zip(best_subset, best_weights), key=lambda item: (item[1], item[0].sharpe))
            outside = [record for record in ordered_pool if record.ticker not in {item.ticker for item in best_subset}]
            outside = outside[: max(self.target_positions * 3, 40)]

            for replace_record, _ in ranked_subset[: max(3, min(len(ranked_subset), 8))]:
                if self._should_stop() or time.monotonic() >= global_deadline:
                    break
                for candidate in outside:
                    if self._should_stop() or time.monotonic() >= global_deadline:
                        break
                    if replace_record.ticker == candidate.ticker:
                        continue
                    trial_subset = [record for record in best_subset if record.ticker != replace_record.ticker] + [candidate]
                    trial_tickers = {record.ticker for record in trial_subset}
                    if len(trial_tickers) != len(trial_subset):
                        continue
                    if not self._is_feasible_subset(trial_tickers, current_tickers):
                        continue

                    trial_objective, trial_weights, trial_return, trial_vol, trial_sold = self._evaluate_subset(
                        trial_subset, current_holdings, total_capital
                    )
                    if self.max_turnover_czk is not None and trial_sold > self.max_turnover_czk + 1e-6:
                        continue
                    if trial_objective > best_objective + 1e-5:
                        best_subset = trial_subset
                        best_objective = trial_objective
                        best_weights = trial_weights
                        best_return = trial_return
                        best_vol = trial_vol
                        best_sold = trial_sold
                        improvement = True
                        self.log(
                            f"Výměna {replace_record.ticker} -> {candidate.ticker} zlepšila cílové Sharpe na {best_objective:.3f}."
                        )
                        break
                if improvement:
                    break

        if self.max_turnover_czk is not None and best_sold > self.max_turnover_czk + 1e-6:
            self.log("Nenašel jsem řešení v zadaném limitu protočeného kapitálu, vracím se k šetrnějšímu složení.")
            best_subset = self._initial_subset(pool, current_holdings)
            best_objective, best_weights, best_return, best_vol, best_sold = self._evaluate_subset(
                best_subset, current_holdings, total_capital
            )

        final_tickers = [record.ticker for record in best_subset]
        current_amount_vector = np.array([current_holdings.get(record.ticker, 0.0) for record in best_subset], dtype=float)
        target_vector = best_weights * total_capital
        target_amount_map = {record.ticker: target_czk for record, target_czk in zip(best_subset, target_vector)}

        for ticker, current_czk in current_holdings.items():
            target_czk = target_amount_map.get(ticker, 0.0)
            trade_size = abs(target_czk - current_czk)
            is_full_exit = target_czk <= 1.0
            if 0 < trade_size < self.min_trade_czk and not is_full_exit:
                target_amount_map[ticker] = current_czk

        for ticker, target_czk in list(target_amount_map.items()):
            current_czk = current_holdings.get(ticker, 0.0)
            trade_size = abs(target_czk - current_czk)
            if current_czk <= 1.0 and 0 < trade_size < self.min_trade_czk:
                target_amount_map[ticker] = 0.0

        target_vector = np.array([target_amount_map.get(record.ticker, 0.0) for record in best_subset], dtype=float)
        target_sum = float(target_vector.sum())
        if target_sum > 0:
            adjustment_budget = total_capital - target_sum
            if abs(adjustment_budget) >= 1e-6:
                adjustable = [
                    idx for idx, record in enumerate(best_subset)
                    if target_amount_map.get(record.ticker, 0.0) > 0
                    and abs(target_amount_map.get(record.ticker, 0.0) - current_holdings.get(record.ticker, 0.0)) >= self.min_trade_czk
                ]
                if not adjustable:
                    adjustable = [idx for idx, record in enumerate(best_subset) if target_amount_map.get(record.ticker, 0.0) > 0]
                if adjustable:
                    extra_piece = adjustment_budget / len(adjustable)
                    for idx in adjustable:
                        target_vector[idx] = max(0.0, target_vector[idx] + extra_piece)

        final_tickers = [record.ticker for record in best_subset]
        final_expected = np.array([record.forecast_pct for record in best_subset], dtype=float)
        final_stds = np.array([record.std_pct for record in best_subset], dtype=float)
        final_current = np.array([current_holdings.get(ticker, 0.0) for ticker in final_tickers], dtype=float)
        final_corr = build_correlation_matrix(final_tickers, self.cache, self.log)
        final_cov = _safe_covariance_matrix(final_stds, final_corr.copy())
        
        final_dropped_czk = sum(amt for t, amt in current_holdings.items() if t not in final_tickers)
        
        final_objective, final_profit_czk, final_risk_czk, _, _ = _objective_from_target_amounts(
            target_vector,
            final_expected,
            final_cov,
            final_current,
            self.sale_penalty_rate,
            final_dropped_czk,
        )

        best_return = final_profit_czk / max(total_capital, 1e-12)
        best_vol = final_risk_czk / max(total_capital, 1e-12)
        best_objective = final_objective

        trade_lines: list[TradeLine] = []
        removed_positions = 0

        for record, target_czk in sorted(zip(best_subset, target_vector), key=lambda item: item[1], reverse=True):
            current_czk = current_holdings.get(record.ticker, 0.0)
            delta = target_czk - current_czk
            if delta > 1.0:
                action = "BUY"
            elif delta < -1.0:
                action = "SELL"
            else:
                action = "KEEP"
            trade_lines.append(
                TradeLine(
                    ticker=record.ticker,
                    current_czk=current_czk,
                    target_czk=target_czk,
                    delta_czk=delta,
                    action=action,
                    sharpe=record.sharpe,
                    forecast_pct=record.forecast_pct,
                    std_pct=record.std_pct,
                    upside_pct=record.upside_pct,
                    horizon_data=record.horizon_data,
                )
            )

        for ticker, amount in current_holdings.items():
            if ticker in final_tickers:
                continue
            removed_positions += 1
            record = self.record_map[ticker]
            trade_lines.append(
                TradeLine(
                    ticker=ticker,
                    current_czk=amount,
                    target_czk=0.0,
                    delta_czk=-amount,
                    action="SELL_ALL",
                    sharpe=record.sharpe,
                    forecast_pct=record.forecast_pct,
                    std_pct=record.std_pct,
                    upside_pct=record.upside_pct,
                    horizon_data=record.horizon_data,
                )
            )

        sold_czk = sum(max(line.current_czk - line.target_czk, 0.0) for line in trade_lines)
        penalty_czk = sold_czk * self.sale_penalty_rate
        invested_czk = max(0.0, total_capital - penalty_czk)
        final_weights = target_vector / max(total_capital, 1e-12)

        return OptimizationResult(
            records=best_subset,
            weights=final_weights,
            sharpe=best_objective,
            expected_return=best_return,
            volatility=best_vol,
            sold_czk=sold_czk,
            penalty_czk=penalty_czk,
            invested_czk=invested_czk,
            trades=trade_lines,
            target_total_czk=total_capital,
            current_total_czk=current_total,
            extra_cash_czk=self.extra_cash_czk,
            position_changes=removed_positions,
            min_trade_czk=self.min_trade_czk,
        )



import json
import threading

class TickerMetadataFetcher:
    def __init__(self, log_fn):
        self.log_fn = log_fn
        from pathlib import Path
        self.cache_file = Path("portfolios/portfolio_metadata_cache.json")
        self.cache = {}
        self._load()

    def _load(self):
        if self.cache_file.exists():
            try:
                with open(self.cache_file, "r", encoding="utf-8") as f:
                    self.cache = json.load(f)
            except: pass

    def _save(self):
        try:
            self.cache_file.parent.mkdir(parents=True, exist_ok=True)
            with open(self.cache_file, "w", encoding="utf-8") as f:
                json.dump(self.cache, f, indent=4)
        except: pass

    def fetch_async(self, tickers: list[str], callback):
        def worker():
            yf = _load_yfinance()
            if not yf:
                callback({})
                return
            updated = False
            results = {}
            for t in tickers:
                if t in self.cache:
                    results[t] = self.cache[t]
                else:
                    try:
                        tkr = yf.Ticker(t)
                        info = tkr.info
                        name = info.get("shortName", info.get("longName", t))
                        sector = info.get("sector", "N/A")
                        price = info.get("currentPrice", info.get("regularMarketPrice", 0.0))
                        mcap = info.get("marketCap", 0)
                        if mcap > 1e9: mcap_str = f"{mcap/1e9:.1f}B"
                        elif mcap > 1e6: mcap_str = f"{mcap/1e6:.1f}M"
                        else: mcap_str = str(mcap)
                        
                        data = {"name": name, "sector": sector, "price": price, "mcap": mcap_str}
                        self.cache[t] = data
                        results[t] = data
                        updated = True
                    except Exception:
                        results[t] = {"name": t, "sector": "N/A", "price": 0.0, "mcap": "0"}
            if updated: self._save()
            callback(results)
        threading.Thread(target=worker, daemon=True).start()


class PortfolioManagerApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Portfolio Manager")
        self.root.geometry("1180x860")

        self.base_dir = Path(__file__).resolve().parent
        self.records: list[StockRecord] = []
        self.fallback_prediction_cache: dict[str, dict[str, float]] = {}
        self.fallback_prediction_inflight: set[str] = set()
        self.meta_path: Path | None = None
        self.worker_thread: threading.Thread | None = None
        self.stop_event: threading.Event | None = None
        self.ui_queue: Queue = Queue()
        self.is_loading_meta = False
        self.last_chart_data: dict | None = None
        self.loaded_historical_projections: dict | None = None
        self.is_optimizing = False

        main = ttk.Frame(root, padding=12)
        main.pack(fill=tk.BOTH, expand=True)

        header = ttk.Frame(main)
        header.pack(fill=tk.X, pady=(0, 10))

        self.reload_button = ttk.Button(header, text="Spustit hromadnou EMA analytiku", command=self.reload_meta_async)
        self.reload_button.pack(side=tk.LEFT)
        self.load_ai_button = ttk.Button(header, text="Načíst AI Kvantily (CSV)", command=self._load_ai_csv)
        self.load_ai_button.pack(side=tk.LEFT, padx=(8, 0))
        self.start_button = ttk.Button(header, text="Optimalizovat portfolio", command=self.start_optimization)
        self.start_button.pack(side=tk.RIGHT)
        self.stop_button = ttk.Button(header, text="Zastavit", command=self.request_stop, state=tk.DISABLED)
        self.stop_button.pack(side=tk.RIGHT, padx=(0, 8))

        self.meta_label_var = tk.StringVar(value="Meta soubor zatím nenačten.")
        ttk.Label(main, textvariable=self.meta_label_var).pack(fill=tk.X, pady=(0, 8))
        self.status_var = tk.StringVar(value="UI připraveno. Načítám data...")
        ttk.Label(main, textvariable=self.status_var).pack(fill=tk.X, pady=(0, 6))
        self.progress = ttk.Progressbar(main, mode="indeterminate")
        self.progress.pack(fill=tk.X, pady=(0, 10))

        input_frame = ttk.Frame(main)
        input_frame.pack(fill=tk.X, pady=(0, 10))

        left = ttk.LabelFrame(input_frame, text="Aktuální portfolio", padding=10)
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 8))

        # Add Ticker input
        add_frame = ttk.Frame(left)
        add_frame.pack(fill=tk.X, pady=(0, 5))
        ttk.Label(add_frame, text="Ticker:").pack(side=tk.LEFT)
        self.add_ticker_var = tk.StringVar()
        ttk.Entry(add_frame, textvariable=self.add_ticker_var, width=8).pack(side=tk.LEFT, padx=5)
        ttk.Label(add_frame, text="CZK:").pack(side=tk.LEFT)
        self.add_amount_var = tk.StringVar()
        ttk.Entry(add_frame, textvariable=self.add_amount_var, width=10).pack(side=tk.LEFT, padx=5)
        ttk.Button(add_frame, text="Přidat/Upravit", command=self._add_holding).pack(side=tk.LEFT, padx=2)
        ttk.Button(add_frame, text="Odebrat", command=self._remove_holding).pack(side=tk.LEFT, padx=2)

        # Treeview
        self.port_tree = ttk.Treeview(
            left,
            columns=("ticker", "name", "sector", "price", "mcap", "czk", "pred", "q10", "q90", "avg_below_q10", "avg_above_q90"),
            show="headings",
            height=8,
        )
        p_headings = {
            "ticker": "Ticker",
            "name": "Název",
            "sector": "Sektor",
            "price": "Cena USD",
            "mcap": "Market Cap",
            "czk": "Hodnota CZK",
            "pred": "Predikce %",
            "q10": "Q10 %",
            "q90": "Q90 %",
            "avg_below_q10": "Průměr <Q10 %",
            "avg_above_q90": "Průměr >Q90 %",
        }
        for col, lab in p_headings.items():
            self.port_tree.heading(col, text=lab)
            self.port_tree.column(col, width=60 if col != "name" else 120, anchor=tk.CENTER)
        self.port_tree.pack(fill=tk.BOTH, expand=True, pady=(0, 6))

        self.portfolio_dict = {}
        self.portfolio_history = []
        self.portfolio_projections = []
        self.total_dividends = 0.0
        self.current_portfolio_path = None
        self.fetcher = TickerMetadataFetcher(self.log)

        holdings_btn_frame = ttk.Frame(left)
        holdings_btn_frame.pack(fill=tk.X, pady=(6, 0))
        ttk.Button(holdings_btn_frame, text="Nové", command=self._new_portfolio).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(holdings_btn_frame, text="💾 Uložit", command=self._save_portfolio).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(holdings_btn_frame, text="📂 Načíst", command=self._load_portfolio_from_file).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(holdings_btn_frame, text="📈 Graf s historií", command=self._on_show_graph_btn_click).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(holdings_btn_frame, text="📌 Připnout Predikci", command=self._pin_prediction).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(holdings_btn_frame, text="🗑 Smazat historii", command=self._clear_projections_history).pack(side=tk.LEFT, padx=(4, 4))
        
        self.apply_btn = ttk.Button(holdings_btn_frame, text="Aplikovat Obchody", command=self._open_apply_trades_dialog, state=tk.DISABLED)
        self.apply_btn.pack(side=tk.LEFT)
        
        # Add Dividends display
        self.div_var = tk.StringVar(value="Statistika | Celkové obdržené dividendy: 0 CZK")
        ttk.Label(left, textvariable=self.div_var, font=("Arial", 9, "bold")).pack(anchor=tk.W, pady=(5, 0))

        right = ttk.LabelFrame(input_frame, text="Nastavení", padding=10)
        right.pack(side=tk.LEFT, fill=tk.Y)

        self.extra_cash_var = tk.StringVar(value="0")
        self.target_positions_var = tk.IntVar(value=50)
        self.max_turnover_var = tk.StringVar(value="")
        self.max_swaps_var = tk.StringVar(value="")
        self.sale_penalty_var = tk.DoubleVar(value=0.02)
        self.min_trade_var = tk.StringVar(value="25")
        
        self.alpha_1w_var = tk.DoubleVar(value=1.0)
        self.alpha_4w_var = tk.DoubleVar(value=0.9)
        self.alpha_13w_var = tk.DoubleVar(value=0.8)
        self.alpha_26w_var = tk.DoubleVar(value=0.7)
        self.alpha_52w_var = tk.DoubleVar(value=0.5)

        self._add_labeled_entry(right, "Dodatečný kapitál (CZK)", self.extra_cash_var)
        self._add_labeled_entry(right, "Cílový počet akcií", self.target_positions_var)
        self._add_labeled_entry(right, "Max protočit kapitál (CZK)", self.max_turnover_var)
        self._add_labeled_entry(right, "Max vyměnit pozic", self.max_swaps_var)
        self._add_labeled_entry(right, "Postih za prodej", self.sale_penalty_var)
        self._add_labeled_entry(right, "Minimální obchod (CZK)", self.min_trade_var)
        
        self._add_labeled_entry(right, "Alfa 1w", self.alpha_1w_var)
        self._add_labeled_entry(right, "Alfa 4w", self.alpha_4w_var)
        self._add_labeled_entry(right, "Alfa 13w", self.alpha_13w_var)
        self._add_labeled_entry(right, "Alfa 26w", self.alpha_26w_var)
        self._add_labeled_entry(right, "Alfa 52w", self.alpha_52w_var)

        table_frame = ttk.LabelFrame(main, text="Načtený vesmír akcií", padding=10)
        table_frame.pack(fill=tk.BOTH, expand=False, pady=(0, 10))

        self.tree = ttk.Treeview(table_frame, columns=("ticker", "sharpe", "forecast", "q10", "q90"), show="headings", height=10)
        headings = {"ticker": "Ticker", "sharpe": "Sharpe", "forecast": "Oček. výnos %", "q10": "Downside %", "q90": "Upside %"}
        for column, label in headings.items():
            self.tree.heading(column, text=label)
            self.tree.column(column, width=100 if column != "ticker" else 90, anchor=tk.CENTER)
        self.tree.pack(fill=tk.BOTH, expand=True)

        self.log_box = tk.Text(main, height=16, state=tk.DISABLED)
        self.log_box.pack(fill=tk.BOTH, expand=True)

        self.root.after(100, self._drain_ui_queue)
        self.root.after(150, self.reload_meta_async)

    def _add_labeled_entry(self, parent: ttk.Widget, label: str, variable):
        ttk.Label(parent, text=label).pack(anchor=tk.W, pady=(4, 0))
        ttk.Entry(parent, textvariable=variable, width=24).pack(anchor=tk.W, fill=tk.X)

    def _append_log(self, message: str):
        self.log_box.configure(state=tk.NORMAL)
        timestamp = dt.datetime.now().strftime("%H:%M:%S")
        self.log_box.insert(tk.END, f"[{timestamp}] {message}\n")
        self.log_box.see(tk.END)
        self.log_box.configure(state=tk.DISABLED)

    def log(self, message: str):
        if threading.current_thread() is threading.main_thread():
            self._append_log(message)
        else:
            self.ui_queue.put(("log", message))

    def _set_busy(self, active: bool, message: str):
        self.status_var.set(message)
        if active:
            self.progress.start(12)
        else:
            self.progress.stop()

        reload_state = tk.DISABLED if self.is_loading_meta or self.is_optimizing else tk.NORMAL
        start_state = tk.DISABLED if self.is_loading_meta or self.is_optimizing or not self.records else tk.NORMAL
        stop_state = tk.NORMAL if self.is_optimizing else tk.DISABLED
        self.reload_button.configure(state=reload_state)
        self.start_button.configure(state=start_state)
        self.stop_button.configure(state=stop_state)

    def _drain_ui_queue(self):
        try:
            while True:
                event = self.ui_queue.get_nowait()
                kind = event[0]
                if kind == "log":
                    self._append_log(event[1])
                elif kind == "meta_loaded":
                    _, path, records = event
                    self._finish_meta_load(path, records)
                elif kind == "meta_error":
                    self._handle_meta_error(event[1])
                elif kind == "opt_done":
                    self._finish_optimization(event[1])
                elif kind == "opt_error":
                    self._handle_optimization_error(event[1])
                elif kind == "opt_stopped":
                    self._finish_stopped_optimization()
                elif kind == "charts_ready":
                    self._display_charts(event[1])
                elif kind == "fallback_ready":
                    _, data, tickers = event
                    self.fallback_prediction_cache.update(data)
                    for t in tickers:
                        self.fallback_prediction_inflight.discard(t.upper())
                    if data:
                        self.log(f"Dopočítána fallback týdenní predikce pro {len(data)} tickerů.")
                    self._refresh_portfolio_tree()
        except Empty:
            pass
        self.root.after(100, self._drain_ui_queue)

    def reload_meta_async(self):
        if self.is_loading_meta or self.is_optimizing:
            return

        self.is_loading_meta = True
        self._set_busy(True, "Zpracovávám historii EMA analytiky...")
        self.log("Spouštím načtení a agregaci vícenásobných meta souborů.")

        alphas = {
            "1w": float(self.alpha_1w_var.get()),
            "4w": float(self.alpha_4w_var.get()),
            "13w": float(self.alpha_13w_var.get()),
            "26w": float(self.alpha_26w_var.get()),
            "52w": float(self.alpha_52w_var.get()),
        }

        def worker():
            try:
                records = load_historical_meta_and_calculate_ema(self.base_dir, alphas, self.log)
                path = Path("historie od 15.12.2025")
                self.ui_queue.put(("meta_loaded", path, records))
            except Exception as exc:
                self.ui_queue.put(("meta_error", str(exc)))

        threading.Thread(target=worker, daemon=True).start()

    def _finish_meta_load(self, path: Path, records: list[StockRecord]):
        self.meta_path = path
        # Seřadit podle sharpe ratio (sestupně) ihned po načtení
        records.sort(key=lambda x: x.sharpe, reverse=True)
        self.records = records
        self.meta_label_var.set(f"Použitý meta soubor: {self.meta_path}")
        self.tree.delete(*self.tree.get_children())
        for record in self.records[:150]:
            self.tree.insert(
                "",
                tk.END,
                values=(
                    record.ticker,
                    f"{record.sharpe:.3f}",
                    f"{record.forecast_pct * 100:.2f}",
                    f"{record.std_pct * 100:.2f}",
                    f"{record.upside_pct * 100:.2f}" if record.upside_pct else "-",
                ),
            )
        self.is_loading_meta = False
        self._set_busy(False, f"Načteno {len(self.records)} akcií z {self.meta_path.name}.")
        self._append_log(f"Načteno {len(self.records)} akcií z {self.meta_path.name}.")
        self._refresh_portfolio_tree()

    def _handle_meta_error(self, message: str):
        self.is_loading_meta = False
        self.records = []
        self.meta_path = None
        self.meta_label_var.set("Meta soubor se nepodařilo načíst.")
        self._set_busy(False, "Načtení meta souboru selhalo.")
        self._append_log(f"Chyba při načítání meta souboru: {message}")
        messagebox.showerror("Chyba", message)
        
    def _load_ai_csv(self):
        if not self.records:
            messagebox.showwarning("Chyba", "Nejprve načtěte EMA analytiku.")
            return
            
        path = filedialog.askopenfilename(
            title="Vyberte CSV s AI Kvantily",
            filetypes=[("CSV Files", "*.csv"), ("All Files", "*.*")]
        )
        if not path:
            return
            
        try:
            pd = _load_pandas()
            df = pd.read_csv(path)
            if "Ticker" not in df.columns:
                messagebox.showerror("Chyba", "CSV neobsahuje sloupec 'Ticker'!")
                return
                
            updates = 0
            record_map = {r.ticker: r for r in self.records}
            import math
            
            for _, row in df.iterrows():
                ticker = str(row["Ticker"]).strip().upper()
                if ticker in record_map:
                    rec = record_map[ticker]
                    
                    q10_val = row.get("q10_1w")
                    q90_val = row.get("q90_1w")
                    mean_val = row.get("mean_1w")
                    
                    if pd.notna(q10_val) and pd.notna(mean_val):
                        # q10/q90 jsou reziduály (odchylky od predikce)
                        # q10 je typicky záporný -> downside = abs(q10)
                        # q90 je typicky kladný -> upside = max(0, q90)
                        downside = max(1e-6, max(1e-6, mean_val - q10_val))
                        upside_bonus = max(0.0, q90_val - mean_val) if pd.notna(q90_val) else 0.0
                        
                        rec.std_pct = downside
                        rec.upside_pct = upside_bonus
                        rec.forecast_pct = mean_val
                        # Modifikovany asymetricky cil (Čistá střední hodnota / Downside)
                        rec.sharpe = rec.forecast_pct / max(downside, 1e-6)
                        updates += 1
                        
            # Re-sort a update UI
            self.records.sort(key=lambda x: x.sharpe, reverse=True)
            self._finish_meta_load(self.meta_path if self.meta_path else Path("AI Data"), self.records)
            self.log(f"Úspěšně nahrazeno/aktualizováno {updates} Tickerů z CSV (q10 Downside, q90 Upside).")
            
        except Exception as e:
            messagebox.showerror("Chyba čtení CSV", str(e))

    def start_optimization(self):
        if self.is_loading_meta:
            messagebox.showinfo("Načítání dat", "Vyčkejte, než se dokončí načtení meta souboru.")
            return

        if self.worker_thread is not None and self.worker_thread.is_alive():
            messagebox.showinfo("Probíhá výpočet", "Vyčkejte na dokončení nebo použijte 'Zastavit'.")
            return

        if not self.records or self.meta_path is None:
            messagebox.showwarning("Chybí data", "Nejdříve načtěte meta soubor.")
            return

        try:
            holdings = parse_holdings_text(self.get_holdings_text())
            extra_cash_czk = _safe_float(self.extra_cash_var.get(), default=0.0)
            target_positions = int(self.target_positions_var.get())
            max_turnover = self.max_turnover_var.get().strip()
            max_swaps = self.max_swaps_var.get().strip()
            sale_penalty_rate = float(self.sale_penalty_var.get())
            min_trade_czk = _safe_float(self.min_trade_var.get(), default=25.0)
        except Exception as exc:
            messagebox.showerror("Chyba vstupu", str(exc))
            return

        record_tickers = {r.ticker for r in self.records}
        missing = [t for t in holdings.keys() if t not in record_tickers]
        if missing:
            msg = (
                f"Tyto tickery z vašeho portfolia nemáme k dispozici v současných datech "
                f"(možná překlep, nebo starší akcie, kterou už AI nesleduje):\n\n"
                f"{', '.join(missing)}\n\n"
                f"Při optimalizaci z nich budou algoritmem vyjmuty. Pokračovat?"
            )
            # You can simply show a warning, or ask for confirmation. Let's just show info for now:
            messagebox.showwarning("Neznámé tickery", msg)

        if target_positions <= 0:
            messagebox.showerror("Chyba vstupu", "Cílový počet akcií musí být kladný.")
            return
        if extra_cash_czk < 0:
            messagebox.showerror("Chyba vstupu", "Dodatečný kapitál nemůže být záporný.")
            return
        if min_trade_czk < 0:
            messagebox.showerror("Chyba vstupu", "Minimální obchod nemůže být záporný.")
            return

        max_turnover_czk = None if not max_turnover else _safe_float(max_turnover)
        max_swaps_int = None if not max_swaps else int(_safe_float(max_swaps))

        self.stop_event = threading.Event()
        self.is_optimizing = True
        self._set_busy(True, "Probíhá optimalizace portfolia...")
        self.log("Výpočet spuštěn. Připravuji optimalizaci portfolia.")

        def worker():
            try:
                manager = PortfolioManager(
                    records=self.records,
                    current_holdings_czk=holdings,
                    extra_cash_czk=extra_cash_czk,
                    target_positions=target_positions,
                    sale_penalty_rate=sale_penalty_rate,
                    max_turnover_czk=max_turnover_czk,
                    max_position_replacements=max_swaps_int,
                    min_trade_czk=min_trade_czk,
                    log_fn=self.log,
                    stop_event=self.stop_event,
                )
                result = manager.optimize()
                if self.stop_event is not None and self.stop_event.is_set():
                    self.ui_queue.put(("opt_stopped",))
                    return
                self.ui_queue.put(("opt_done", result))
            except Exception as exc:  # pragma: no cover - UI path
                self.ui_queue.put(("opt_error", str(exc)))

        self.worker_thread = threading.Thread(target=worker, daemon=True)
        self.worker_thread.start()

    def request_stop(self):
        if self.stop_event is not None:
            self.stop_event.set()
            self.status_var.set("Zastavuji výpočet...")
            self._append_log("Byl odeslán požadavek na zastavení výpočtu.")

    def _finish_optimization(self, result: OptimizationResult):
        self.is_optimizing = False
        self._set_busy(False, "Optimalizace dokončena.")
        self.last_result = result
        self.apply_btn.config(state=tk.NORMAL)
        self.log(f"Optimalizace hotova. Cílové Sharpe: {result.sharpe:.3f}")
        self._start_chart_computation(result, None)

    def _handle_optimization_error(self, message: str):
        self.is_optimizing = False
        self._set_busy(False, "Optimalizace selhala.")
        self._append_log(f"Chyba při optimalizaci: {message}")
        messagebox.showerror("Chyba", message)

    def _finish_stopped_optimization(self):
        self.is_optimizing = False
        self._set_busy(False, "Výpočet byl zastaven.")
        self._append_log("Výpočet byl zastaven uživatelem.")
        
    def _on_apply_btn_click(self):
        if hasattr(self, 'last_result') and self.last_result:
            self._apply_calculated_portfolio(self.last_result)

    

    
    def _export_portfolio_json(self):
        import datetime
        return {
            "version": 2,
            "holdings": self.portfolio_dict,
            "extra_cash": float(self.extra_cash_var.get() or 0),
            "dividends": self.total_dividends,
            "history": self.portfolio_history,
            "projections": self.portfolio_projections,
            "last_saved": datetime.datetime.now().isoformat()
        }

    def _import_portfolio_json(self, data):
        self.portfolio_dict = data.get("holdings", {})
        self.extra_cash_var.set(str(data.get("extra_cash", 0.0)))
        self.total_dividends = data.get("dividends", 0.0)
        self.portfolio_history = data.get("history", [])
        self.portfolio_projections = data.get("projections", [])
        self.div_var.set(f"Statistika | Celkové obdržené dividendy: {self.total_dividends:.2f} CZK")
        self._refresh_portfolio_tree()

    def _save_portfolio(self):
        if self.current_portfolio_path:
            import json
            from tkinter import messagebox
            try:
                self.current_portfolio_path.parent.mkdir(parents=True, exist_ok=True)
                with open(self.current_portfolio_path, "w", encoding="utf-8") as f:
                    json.dump(self._export_portfolio_json(), f, indent=4)
                self.log(f"Portfolio uloženo: {self.current_portfolio_path.name}")
            except Exception as e:
                messagebox.showerror("Chyba", str(e))
        else:
            self._save_portfolio_as()

    def _save_portfolio_as(self):
        portfolios_dir = self.base_dir / "portfolios"
        portfolios_dir.mkdir(parents=True, exist_ok=True)
        from tkinter import filedialog
        filepath = filedialog.asksaveasfilename(
            title="Uložit portfolio jako...",
            initialdir=str(portfolios_dir),
            defaultextension=".json",
            filetypes=[("JSON soubory", "*.json")],
        )
        if not filepath:
            return
        self.current_portfolio_path = Path(filepath)
        self._save_portfolio()

    def _load_portfolio_from_file(self):
        portfolios_dir = self.base_dir / "portfolios"
        portfolios_dir.mkdir(parents=True, exist_ok=True)
        from tkinter import filedialog
        filepath = filedialog.askopenfilename(
            title="Načíst portfolio ze souboru...",
            initialdir=str(portfolios_dir),
            filetypes=[("JSON soubory", "*.json"), ("Textové soubory", "*.txt")],
        )
        if not filepath:
            return
        self._load_portfolio(Path(filepath))

    def _load_portfolio(self, path=None, quiet=False):
        if not path:
            path = self.base_dir / "portfolios" / "default.json"
        
        if not path.exists():
            return

        import json
        from tkinter import messagebox
        try:
            with open(path, "r", encoding="utf-8") as f:
                if path.suffix == ".json":
                    data = json.load(f)
                    self._import_portfolio_json(data)
                else: 
                    p_text = f.read().strip()
                    self.portfolio_dict = parse_holdings_text(p_text)
                    self._refresh_portfolio_tree()
            self.current_portfolio_path = path
            if not quiet:
                self.log(f"Portfolio úspěšně načteno: {path.name}")
        except Exception as e:
            if not quiet:
                messagebox.showerror("Chyba čtení", str(e))

    def get_holdings_text(self):
        return "\n".join([f"{k} {v}" for k, v in self.portfolio_dict.items()])

    def _refresh_portfolio_tree(self):
        for item in self.port_tree.get_children():
            self.port_tree.delete(item)
        records_by_ticker = {record.ticker.upper(): record for record in self.records}
        missing_fallback = [
            t.upper()
            for t in self.portfolio_dict.keys()
            if t.upper() not in records_by_ticker
            and t.upper() not in self.fallback_prediction_cache
            and t.upper() not in self.fallback_prediction_inflight
        ]
        if missing_fallback:
            self._load_fallback_predictions_async(missing_fallback)
        
        def update_rows(metadata):
            for t, amt in self.portfolio_dict.items():
                meta = metadata.get(t, {"name": t, "sector": "N/A", "price": 0.0, "mcap": "0"})
                record = records_by_ticker.get(t.upper())
                fallback = self.fallback_prediction_cache.get(t.upper())
                pred = f"{record.forecast_pct * 100:.2f}" if record else (f"{fallback['pred'] * 100:.2f}" if fallback else "-")
                q10 = f"{record.std_pct * 100:.2f}" if record else (f"{fallback['q10'] * 100:.2f}" if fallback else "-")
                q90 = f"{record.upside_pct * 100:.2f}" if record else (f"{fallback['q90'] * 100:.2f}" if fallback else "-")
                avg_below_q10 = f"{fallback['avg_below_q10'] * 100:.2f}" if fallback else "-"
                avg_above_q90 = f"{fallback['avg_above_q90'] * 100:.2f}" if fallback else "-"
                self.port_tree.insert(
                    "",
                    tk.END,
                    values=(t, meta["name"], meta["sector"], f"{meta['price']:.2f}", meta["mcap"], f"{amt:.2f}", pred, q10, q90, avg_below_q10, avg_above_q90),
                )
                
        self.fetcher.fetch_async(list(self.portfolio_dict.keys()), lambda m: self.root.after(0, update_rows, m))

    def _load_fallback_predictions_async(self, tickers: list[str]) -> None:
        tickers = [t.upper() for t in tickers if t]
        if not tickers:
            return
        self.fallback_prediction_inflight.update(tickers)

        def worker():
            data = self._compute_weekly_fallback_predictions(tickers)
            self.ui_queue.put(("fallback_ready", data, tickers))

        threading.Thread(target=worker, daemon=True).start()

    def _compute_weekly_fallback_predictions(self, tickers: list[str]) -> dict[str, dict[str, float]]:
        np = _load_numpy()
        pd = _load_pandas()
        yf = _load_yfinance()
        if not yf:
            return {}
        try:
            prices = yf.download(tickers, period="5y", interval="1wk", auto_adjust=True, progress=False)["Close"]
        except Exception:
            return {}
        if isinstance(prices, pd.Series):
            prices = prices.to_frame(name=tickers[0])

        result: dict[str, dict[str, float]] = {}
        for ticker in tickers:
            if ticker not in prices.columns:
                continue
            weekly_returns = prices[ticker].dropna().pct_change().dropna()
            if len(weekly_returns) < 20:
                continue
            q10 = float(weekly_returns.quantile(0.10))
            q90 = float(weekly_returns.quantile(0.90))
            below = weekly_returns[weekly_returns <= q10]
            above = weekly_returns[weekly_returns >= q90]
            result[ticker] = {
                "pred": float(weekly_returns.mean()),
                "q10": q10,
                "q90": q90,
                "avg_below_q10": float(np.nan_to_num(below.mean(), nan=0.0)),
                "avg_above_q90": float(np.nan_to_num(above.mean(), nan=0.0)),
            }
        return result

    def _add_holding(self):
        t = self.add_ticker_var.get().upper().strip()
        amt_str = self.add_amount_var.get().strip()
        if not t or not amt_str: return
        try:
            amt = float(amt_str)
            self.portfolio_dict[t] = amt
            self._refresh_portfolio_tree()
            self.add_ticker_var.set("")
            self.add_amount_var.set("")
        except:
            messagebox.showerror("Chyba", "Neplatná částka")

    def _remove_holding(self):
        t = self.add_ticker_var.get().upper().strip()
        if t in self.portfolio_dict:
            del self.portfolio_dict[t]
            self._refresh_portfolio_tree()
            self.add_ticker_var.set("")

    def _new_portfolio(self):
        self.portfolio_dict = {}
        self.portfolio_history = []
        self.portfolio_projections = []
        self.total_dividends = 0.0
        self.current_portfolio_path = None
        self.extra_cash_var.set("0")
        self.div_var.set("Statistika | Celkové obdržené dividendy: 0 CZK")
        self._refresh_portfolio_tree()


    def _pin_prediction(self):
        if not self.last_result:
            from tkinter import messagebox
            messagebox.showinfo("Chyba", "Nejprve spusťte optimalizaci pro vytvoření predikce.")
            return
            
        import datetime
        now_str = datetime.datetime.now().isoformat()
        
        # Calculate expected equity over time
        total_cash = float(self.extra_cash_var.get())
        total_val = sum(self.portfolio_dict.values()) + total_cash
        
        expected_returns = []
        for t in self.last_result.trades:
            if t.target_czk > 0:
                expected_returns.append(t.forecast_pct / 100.0) # Approx
                
        # Simplified: we use the overall expected return from the result
        overall_expected = self.last_result.expected_profit_czk / max(1.0, total_val)
        
        dates = []
        expected_vals = []
        now = datetime.datetime.now()
        
        for w in [1, 4, 13, 26, 52]:
            dates.append((now + datetime.timedelta(weeks=w)).isoformat())
            # Linearly scale the annual expected return
            val = total_val * (1.0 + overall_expected * (w / 52.0))
            expected_vals.append(val)
            
        self.portfolio_projections.append({
            "date": now_str,
            "start_value": total_val,
            "dates": dates,
            "expected": expected_vals
        })
        self._save_portfolio()
        from tkinter import messagebox
        messagebox.showinfo("Hotovo", "Aktuální predikce byla připnuta k portfoliu!")

    def _open_apply_trades_dialog(self):
        if not self.last_result: return
        import tkinter as tk
        from tkinter import ttk
        from tkinter import messagebox
        import datetime

        top = tk.Toplevel(self.root)
        top.title("Aplikovat obchody (Executer)")
        top.geometry("800x600")

        ttk.Label(top, text="Potvrzení a ruční úprava obchodů", font=("Arial", 12, "bold")).pack(pady=10)

        cols = ("ticker", "action", "amount", "price", "fee")
        tree = ttk.Treeview(top, columns=cols, show="headings", height=15)
        headings = {"ticker": "Ticker", "action": "Akce", "amount": "Množství (CZK)", "price": "Realizační Cena", "fee": "Poplatek 2%"}
        for c, l in headings.items():
            tree.heading(c, text=l)
            tree.column(c, anchor=tk.CENTER)
        tree.pack(fill=tk.BOTH, expand=True, padx=10)

        trades_data = []
        for trade in self.last_result.trades:
            if trade.action == "KEEP": continue
            amt = abs(trade.delta_czk)
            fee = amt * 0.02
            trades_data.append({
                "ticker": trade.ticker,
                "action": trade.action,
                "amount": amt,
                "price": amt, 
                "fee": fee
            })
            tree.insert("", tk.END, values=(trade.ticker, trade.action, f"{amt:.2f}", f"{amt:.2f}", f"{fee:.2f}"))

        def apply():
            try:
                total_cash_change = 0.0
                for data in trades_data:
                    t = data["ticker"]
                    act = data["action"]
                    amt = data["amount"]
                    fee = data["fee"]
                    
                    if act == "BUY":
                        self.portfolio_dict[t] = self.portfolio_dict.get(t, 0.0) + amt
                        total_cash_change -= (amt + fee)
                    elif act.startswith("SELL"):
                        val = min(self.portfolio_dict.get(t, 0.0), amt)
                        self.portfolio_dict[t] -= val
                        if self.portfolio_dict[t] < 1.0:
                            del self.portfolio_dict[t]
                        total_cash_change += (val - fee)
                
                new_cash = float(self.extra_cash_var.get()) + total_cash_change
                self.extra_cash_var.set(f"{new_cash:.2f}")

                # Save history point
                total_eq = new_cash + sum(self.portfolio_dict.values())
                import datetime
                self.portfolio_history.append({
                    "timestamp": datetime.datetime.now().isoformat(),
                    "total_equity": total_eq
                })

                self._refresh_portfolio_tree()
                self._save_portfolio()
                messagebox.showinfo("Hotovo", "Obchody byly aplikovány a portfolio uloženo.")
                top.destroy()
                self.apply_btn.config(state=tk.DISABLED)
                self.last_result = None
            except Exception as e:
                messagebox.showerror("Chyba", str(e))

        ttk.Button(top, text="Potvrdit a Aplikovat (Fixní 2% poplatek)", command=apply).pack(pady=10)

    def _on_apply_btn_click(self):
        self._open_apply_trades_dialog()

    def _report_result(self, result):
        pass # Not used anymore
        
    def _clear_projections_history(self):
        self.portfolio_projections = []
        self.portfolio_history = []
        self._save_portfolio()
        self.log("Historie predikcí a equity vymazána z portfolia.")

    def _on_show_graph_btn_click(self):
        self._start_chart_computation(None, None)

    def _show_comparison_window(self, result):
        pass # Replaced by the apply trades logic

    def _start_chart_computation(self, result, manual_holdings_text):
        if self.is_optimizing or self.is_loading_meta:
            self.log("Nyní nelze spustit grafy.")
            return
        self.log("Stahuji data z Yahoo Finance pro graf...")
        self._set_busy(True, "Stahuji data pro graf...")
        import threading
        def worker():
            try:
                chart_data = self._compute_chart_data(result, manual_holdings_text)
                self.ui_queue.put(("charts_ready", chart_data))
            except Exception as e:
                self.ui_queue.put(("log", f"Chyba grafů: {e}"))
        threading.Thread(target=worker, daemon=True).start()

    def _compute_chart_data(self, result, manual_holdings_text):
        np = _load_numpy()
        pd = _load_pandas()
        yf = _load_yfinance()

        if not yf: return None

        old_holdings = self.portfolio_dict.copy()
        extra_cash = float(self.extra_cash_var.get() or 0)
        old_total = sum(old_holdings.values()) + extra_cash

        valid_tickers = list(old_holdings.keys())
        if not valid_tickers: return None

        end_date = pd.Timestamp.today()
        start_date = end_date - pd.DateOffset(years=1)
        
        try:
            data = yf.download(valid_tickers + ["^GSPC"], start=start_date, end=end_date, progress=False)["Close"]
        except Exception:
            return None
            
        if "^GSPC" in data.columns:
            sp500 = data["^GSPC"].dropna()
        else:
            sp500 = None

        hist_dates = []
        hist_equity = []
        if sp500 is not None and not sp500.empty:
            hist_dates = sp500.index.tolist()
            # SP500 relative to portfolio start
            start_sp = sp500.iloc[0]
            hist_equity = (sp500 / start_sp * old_total).tolist()

        import datetime
        now = datetime.datetime.now()
        
        # Build current projection if we have records
        proj_dates = []
        expected_line = []
        q10_line = []
        q90_line = []
        
        if self.records:
            # Approximate from AI quantiles
            # For simplicity, we just use the expected return of current holdings
            pass # Skipping complex projection building for current

        return {
            "hist_dates": hist_dates,
            "sp500_czk": hist_equity,
            "now": now,
            "current_total": old_total,
            "projections": self.portfolio_projections,
            "history": self.portfolio_history
        }

    def _display_charts(self, chart_data):
        self._set_busy(False, "Graf zobrazen.")
        if not chart_data: return

        try:
            import matplotlib.pyplot as plt
            import matplotlib.dates as mdates
            from dateutil import parser
        except: return

        fig, ax = plt.subplots(figsize=(12, 7))
        
        # Plot SP500 Benchmark
        if chart_data["sp500_czk"]:
            ax.plot(chart_data["hist_dates"], chart_data["sp500_czk"], label="S&P 500 Benchmark (CZK ekvivalent)", color="black", alpha=0.3, linestyle="--")

        # Plot Real Equity History
        if chart_data["history"]:
            hx = [parser.parse(h["timestamp"]) for h in chart_data["history"]]
            hy = [h["total_equity"] for h in chart_data["history"]]
            ax.plot(hx, hy, label="Reálná Hodnota Portfolia", color="blue", linewidth=2, marker="o")

        # Plot Saved Projections
        colors = ["green", "orange", "purple", "brown", "pink"]
        for i, proj in enumerate(chart_data["projections"]):
            c = colors[i % len(colors)]
            p_date = parser.parse(proj["date"])
            p_val = proj["start_value"]
            
            # Draw anchor point
            ax.plot([p_date], [p_val], marker="D", color=c)
            
            # Draw projections
            px = [p_date] + [parser.parse(d) for d in proj.get("dates", [])]
            py = [p_val] + proj.get("expected", [])
            ax.plot(px, py, color=c, linestyle="-", alpha=0.6, label=f"Predikce {p_date.strftime('%d.%m.%Y')}")
            
            if py and len(py) > 1:
                ax.annotate(f"{py[-1]:.0f} CZK", xy=(px[-1], py[-1]), xytext=(5, 0), textcoords="offset points", color=c)

        ax.set_title("Vývoj Portfolia a Historické AI Predikce (Absolutní CZK)")
        ax.set_ylabel("Hodnota (CZK)")
        ax.xaxis.set_major_formatter(mdates.DateFormatter('%Y-%m'))
        ax.grid(True, alpha=0.3)
        ax.legend()
        plt.tight_layout()
        plt.show()

        # Save the current state as a projection snapshot if we have a new one
        # To do this correctly, we add a button in the UI.



def main() -> None:
    root = tk.Tk()
    PortfolioManagerApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
