import os
import sys
import time
import json
import random
import datetime
import traceback
import math
from collections import defaultdict, deque
from threading import Thread
import threading
import atexit
import signal
from queue import Queue, SimpleQueue
from functools import lru_cache
from concurrent.futures import ThreadPoolExecutor

EXECUTOR = ThreadPoolExecutor(max_workers=64)
# ───────── 매도 기준 전역 상수) ─────────
TP_RATIO = 1.008  
SL_RATIO = 0.992   
# ──────────────────────────────────────────────────────────────
# ───────── strategy_11 전역 상태 ─────────
strategy_11_conditions = {}       # 조건 딕셔너리
latest_strategy_log_count = 0     # 마지막으로 계산에 사용한 로그 행 수
# ────────────────────────────────────────
# ── Thread-pool watchdog ───────────────────────────
import psutil, threading, time, os
p = psutil.Process(os.getpid())

def thread_pool_watchdog():
    while True:
        active_threads = threading.active_count()
        queued_tasks   = EXECUTOR._work_queue.qsize()
        cpu_percent    = psutil.cpu_percent(interval=None)

        if queued_tasks > 0 or cpu_percent >= 50:
            print(f"[TP] 활성:{active_threads:3}  큐:{queued_tasks:3}  CPU:{cpu_percent:4.1f}%")

        time.sleep(2)
# ───────────────────────────────────────────────────

import glob
import warnings
warnings.filterwarnings("ignore", category=RuntimeWarning, module="ta.trend")

# 서드파티 라이브러리
import websocket
import requests
import yaml
import uuid
import pandas as pd
from ta.momentum import RSIIndicator
try: from ta.momentum import CMOIndicator
except ImportError:
    import pandas as pd
    class CMOIndicator:
        def __init__(self, close, window=14, fillna=False):
            close = pd.Series(close, dtype="float")
            up    = close.diff().clip(lower=0).rolling(window).sum()
            down  = (-close.diff().clip(upper=0)).rolling(window).sum()
            self._cmo = 100 * (up - down) / (up + down)
            if fillna: self._cmo = self._cmo.fillna(0)
        def cmo(self): return self._cmo
from ta.volatility import BollingerBands
from ta.trend import SMAIndicator

# 라이브러리 기반 지표 계산 함수 (RSI-14 / MA20 / Bollinger ±2σ)
def _calc_ta_indicators(closes: list[float]):
    import pandas as _pd
    _ser = _pd.Series(closes, dtype="float")
    _rsi = RSIIndicator(_ser, 14).rsi().iloc[-1]
    _ma  = SMAIndicator(_ser, 20).sma_indicator().iloc[-1]
    _bb  = BollingerBands(_ser, 20, 2)
    _up  = _bb.bollinger_hband().iloc[-1]
    _lo  = _bb.bollinger_lband().iloc[-1]

    # 볼린저밴드 역전 오류 방지 검사
    if not (_up > _ma > _lo):
        # 표준편차가 0(상·중·하단 완전 동일)인 경우는
        # 역전이 아니라 데이터 부족이므로 로그를 생략
        if not (_up == _ma == _lo):
            print(f"[오류] 볼린저밴드 역전 발생 → 상단: {_up}, 중단: {_ma}, 하단: {_lo}")

    return _rsi, _ma, _up, _lo

# 캔들 확정 시 ta 라이브러리 공식값으로 지표 덮어쓰기
def update_ta_indicators(tr_key: str):
    if len(candle_1min_map[tr_key]) >= 20:
        closes = [c["close"] for c in list(candle_1min_map[tr_key])[-20:]]
        rsi, ma, _, _ = _calc_ta_indicators(closes)
        _set_rsi(rsi_14_1min_map, tr_key, rsi)
        ma_20_1min_map[tr_key] = ma

    if len(candle_1min_map[tr_key]) >= 30:
        closes_30 = [c["close"] for c in list(candle_1min_map[tr_key])[-30:]]
        ma_30_1min_map[tr_key] = sum(closes_30) / 30
        
    if len(candle_3min_map[tr_key]) >= 20:
        closes = [c["close"] for c in list(candle_3min_map[tr_key])[-20:]]
        rsi, ma, _, _ = _calc_ta_indicators(closes)
        _set_rsi(rsi_14_3min_map, tr_key, rsi)
        ma_20_3min_map[tr_key] = ma

    if len(candle_3tick_map[tr_key]) >= 20:
        closes = [c["close"] for c in list(candle_3tick_map[tr_key])[-20:]]
        rsi, ma, _, _ = _calc_ta_indicators(closes)
        _set_rsi(rsi_14_3tick_map, tr_key, rsi)
        ma_20_3tick_map[tr_key] = ma
        
def call_api(method, url, headers=None, params=None, json_body=None, timeout=10):
    result_box = {"res": None, "err": None}

    def _task():
        try:
            if method == "GET":
                res = requests.get(url, headers=headers, params=params, timeout=timeout)
            elif method == "POST":
                res = requests.post(url, headers=headers, json=json_body, timeout=timeout)
            else:
                raise ValueError("지원하지 않는 method")

            if res.status_code != 200:
                result_box["err"] = f"{res.status_code} / {res.text}"
            else:
                result_box["res"] = res.json()
        except requests.exceptions.RequestException as e:
            result_box["err"] = str(e)

    api_job_queue.put(_task)

    # 최대 5초 대기
    start = time.time()
    while result_box["res"] is None and result_box["err"] is None and time.time() - start < 5:
        time.sleep(0.05)

    return result_box["res"], result_box["err"]
        
def enqueue_api_call(func):
    api_job_queue.put(func)   

TRADING_CUTOFF = 14*3600 + 30*60      # 오후 2시 30분
AUTO_LIQUIDATE = 14*3600 + 31*60      # 오후 2시 31분
interest_count = len(user_interest_stock_codes) if "user_interest_stock_codes" in globals() else 50

HTS_SYNC_INTERVAL = 10 + (min(interest_count, 100) - 1) // 10 * 5

state_lock = threading.Lock()         # 데이터 보호용 락
log_lock   = threading.Lock()

last_log_time_map = defaultdict(lambda: 0)
gap_log_time_map     = defaultdict(int)           # 시가갭 로그 시간 전용
last_3min_index_map  = defaultdict(lambda: -1)
last_ask_log_time_map = defaultdict(lambda: 0)
strategy_log_time_map = defaultdict(float)

# 종목명 매핑, 관심종목 목록
stock_name_map = {}
interest_stocks = []
체결확인 = False
호가확인_map = defaultdict(bool)
# 1분봉 데이터
candle_1min_map = defaultdict(lambda: deque())
minute_tracker_map = {}
cur_open_map = {}
cur_high_map = {}
cur_low_map = {}
cur_volume_map = {}
warmup_done_map = defaultdict(bool)
warmup_start_time_map = defaultdict(float)  # 실시간 틱 수신 시작 시각
last_price_map = {}
acml_vol_map = defaultdict(int)

# 체결강도/체결량
cttr_1s_map = defaultdict(lambda: deque(maxlen=3))
buy_volume_3s_map = defaultdict(lambda: deque(maxlen=6))
sell_volume_3s_map = defaultdict(lambda: deque(maxlen=6))
total_volume_3s_map = defaultdict(lambda: deque(maxlen=6))

# 호가 잔량 관련 변수
bid_ho_map = defaultdict(lambda: deque(maxlen=4))
ask_ho_map = defaultdict(lambda: deque(maxlen=4))
bidp_rsqn1_map = defaultdict(int)
askp_rsqn1_map = defaultdict(int)
bidp_rsqn3_map = defaultdict(int)
askp_rsqn3_map = defaultdict(int)

# 당일 시가
day_open_price_map = {}

# 호가 보정용 이전 값 저장
last_ask_price_map = defaultdict(            # 기본값: bid1~5 / ask1~5 모두 0
    lambda: {**{f"bid{i}": 0 for i in range(1, 6)},
             **{f"ask{i}": 0 for i in range(1, 6)}}
)

# WebSocket 인스턴스
ws_instance = None
ws_send_lock  = threading.Lock()        # 동시 전송 차단용
ws_send_times = deque(maxlen=5)         # 최근 5건 전송 시각

def ws_safe_send(msg: str):
    """
    모든 ws.send() 대신 호출.
    - 동시 전송을 한 쓰레드로 직렬화
    - 최근 1초 전송이 5건을 넘지 않도록 자동 대기
    """
    while True:
        with ws_send_lock:
            now = time.time()
            while ws_send_times and now - ws_send_times[0] >= 1:
                ws_send_times.popleft()
            if len(ws_send_times) < 5:
                ws_instance.send(msg)
                ws_send_times.append(now)
                return
        time.sleep(0.05)   # 50 ms 후 재시도
# ---------------------------------------------
approval_key = None
subscribed_codes = set()
exec_subscribed = False  # 체결통보 구독 중복 방지용
pending_subs = set()
# 틱 순매수 정확 계산용 (1분 내 필터링)
tick_net_count_time_map = defaultdict(lambda: deque())

# 3틱봉 구성용
tick_3_count_map = defaultdict(int)
tick_3_price_list_map = defaultdict(list)
tick_3_volume_list_map = defaultdict(list)
candle_3tick_map = defaultdict(lambda: deque(maxlen=20))

# 3분봉 구성용
candle_3min_temp_map = defaultdict(list)
candle_3min_map = defaultdict(lambda: deque(maxlen=30))

# VWAP 유지 시간 추적용
vwap_check_start_time_map = defaultdict(float)

# 추가 지표 계산용
vwap_price_volume_map = defaultdict(float)
vwap_volume_map = defaultdict(float)

# 볼린저 밴드(20)용 종가 리스트
close_1min_20_map = defaultdict(lambda: deque(maxlen=20))
close_3min_20_map = defaultdict(lambda: deque(maxlen=20))
close_3tick_20_map = defaultdict(lambda: deque(maxlen=20))

# RSI(14)
rsi_14_1min_map = defaultdict(dict)
rsi_14_3min_map = defaultdict(dict)

rsi_14_3tick_map = defaultdict(dict)
# ───────── 추가: 기존 now→prev 이동 래퍼 ─────────
def _set_rsi(map_obj, tr_key, new_val):
    """map_obj[tr_key]['prev'] ← 직전 now,  map_obj[tr_key]['now'] ← new_val"""
    prev = map_obj[tr_key].get("now")
    if prev is not None:
        map_obj[tr_key]["prev"] = prev
    map_obj[tr_key]["now"] = new_val
# ───────────────────────────────────────────────
# ───────── strategy_11용 1‑분봉 지표 스냅샷 ─────────
def snapshot_row_for_strategy11(tr_key):
    """
    최근 1분봉 100개를 바탕으로 log_entry_start()와 동일 지표 35종을 계산하여
    dict 로 반환한다. strategy_11 이 실시간으로 조건을 평가할 때 사용된다.
    """
    import math, pandas as _pd
    if len(candle_1min_map[tr_key]) == 0:
        return {}

    df = _pd.DataFrame(list(candle_1min_map[tr_key])[-100:])
    close = df["close"].astype(float)
    high  = df["high"].astype(float)
    low   = df["low"].astype(float)
    vol   = df["volume"].astype(float)
    open  = df["open"].astype(float)

    from ta.trend import EMAIndicator, SMAIndicator, MACD, CCIIndicator, ADXIndicator, PSARIndicator
    from ta.momentum import RSIIndicator, TSIIndicator, StochasticOscillator, ROCIndicator, WilliamsRIndicator
    from ta.volatility import BollingerBands, AverageTrueRange
    from ta.volume import OnBalanceVolumeIndicator, ForceIndexIndicator, ChaikinMoneyFlowIndicator, AccDistIndexIndicator
    try: from ta.momentum import CMOIndicator
    except ImportError:
        class CMOIndicator:
            def __init__(self, c, window=14):
                up  = c.diff().clip(lower=0).rolling(window).sum()
                dn  = (-c.diff().clip(upper=0)).rolling(window).sum()
                self._cmo = 100*(up-dn)/(up+dn)
            def cmo(self): return self._cmo
    try: from ta.volume import MoneyFlowIndexIndicator
    except ImportError:
        class MoneyFlowIndexIndicator:
            def __init__(self,h,l,c,v,w=14):
                tp=(h+l+c)/3; rmf=tp*v; diff=tp.diff()
                pmf=_pd.Series.where(diff>0,rmf,0).rolling(w).sum()
                nmf=_pd.Series.where(diff<0,-rmf,0).rolling(w).sum()
                self._mfi=100-(100/(1+pmf/nmf))
            def money_flow_index(self): return self._mfi

    def _safe(fn):
        try: return fn()
        except Exception: return math.nan

    bb   = _safe(lambda: BollingerBands(close,20,2))
    sto  = _safe(lambda: StochasticOscillator(high,low,close))
    macd = _safe(lambda: MACD(close,26,12,9))
    adx  = _safe(lambda: ADXIndicator(high,low,close))

    row = {
        "close"      : close.iloc[-1],
        "RSI"        : _safe(lambda: RSIIndicator(close,14).rsi().iloc[-1]),
        "RSI_7"      : _safe(lambda: RSIIndicator(close,7).rsi().iloc[-1]),
        "EMA_5"      : _safe(lambda: EMAIndicator(close,5).ema_indicator().iloc[-1]),
        "EMA20"      : _safe(lambda: EMAIndicator(close,20).ema_indicator().iloc[-1]),
        "SMA30"      : _safe(lambda: SMAIndicator(close,30).sma_indicator().iloc[-1]),
        "ATR"        : _safe(lambda: AverageTrueRange(high,low,close,14).average_true_range().iloc[-1]),
        "Stoch_K"    : sto.stoch().iloc[-1]          if isinstance(sto, StochasticOscillator) else math.nan,
        "Stoch_D"    : sto.stoch_signal().iloc[-1]   if isinstance(sto, StochasticOscillator) else math.nan,
        "MACD"       : macd.macd().iloc[-1]          if isinstance(macd, MACD) else math.nan,
        "MACD_signal": macd.macd_signal().iloc[-1]   if isinstance(macd, MACD) else math.nan,
        "CCI"        : _safe(lambda: CCIIndicator(high,low,close,20).cci().iloc[-1]),
        "ROC"        : _safe(lambda: ROCIndicator(close,10).roc().iloc[-1]),
        "TSI"        : _safe(lambda: TSIIndicator(close).tsi().iloc[-1]),
        "WilliamsR"  : _safe(lambda: WilliamsRIndicator(high,low,close,14).williams_r().iloc[-1]),
        "ADX"        : adx.adx().iloc[-1] if isinstance(adx, ADXIndicator) and len(close) >= 27 and not math.isnan(adx.adx().iloc[-1]) else math.nan,
        "plusDI"     : adx.adx_pos().iloc[-1] if isinstance(adx, ADXIndicator) and len(close) >= 27 and not math.isnan(adx.adx_pos().iloc[-1]) else math.nan,
        "minusDI"    : adx.adx_neg().iloc[-1] if isinstance(adx, ADXIndicator) and len(close) >= 27 and not math.isnan(adx.adx_neg().iloc[-1]) else math.nan,
        "CMO"        : _safe(lambda: CMOIndicator(close).cmo().iloc[-1]),
        "PSAR"       : _safe(lambda: PSARIndicator(high,low,close).psar().iloc[-1]),
        "OBV"        : _safe(lambda: OnBalanceVolumeIndicator(close,vol).on_balance_volume().iloc[-1]),
        "MFI"        : _safe(lambda: MoneyFlowIndexIndicator(high,low,close,vol).money_flow_index().iloc[-1]),
        "ForceIndex" : _safe(lambda: ForceIndexIndicator(close,vol).force_index().iloc[-1]),
        "CMF"        : _safe(lambda: ChaikinMoneyFlowIndicator(high,low,close,vol).chaikin_money_flow().iloc[-1]),
        "AD_Line"    : _safe(lambda: AccDistIndexIndicator(high,low,close,vol).acc_dist_index().iloc[-1]),
        "FlashReversal" : _safe(lambda: max(0, (close.iloc[-1] - open.iloc[-1]) / (high.iloc[-1] - low.iloc[-1])) if high.iloc[-1] > low.iloc[-1] else 0),
        "BB_Width"   : _safe(lambda: (bb.bollinger_hband().iloc[-1] - bb.bollinger_lband().iloc[-1]) / bb.bollinger_mavg().iloc[-1]) if isinstance(bb, BollingerBands) else math.nan,
        "PercentB"   : _safe(lambda: (close.iloc[-1] - bb.bollinger_lband().iloc[-1]) / (bb.bollinger_hband().iloc[-1] - bb.bollinger_lband().iloc[-1])) if isinstance(bb, BollingerBands) else math.nan,
        "HA_Close"   : _safe(lambda: (df["open"] + df["high"] + df["low"] + df["close"]).iloc[-1] / 4),
        "VFI"        : _safe(lambda: (((high + low + close) / 3 * vol * ((high + low + close) / 3).diff().apply(lambda x: 1 if x > 0 else (-1 if x < 0 else 0))).rolling(14).sum() / vol.rolling(14).sum()).iloc[-1]),
        "Volume_Osc": _safe(lambda: (vol.iloc[-1] - vol[-10:].mean()) / vol[-10:].mean() if vol[-10:].mean() else 0)
    }

    bid1 = last_ask_price_map[tr_key].get("bid1", 0)
    ask1 = last_ask_price_map[tr_key].get("ask1", 0)
    bidv = bidp_rsqn1_map[tr_key];  askv = askp_rsqn1_map[tr_key]
    row["BidAskSpread"] = ask1 - bid1 if ask1 and bid1 else math.nan
    row["BidAskRatio"]  = bidv / askv if askv else math.nan
    row["OrderBookDivIdx"] = (bidv - askv) / (bidv + askv) if (bidv + askv) else math.nan

    return row
# ───────────────────────────────────────────────────

# 20MA (1분봉/3분봉용)
ma_20_1min_map = defaultdict(float)
ma_30_1min_map = defaultdict(float)
ma_20_3min_map = defaultdict(float)

ma_20_3tick_map = defaultdict(float)

# 3틱 단위 종가 리스트
close_3tick_map = defaultdict(lambda: deque(maxlen=50))

# 3틱봉 거래량
volume_3tick_map = defaultdict(lambda: deque(maxlen=20))
obv_map = defaultdict(lambda: deque(maxlen=10))

# 최근 1분 최고가
high_1min_map = defaultdict(lambda: deque(maxlen=1))

# 체결시간 트래킹 (30초 체결건수 계산용)
tick_time_list_map = defaultdict(lambda: deque(maxlen=100))

# 틱 수급 (1분 단위 순매수틱 계산용)
tick_net_count_map = defaultdict(lambda: deque(maxlen=60))

# 3틱 기준 10분 최고가/최저가 트래킹
high_200tick_map = defaultdict(lambda: deque(maxlen=200))
low_200tick_map = defaultdict(lambda: deque(maxlen=200))

tick_surge_flag_map = defaultdict(bool)
vwap_hold_flag_map = defaultdict(bool)
verify_done_map = defaultdict(bool)
last_finalized_1min_map = {}

prev_close_price_map = {}

position_map = defaultdict(dict)
symbol_locks = defaultdict(threading.Lock)
# [추가] 전략 실행을 종목별로 직렬화하는 래퍼
def _run_strategy_safe(strategy_fn, tr_key):
    """
    같은 종목(tr_key)에 대해 동시에 여러 전략이 들어오는 경우를 방지한다.
    • 반드시 symbol_locks[tr_key]로 잠궈서 한 번에 하나의 전략만 통과
    """
    with symbol_locks[tr_key]:
        strategy_fn(tr_key)
initial_load_queue = Queue()
mfe_mae_track_map = defaultdict(dict)
current_position_code = None
order_no_map = {}
strategy_status_map = defaultdict(lambda: {"s1": None, "s2": None, "s3": None, "s4": None, "s5": None})

api_job_queue = SimpleQueue()
strategy_queue = Queue()
subscribe_job_queue = Queue()
# ----------------------------------
# [설정] kis_devlp.yaml 로드
# ----------------------------------
with open("kis_devlp.yaml", "r", encoding="utf-8") as f:
    config = yaml.safe_load(f)

HTS_ID = config["my_userid"]      # ← 추가
APP_KEY = config["my_app"]
APP_SECRET = config["my_sec"]
REAL_DOMAIN = config["prod"]
WS_URL = "ws://ops.koreainvestment.com:21000"

def make_hash(body: dict) -> str:
    """
    주문·정정·취소 API 호출용 해시키를 즉시(동기) 생성한다.
    • call_api() / api_job_queue 를 사용하지 않아 TPS 워커와의
      중첩 교착이 발생하지 않는다.
    • 오류 시 빈 문자열("")을 반환하여 상위 로직이 그대로
      예외를 처리하도록 한다.
    """
    url = f"{REAL_DOMAIN}/uapi/hashkey"
    headers = {
        "Content-Type": "application/json; charset=utf-8",
        "appkey":  APP_KEY,
        "appsecret": APP_SECRET
    }
    try:
        resp = requests.post(url, headers=headers, json=body, timeout=3)
        resp.raise_for_status()               # HTTP 오류 발생 시 예외
        data = resp.json()
        return data.get("HASH", "")
    except Exception as e:
        print(f"[ERROR] hashkey 생성 실패: {e}")
        return ""

def get_tick_unit(price: int) -> int:
    if price < 1_000:      return 1
    if price < 5_000:      return 5
    if price < 10_000:     return 10
    if price < 50_000:     return 50
    if price < 100_000:    return 100
    return 500
    
# 체결 TR / 호가 TR
TR_ID_TICK = "H0STCNT0"   # 체결
TR_ID_ASK = "H0STASP0"    # 호가

# ----------------------------------
# [토큰 발급]
# ----------------------------------
def get_access_token():
    token_path = "access_token.json"
    url = "https://openapi.koreainvestment.com:9443/oauth2/tokenP"
    headers = {"content-type": "application/json; charset=UTF-8"}
    body = {
        "grant_type": "client_credentials",
        "appkey": APP_KEY,
        "appsecret": APP_SECRET
    }

    def request_token():
        try:
            data, err = call_api("POST", url, headers=headers, json_body=body)
            if err:
                print(f"[ERROR] access_token 요청 실패: {err}")
                raise Exception(err)
            access_token = data["access_token"]
            expires_in = data["expires_in"]
            expires_at = time.time() + int(expires_in)
            with open(token_path, "w", encoding="utf-8") as f:
                json.dump({"access_token": access_token, "expires_at": expires_at}, f)
            os.chmod(token_path, 0o600)
            return access_token
        except Exception as e:
            print(f"[ERROR] access_token 요청 실패: {e}")
            raise

    # JSON 파일이 존재하면 토큰 유효성 검사
    if os.path.exists(token_path):
        try:
            with open(token_path, "r", encoding="utf-8") as f:
                data = json.load(f)
                access_token = data.get("access_token")
                expires_at = data.get("expires_at")

                # ✅ 만료 임박 또는 이상치 → 재발급
                if not access_token or not expires_at or time.time() >= float(expires_at) - 60:
                    return request_token()
                return access_token
        except Exception as e:
            print(f"[WARN] access_token 파일 불러오기 실패: {e}")

    # 파일이 없거나 실패 → 재발급
    return request_token()

def restore_position_from_balance():
    """
    1) 잔고 조회(계좌 보유 종목)
    2) position_map 에 포지션 등록
    3) 전략 ID 는 last_position.json 로부터 이어받기
       (없으면 0 으로 두고, 실시간 구독만 걸어 둠)
    """
    url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/trading/inquire-balance"
    headers = {
        "Content-Type":  "application/json; charset=utf-8",
        "authorization": f"Bearer {get_access_token()}",
        "appkey":        APP_KEY,
        "appsecret":     APP_SECRET,
        "tr_id":         "TTTC8434R",
        "custtype":      "P"
    }
    params = {
        "CANO":             config["my_acct"],
        "ACNT_PRDT_CD":     config["my_prod"],
        "AFHR_FLPR_YN":     "N",
        "OFL_YN":           "",
        "INQR_DVSN":        "02",
        "UNPR_DVSN":        "01",
        "FUND_STTL_ICLD_YN":"N",
        "FNCG_AMT_AUTO_RDPT_YN":"N",
        "PRCS_DVSN":        "00",
        "CTX_AREA_FK100":   "",
        "CTX_AREA_NK100":   ""
    }

    try:
        data, err = call_api("GET", url, headers=headers, params=params)
        if err:
            print(f"[ERROR] 잔고 조회 실패: {err}")
            return

        restored_any = False
        for item in data.get("output1", []):
            # 안전한 형 변환 -------------------------------------------------
            def _to_int(x: str) -> int:
                return int(float(x.replace(",", ""))) if x else 0

            code       = item.get("pdno")
            qty        = _to_int(item.get("hldg_qty", "0"))
            avg_price  = float(item.get("pchs_avg_pric", "0").replace(",", "")) if item.get("pchs_avg_pric") else 0.0
            # ----------------------------------------------------------------

            if qty <= 0 or not code:
                continue

            position_map[code] = {
                "entry_price": avg_price,
                "entry_time":  time.time(),
                "strategy_id": 0,          # 뒤에서 별도 복원
                "qty":         qty
            }
            # ────── 복원 포지션용 초기 값 세팅 ──────
            last_price_map[code] = avg_price          # 현재가 초기화
            mfe_mae_track_map[code] = {
                "start_time": time.time(),
                "max_price":  avg_price,
                "min_price":  avg_price
            }
            log_entry_start(                       # 전략 ID 0 = 복원
                tr_key=code,
                strategy_name="0",
                entry_price=avg_price,
                candle={"open": avg_price, "high": avg_price,
                        "low": avg_price,  "close": avg_price, "volume": 0},
                rsi=0, sma30=0,
                volume_now=0, volume_10_avg=0,
                cttr=0, tick_net=0, tick_speed=0,
                bid1=0, ask1=0, bid_vol=0, ask_vol=0
            )
            # ───────────────────────────────────────
            restored_any = True
            print(f"[복원] {code} | 수량:{qty} | 평균단가:{avg_price}")

            # 실시간 데이터 없으면 구독 등록
            if code not in interest_stocks:
                add_stock_realtime(code, stock_name_map.get(code, code))

        if not restored_any:
            print("[복원] 조회된 보유 종목이 없습니다.")

    except Exception as e:
        print(f"[ERROR] 잔고 기반 복원 실패: {e}")
        return

    # ───────────────── 전략 ID 이어붙이기 ─────────────────
    try:
        with open("last_position.json", "r", encoding="utf-8") as f:
            items = json.load(f)
            for item in items:
                code = item.get("code")
                strategy = item.get("strategy")
                if code in position_map and strategy is not None:
                    position_map[code]["strategy_id"] = strategy
                    print(f"[복원] {code} → 전략 {strategy} 로 이어받음")
    except FileNotFoundError:
        pass
    except Exception as e:
        print(f"[경고] 전략 복원 실패: {e}")
    for code in position_map:
        position_map[code]["_need_monitor"] = True

# ───────────────────────────────────────────
# [NEW]  하루 한 번 08:50쯤 전날 데이터 싹 비우기
# ───────────────────────────────────────────
def perform_daily_reset():
    global 체결확인
    """
    • 전일 캔들·지표 deque 비우고
    • 체결확인 / 호가확인 플래그 초기화
    • 관심종목·포지션은 그대로 두되,
      09:00 장시작 직전에 1분봉 선로딩 다시 걸어 줌
    """
    print("\n🔄 [Daily-Reset] 전일 데이터 초기화 시작\n")

    # 1) 실시간용 캐시/지도 다 비움  (position_map 제외!)
    for m in [
        candle_1min_map, candle_3min_map, candle_3tick_map,
        close_1min_20_map, close_3min_20_map, close_3tick_20_map,
        cttr_1s_map, buy_volume_3s_map, sell_volume_3s_map,
        total_volume_3s_map, tick_time_list_map, tick_net_count_time_map,
        ma_20_1min_map, ma_20_3min_map, ma_20_3tick_map,
        rsi_14_1min_map, rsi_14_3min_map, rsi_14_3tick_map,
        bid_ho_map, ask_ho_map, last_ask_price_map,
        bidp_rsqn1_map, askp_rsqn1_map, bidp_rsqn3_map, askp_rsqn3_map,
        vwap_price_volume_map, vwap_volume_map,
        minute_tracker_map, cur_open_map, cur_high_map, cur_low_map,
        cur_volume_map, last_price_map, high_1min_map,
        high_200tick_map, low_200tick_map, volume_3tick_map
    ]:
        m.clear()

    체결확인_map.clear() if '체결확인_map' in globals() else None
    체결확인 = False
    호가확인_map.clear()

    # 2) 09:00 직후 새로운 1 분봉 불러오도록 큐 재등록
    for c in list(interest_stocks):
        initial_load_queue.put(c)

    # 3) 포지션 살아있으면 잔고 다시 싱크
    restore_position_from_balance()

    _held_cache.clear()
    print("✅ [Daily-Reset] 초기화 완료 ─ 09:00부터 새 데이터 수집\n")


def daily_reset_worker():
    """날짜가 바뀌면 08:50쯤 perform_daily_reset() 한 번 호출"""
    last_seen = datetime.date.today()
    while True:
        now = datetime.datetime.now()
        if now.date() != last_seen and now.hour == 8 and now.minute >= 50:
            perform_daily_reset()
            last_seen = now.date()
        time.sleep(30)      # 30 초 간격 체크
        
def save_positions():
    """현재 position_map을 last_position.json에 저장"""
    with state_lock:
        items = [
            {"code": c, "strategy": d.get("strategy_id", 0), "qty": d.get("qty", 0)}
            for c, d in position_map.items()
        ]
    with open("last_position.json", "w", encoding="utf-8") as f:
        json.dump(items, f, ensure_ascii=False)
        
def is_stock_held(tr_key: str) -> bool:
    """
    현재 계좌에서 해당 종목을 실시간으로 보유 중인지 여부를 확인합니다.
    True = 보유 중 / False = 미보유
    """
    url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/trading/inquire-balance"
    headers = {
        "Content-Type": "application/json; charset=utf-8",
        "authorization": f"Bearer {get_access_token()}",
        "appkey": APP_KEY,
        "appsecret": APP_SECRET,
        "tr_id": "TTTC8434R",
        "custtype": "P"
    }
    body = {
        "ACNT_PWD": config["my_pwd"],
        "CANO": config["my_acct"],
        "ACNT_PRDT_CD": config["my_prod"],
        "AFHR_FLPR_YN": "N",
        "OFL_YN": "",
        "INQR_DVSN": "02",
        "UNPR_DVSN": "01",
        "FUND_STTL_ICLD_YN": "N",
        "FNCG_AMT_AUTO_RDPT_YN": "N",
        "PRCS_DVSN": "00",
        "CTX_AREA_FK100": "",
        "CTX_AREA_NK100": ""
    }

    try:
        res = requests.post(url, headers=headers, json=body, timeout=5)
        res.raise_for_status()
        data = res.json()
        items = data.get("output1", [])
        for item in items:
            code = item.get("pdno")
            qty = int(item.get("hldg_qty", "0").replace(",", ""))
            if code == tr_key and qty > 0:
                return True
        return False
    except Exception as e:
        print(f"[ERROR] 실시간 보유확인 실패: {e}")
        return False

_held_cache = {}  # 종목별 잔고 확인 캐시

def is_stock_held_cached(tr_key: str, ttl=5) -> bool:
    now = time.time()
    hit = _held_cache.get(tr_key)
    if hit and now - hit["ts"] < ttl:
        return hit["val"]
    val = is_stock_held(tr_key)
    _held_cache[tr_key] = {"val": val, "ts": now}
    return val
    
def auto_liquidate_all():
    with state_lock:
        codes = list(position_map.keys())

    for code in codes:
        qty = position_map[code].get("qty", 1)
        print(f"[일괄청산] 14:31 트리거 → {code}")
        submit_sell_order(code, qty)
        with state_lock:
            position_map.pop(code, None)
            
    _held_cache.clear() 
    print("[일괄청산] 완료")
        
def schedule_liquidation():
    now = time.localtime()
    now_sec = now.tm_hour * 3600 + now.tm_min * 60 + now.tm_sec
    delay = max(0, AUTO_LIQUIDATE - now_sec)
    threading.Timer(delay, auto_liquidate_all).start()

def get_balance_amount():
    """
    계좌 주문가능 현금 조회 (GET 방식)
    • POST+body 로 보내면 OPSQ2001 오류가 난다.
    • 오류·예외 시 0 반환 → 상위 로직이 주문을 건너뛴다.
    """
    url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/trading/inquire-psbl-order"
    params = {
        "CANO": config["my_acct"],
        "ACNT_PRDT_CD": config["my_prod"],
        "PDNO": "005930",          # 더미 종목
        "ORD_UNPR": "0",
        "ORD_DVSN": "01",
        "CMA_EVLU_AMT_ICLD_YN": "N",
        "OVRS_ICLD_YN": "N"
    }
    headers = {
        "authorization": f"Bearer {get_access_token()}",
        "appkey":  APP_KEY,
        "appsecret": APP_SECRET,
        "tr_id":   "TTTC8908R",
        "custtype": "P"
    }

    data, err = call_api("GET", url, headers=headers, params=params)
    if err:
        print(f"[ERROR] 주문가능금액 요청 실패: {err}")
        return 0

    output = data.get("output")
    if not output or "ord_psbl_cash" not in output:
        print(f"[ERROR] 주문가능금액 응답 이상: {data}")
        return 0

    try:
        return int(output["ord_psbl_cash"])
    except Exception:
        print(f"[ERROR] 주문가능금액 파싱 실패: {output.get('ord_psbl_cash')}")
        return 0

def place_order_market(tr_key: str, qty: int) -> str | None:
    def _task():
        url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/trading/order-cash"
        body = {
            "CANO": config["my_acct"],
            "ACNT_PRDT_CD": config["my_prod"],
            "ACNT_PWD": config["my_pwd"],
            "PDNO": tr_key,
            "ORD_DVSN": "01",
            "ORD_QTY": str(qty),
            "ORD_UNPR": "0",
            "CTAC_TLNO": config.get("my_phone", "01000000000")
        }
        headers = {
            "Content-Type": "application/json; charset=utf-8",
            "authorization": f"Bearer {get_access_token()}",
            "appkey": APP_KEY,
            "appsecret": APP_SECRET,
            "tr_id": "TTTC0012U",
            "custtype": "P",
            "hashkey": make_hash(body)
        }
        try:
            res = requests.post(url, headers=headers, json=body)
            data = res.json()
            if "output" in data and ("ODNO" in data["output"] or "odno" in data["output"]):
                ord_no = data["output"].get("ODNO") or data["output"].get("odno")
                price = last_price_map.get(tr_key, 0)
                print(f"[시장가 매수] {tr_key} | 수량:{qty} | 진입가: {price}")
                print("[응답]", res.status_code, res.text)
                return ord_no
            else:
                print(f"[ERROR] 시장가 매수 실패 | msg: {data.get('msg1')} | code: {data.get('rt_cd')}")
                print("[응답 원문]", res.status_code, res.text)
                return None
        except Exception as e:
            print(f"[ERROR] 시장가 매수 요청 실패: {e}")
            return None

    result_box = {"ord_no": None}
    def wrapped():
        result_box["ord_no"] = _task()
    api_job_queue.put(wrapped)

    # --- 결과 대기 (최대 5초) ---
    start_ts = time.time()
    while result_box["ord_no"] is None and time.time() - start_ts < 5:
        time.sleep(0.05)

    return result_box["ord_no"]  # None 또는 체결번호

# ────────────────────────────────────────────────────────────────
# [교체] log_entry_start() – 고급 지표 35종 포함 완전판
# ────────────────────────────────────────────────────────────────
def log_entry_start(
    tr_key, strategy_name, entry_price, candle, rsi, sma30, volume_now,
    volume_10_avg, cttr, tick_net, tick_speed, bid1, ask1, bid_vol, ask_vol
):
    import os, csv, math, datetime as _dt, pandas as _pd
    # ───── 중복 로그 방지: 같은 종목+시각 이미 있으면 저장 건너뜀 ─────
    fname = f"logs/{strategy_name}전략_{_dt.datetime.now().strftime('%Y%m%d')}.csv"
    entry_time_str = _dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    if os.path.exists(fname):
        with log_lock:
            with open(fname, newline="", encoding="utf-8") as f:
                for row in csv.DictReader(f):
                    if row.get("종목코드") == tr_key and row.get("진입 시각") == entry_time_str:
                        print(f"[중복차단] 이미 동일 종목+시각의 로그가 존재 → 저장 생략: {tr_key}")
                        return
    df = _pd.DataFrame(list(candle_1min_map[tr_key])[-100:] or [candle])
    
    close_ser = df["close"].astype(float)
    high_ser  = df["high"].astype(float)
    low_ser   = df["low"].astype(float)
    vol_ser   = df["volume"].astype(float)
    if len(df) < 20:
        # ✅ 데이터 부족해도 로그는 남기고, 일부 지표만 공란 처리
        print(f"[경고] {tr_key} 1분봉 데이터 {len(df)}개 → 지표 누락 가능성 있음")
    for col in ("open", "high", "low", "close", "volume"):
        if col not in df.columns:
            df[col] = candle[col]
    # ─ (2) 거래량·MFI·Volume Spike ─
    try:
        vol_now    = vol_ser.iloc[-1]
        vol_10_avg = vol_ser[-10:].mean()
        row_mfi    = MoneyFlowIndexIndicator(
            high=high_ser, low=low_ser,
            close=close_ser, volume=vol_ser
        ).money_flow_index().iloc[-1]
        row_vosc   = (vol_now - vol_10_avg) / vol_10_avg if vol_10_avg else 0
        row_spi    = row_vosc * 100
    except Exception:
        row_mfi  = math.nan
        row_vosc = math.nan
        row_spi  = math.nan
    close_ser = df["close"].astype(float)
    high_ser  = df["high"].astype(float)
    low_ser   = df["low"].astype(float)
    vol_ser   = df["volume"].astype(float)

    # ─ (2) 지표 라이브러리 ─
    from ta.trend     import EMAIndicator, SMAIndicator, MACD, CCIIndicator, ADXIndicator, PSARIndicator
    from ta.momentum  import RSIIndicator, TSIIndicator, StochasticOscillator, ROCIndicator, WilliamsRIndicator
    from ta.volatility import BollingerBands, AverageTrueRange
    from ta.volume     import OnBalanceVolumeIndicator, ForceIndexIndicator, ChaikinMoneyFlowIndicator, AccDistIndexIndicator
    # CMO, MFI 폴백
    try: from ta.momentum import CMOIndicator
    except ImportError:
        class CMOIndicator:
            def __init__(self, close, window=14): up=close.diff().clip(lower=0).rolling(window).sum(); dn=(-close.diff().clip(upper=0)).rolling(window).sum(); self._cmo=100*(up-dn)/(up+dn)
            def cmo(self): return self._cmo
    try: from ta.volume import MoneyFlowIndexIndicator
    except ImportError:
        class MoneyFlowIndexIndicator:
            def __init__(self, h,l,c,v,window=14): tp=(h+l+c)/3; rmf=tp*v; diff=tp.diff(); pmf=_pd.Series.where(diff>0,rmf,0).rolling(window).sum(); nmf=_pd.Series.where(diff<0,-rmf,0).rolling(window).sum(); self._mfi=100-(100/(1+pmf/nmf))
            def money_flow_index(self): return self._mfi

    # ─ (3) 지표 계산 ─
    def _safe(fn):  # 간단 래퍼
        try: return fn()
        except: return ""
    rsi7   = _safe(lambda: RSIIndicator(close_ser,7).rsi().iloc[-1])
    ema5   = _safe(lambda: EMAIndicator(close_ser,5).ema_indicator().iloc[-1])
    ema20  = _safe(lambda: EMAIndicator(close_ser,20).ema_indicator().iloc[-1])
    bb_obj = _safe(lambda: BollingerBands(close_ser,20,2))
    bb_w   = (bb_obj.bollinger_hband().iloc[-1]-bb_obj.bollinger_lband().iloc[-1])/bb_obj.bollinger_mavg().iloc[-1] if bb_obj!="" else ""
    pct_b  = (close_ser.iloc[-1]-bb_obj.bollinger_lband().iloc[-1])/(bb_obj.bollinger_hband().iloc[-1]-bb_obj.bollinger_lband().iloc[-1]) if bb_obj!="" else ""
    atr    = _safe(lambda: AverageTrueRange(high_ser,low_ser,close_ser,14).average_true_range().iloc[-1])
    sto    = _safe(lambda: StochasticOscillator(high_ser,low_ser,close_ser))
    stoch_k= sto.stoch().iloc[-1] if sto!="" else ""; stoch_d=sto.stoch_signal().iloc[-1] if sto!="" else ""
    supert = _safe(lambda: ((high_ser+low_ser)/2+3*AverageTrueRange(high_ser,low_ser,close_ser,10).average_true_range()).iloc[-1])
    vol_spi= (volume_now-volume_10_avg)/volume_10_avg*100 if volume_10_avg else ""
    macd_o = _safe(lambda: MACD(close_ser,26,12,9))
    macd_v = macd_o.macd().iloc[-1] if macd_o!="" else ""; macd_s=macd_o.macd_signal().iloc[-1] if macd_o!="" else ""
    momentum=_safe(lambda: close_ser.iloc[-1]-close_ser.iloc[-2])
    roc    = _safe(lambda: ROCIndicator(close_ser,10).roc().iloc[-1])
    tsi    = _safe(lambda: TSIIndicator(close_ser).tsi().iloc[-1])
    willr  = _safe(lambda: WilliamsRIndicator(high_ser,low_ser,close_ser,14).williams_r().iloc[-1])
    cci    = _safe(lambda: CCIIndicator(high_ser,low_ser,close_ser,20).cci().iloc[-1])
    adx_o  = _safe(lambda: ADXIndicator(high_ser,low_ser,close_ser))
    adx     = adx_o.adx().iloc[-1]      if adx_o != "" and len(close_ser) >= 27 else ""
    plus_di = adx_o.adx_pos().iloc[-1]  if adx_o != "" and len(close_ser) >= 27 else ""
    minus_di= adx_o.adx_neg().iloc[-1]  if adx_o != "" and len(close_ser) >= 27 else ""
    cmo    = _safe(lambda: CMOIndicator(close_ser).cmo().iloc[-1])
    tick_vol=_safe(lambda: close_ser.diff().abs().tail(20).std())
    sma20  = _safe(lambda: SMAIndicator(close_ser,20).sma_indicator().iloc[-1])
    twap   = _safe(lambda: close_ser.tail(20).mean())
    psar   = _safe(lambda: PSARIndicator(high_ser,low_ser,close_ser).psar().iloc[-1])
    ha_cls = (df["open"]+df["high"]+df["low"]+df["close"]).iloc[-1]/4
    vfi_val= _safe(lambda:(((high_ser+low_ser+close_ser)/3*vol_ser*((high_ser+low_ser+close_ser)/3).diff().apply(lambda x:1 if x>0 else(-1 if x<0 else 0))).rolling(14).sum()/vol_ser.rolling(14).sum()).iloc[-1])
    obv    = _safe(lambda: OnBalanceVolumeIndicator(close_ser,vol_ser).on_balance_volume().iloc[-1])
    mfi    = _safe(lambda: MoneyFlowIndexIndicator(high_ser,low_ser,close_ser,vol_ser).money_flow_index().iloc[-1])
    fi     = _safe(lambda: ForceIndexIndicator(close_ser,vol_ser).force_index().iloc[-1])
    cmf    = _safe(lambda: ChaikinMoneyFlowIndicator(high_ser,low_ser,close_ser,vol_ser).chaikin_money_flow().iloc[-1])
    adl    = _safe(lambda: AccDistIndexIndicator(high_ser,low_ser,close_ser,vol_ser).acc_dist_index().iloc[-1])
    try:
        vol_osc = (volume_now - volume_10_avg) / volume_10_avg if volume_10_avg else ""
    except:
        vol_osc = ""
    try:
        bidask_ratio = math.log(bid_vol / ask_vol) if ask_vol and bid_vol > 0 else ""
    except:
        bidask_ratio = ""
    try:
        md_ratio = math.log(bidp_rsqn3_map[tr_key] / askp_rsqn3_map[tr_key]) if askp_rsqn3_map[tr_key] and bidp_rsqn3_map[tr_key] > 0 else ""
    except:
        md_ratio = ""
    try:
        spread_sq = ((ask1 - bid1) / entry_price * 100) if bid1 and ask1 else ""
    except:
        spread_sq = ""
    try:
        if candle["high"] <= candle["low"]:
            flash_rev = 0
        else:
            raw_val = (candle["close"] - candle["open"]) / (candle["high"] - candle["low"])
            flash_rev = max(0, raw_val)
    except Exception:
        flash_rev = ""
    try:
        ob_div = round((bid_vol - ask_vol) / (bid_vol + ask_vol), 6) if (bid_vol + ask_vol) else ""
    except:
        ob_div = ""

    # ─ (4) CSV 라인 생성 ─
    date_str = _dt.datetime.now().strftime("%Y%m%d")
    fname    = f"logs/{strategy_name}전략_{date_str}.csv"; os.makedirs("logs", exist_ok=True)
    row = {
        "전략 이름":strategy_name,"종목코드":tr_key,"종목명":stock_name_map.get(tr_key,tr_key),
        "진입 시각":_dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S"),"진입가":entry_price,
        "청산 시각":"","청산가":"","종료 사유":"",
        "시가":candle["open"],"고가":candle["high"],"저가":candle["low"],"종가":candle["close"],
        "RSI":round(rsi,2) if rsi else "","RSI_7":round(rsi7,2) if rsi7!="" else "",
        "SMA30":int(sma30) if isinstance(sma30,(int,float)) and math.isfinite(sma30) else "",
        "EMA_5":round(ema5,2) if ema5!="" else "","SuperTrend":round(supert,2) if supert!="" else "",
        "Stoch_K":round(stoch_k,2) if stoch_k!="" else "","Stoch_D":round(stoch_d,2) if stoch_d!="" else "",
        "BB_Width":round(bb_w,4) if bb_w!="" else "","ATR":round(atr,2) if atr!="" else "",
        "VWAP":round(vwap_price_volume_map[tr_key]/vwap_volume_map[tr_key],2) if vwap_volume_map[tr_key] else "",
        "Volume_Spike_Index": round(row_spi,2),
        "OrderFlowImbalance":bidp_rsqn1_map[tr_key]-askp_rsqn1_map[tr_key] if tr_key in bidp_rsqn1_map else "",
        "BidAskSpread":abs(ask1-bid1) if bid1 and ask1 else "",
        "FlashReversal":round(flash_rev,3),
        "호가 스프레드":(ask1-bid1) if bid1 and ask1 else "","체결량(3초)":total_volume_3s_map[tr_key][-1] if total_volume_3s_map[tr_key] else "",
        "현재 거래량":volume_now,"10분 평균 거래량":int(volume_10_avg),
        "체결강도":round(cttr,2),"순매수틱":tick_net,"틱속도":tick_speed,
        "매수호가1":bid1,"매도호가1":ask1,"매수호가잔량":bid_vol,"매도호가잔량":ask_vol,
        "EMA20":round(ema20,2) if ema20!="" else "","PercentB":round(pct_b,4) if pct_b!="" else "",
        "OBV":int(obv) if obv!="" and math.isfinite(obv) else "","MFI": round(row_mfi,2),
        "ForceIndex":int(fi) if fi!="" and math.isfinite(fi) else "","CMF":round(cmf,3) if cmf!="" else "",
        "AD_Line":int(adl) if adl!="" and math.isfinite(adl) else "","Volume_Osc": round(row_vosc,4),
        "BidAskRatio":round(bidask_ratio,3) if bidask_ratio!="" else "",
        "MarketDepthRatio":round(md_ratio,3) if md_ratio!="" else "",
        "SpreadSqueeze":round(spread_sq,2) if spread_sq!="" else "",
        "OrderBookDivIdx":round(ob_div,3) if ob_div!="" else "",
        # 나머지 추가·미사용 컬럼들 공란 유지
        "수익률(%)":"","MFE":"","MAE":"","3분 최고가":"계산중","3분 최저가":"계산중"
    }
    write_header = not os.path.exists(fname)
    with log_lock:
        with open(fname,"a",newline="",encoding="utf-8") as f:
            wr = csv.DictWriter(f,fieldnames=row.keys())
            if write_header: wr.writeheader()
            wr.writerow(row)

def log_entry_finish(
    tr_key: str,
    strategy_name: str,
    exit_price: float,
    reason: str,
    mfe: float | None,
    mae: float | None,
    max3: float | None,
    min3: float | None,
    entry_time: float | None = None,
    fname: str | None = None,
    candles_1min: list[dict] | None = None
) -> bool:
    import csv, os, datetime as _dt, math, pandas as pd
    try:
        from ta.volume import MoneyFlowIndexIndicator
    except ImportError:
        class MoneyFlowIndexIndicator:
            def __init__(self, high, low, close, volume, window=14):
                tp = (high + low + close) / 3
                rmf = tp * volume
                diff = tp.diff()
                pmf = pd.Series.where(diff > 0, rmf, 0).rolling(window).sum()
                nmf = pd.Series.where(diff < 0, -rmf, 0).rolling(window).sum()
                self._mfi = 100 - (100 / (1 + pmf / nmf))
            def money_flow_index(self):
                return self._mfi

    if fname is None:
        date_str = _dt.datetime.now().strftime("%Y%m%d")
        fname = f"logs/{strategy_name}전략_{date_str}.csv"
    if not os.path.exists(fname):
        return False

    entry_dt = (
        _dt.datetime.fromtimestamp(entry_time).replace(microsecond=0)
        if entry_time else None
    )
    now_str = _dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    with log_lock:
        with open(fname, newline="", encoding="utf-8") as f:
            rows = list(csv.DictReader(f))
        if not rows:
            return False

        target_idx = None
        min_diff = 9999
        for idx in reversed(range(len(rows))):
            r = rows[idx]
            if r.get("종목코드") != tr_key or r.get("청산 시각"):
                continue
            if entry_dt:
                try:
                    row_dt = _dt.datetime.strptime(r.get("진입 시각", ""), "%Y-%m-%d %H:%M:%S")
                    diff = abs((row_dt - entry_dt).total_seconds())
                except Exception:
                    diff = 9999
            else:
                diff = 0
            if diff < min_diff:
                min_diff = diff
                target_idx = idx
                if diff <= 1:
                    break
        if target_idx is None:
            with open("log_finish_debug.txt", "a", encoding="utf-8") as f:
                f.write(f"[실패] 청산 대상 못 찾음 → 종목:{tr_key}, 시각:{now_str}, 전략:{strategy_name}, entry_time: {entry_time}\n")
            return False

        row = rows[target_idx]
        row["청산 시각"] = now_str
        print(f"[디버깅] 로그 덮어쓰기 성공 → 청산 시각:{now_str}, 청산가:{exit_price}")
        row["청산가"] = f"{exit_price:.2f}"

        try:
            entry_px = float(row.get("진입가", 0))
            row["수익률(%)"] = f"{(exit_price - entry_px) / entry_px * 100:.2f}" if entry_px else ""
        except:
            row["수익률(%)"] = ""

        if reason:
            if reason == "시간청산":
                try:
                    수익률 = (exit_price - entry_px) / entry_px
                    suffix = (
                        "(익절)" if 수익률 > 0 else
                        "(손절)" if 수익률 < 0 else
                        "(본절)"
                    )
                    row["종료 사유"] = f"{reason}{suffix}"
                except:
                    row["종료 사유"] = reason
            else:
                row["종료 사유"] = reason
        else:
            try:
                수익률 = (exit_price - entry_px) / entry_px
                row["종료 사유"] = "익절" if 수익률 > 0 else "손절" if 수익률 < 0 else "본절"
            except:
                row["종료 사유"] = ""

        row["MFE"] = f"{mfe:.2f}" if mfe is not None else ""
        row["MAE"] = f"{mae:.2f}" if mae is not None else ""

        if entry_time:
            recent_prices = []
            now_ts = time.time()
            for px, ts in zip(high_200tick_map[tr_key], tick_time_list_map[tr_key]):
                if entry_time <= ts <= entry_time + 180:
                    recent_prices.append(px)
            row["3분 최고가"] = max(recent_prices) if recent_prices else ""
            row["3분 최저가"] = min(recent_prices) if recent_prices else ""

        try:
            candles = candles_1min or list(candle_1min_map.get(tr_key, []))[-20:]
            if len(candles) < 5:
                raise ValueError("캔들 부족")
            df = pd.DataFrame(candles)
            vol_now = df["volume"].iloc[-1]
            vol_10_avg = df["volume"].tail(10).mean()
            vol_spi_idx = (vol_now - vol_10_avg) / vol_10_avg * 100 if vol_10_avg else 0
            mfi_val = MoneyFlowIndexIndicator(
                high=df["high"], low=df["low"],
                close=df["close"], volume=df["volume"], window=14
            ).money_flow_index().iloc[-1]
            vol_osc = (vol_now - vol_10_avg) / vol_10_avg if vol_10_avg else 0
            row["Volume_Spike_Index"] = round(vol_spi_idx, 2)
            row["MFI"] = round(mfi_val, 2)
            row["Volume_Osc"] = round(vol_osc, 4)
        except Exception:
            row["Volume_Spike_Index"] = "0"
            row["MFI"] = "0"
            row["Volume_Osc"] = "0"

        with open(fname, "w", newline="", encoding="utf-8") as f:
            wr = csv.DictWriter(f, fieldnames=rows[0].keys())
            wr.writeheader()
            wr.writerows(rows)

        with open("log_finish_debug.txt", "a", encoding="utf-8") as f:
            f.write(f"[완료] 청산 완료 → 종목:{tr_key}, 시각:{now_str}, 전략:{strategy_name}\n")

    return True


def initial_1min_loader():
    while True:
        code = initial_load_queue.get()
        try:
            fetch_today_1min(code)
        except Exception as e:
            print(f"[초기로드 오류] {code}: {e}")
        time.sleep(0.3)  # API 요청 간격 제한
        initial_load_queue.task_done()
        
def update_3min_high_low_later(tr_key, strategy_name, entry_time):
    """
    3분 대기 후 '종목코드+진입 시각' 일치하는 행에
    3분 최고가/최저가 값을 채워넣는다.
    """
    import os, csv, datetime, time

    time.sleep(180)  # 3분 대기

    # CSV 경로 설정
    date_str = datetime.datetime.now().strftime("%Y%m%d")
    fname = f"logs/{strategy_name}전략_{date_str}.csv"
    if not os.path.exists(fname):
        return

    # 진입 시각 문자열 변환
    entry_time_str = datetime.datetime.fromtimestamp(entry_time).strftime("%Y-%m-%d %H:%M:%S")

    # 고저가 추출
    track = mfe_mae_track_map.get(tr_key, {})
    max3 = track.get("max_price", "")
    min3 = track.get("min_price", "")

    with log_lock:
        with open(fname, newline="", encoding="utf-8") as f:
            rows = list(csv.DictReader(f))
        if not rows:
            return

        # 행 수정
        for row in rows:
            if row.get("종목코드") == tr_key and row.get("진입 시각") == entry_time_str:
                if row.get("3분 최고가", "") in ("", "계산중", None):
                    row["3분 최고가"] = max3
                if row.get("3분 최저가", "") in ("", "계산중", None):
                    row["3분 최저가"] = min3
                break

        # 전체 필드 조합
        fieldnames = []
        for r in rows:
            for k in r:
                if k not in fieldnames:
                    fieldnames.append(k)

        with open(fname, "w", newline="", encoding="utf-8") as f:
            wr = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
            wr.writeheader()
            wr.writerows(rows)

def submit_order(tr_key, entry_price, strategy_id):
    volume_now = cur_volume_map.get(tr_key, 0)
    volume_10_avg = (
        sum(c["volume"] for c in list(candle_1min_map[tr_key])[-10:])
        / 10 if len(candle_1min_map[tr_key]) >= 10 else 0
    )
    # --- ⬇️ 여기부터 추가 ---
    now = time.localtime()
    now_sec = now.tm_hour * 3600 + now.tm_min * 60 + now.tm_sec
    BUY_CUTOFF = 15 * 3600          # 15:00 = 54000초
    if now_sec >= BUY_CUTOFF:
        print(f"[차단] 15:00 이후 매수 금지 → {tr_key} 진입 무시")
        return                      # ⬅️ 그냥 빠져나와 버린다
    # --- ⬆️ 여기까지 추가 ---

    qty = 1    

    bid1 = last_ask_price_map[tr_key].get("bid1", 0)
    stop = int(entry_price * SL_RATIO)

    if bid1 < stop:
        print(f"[차단] 매수1호가가 손절가보다 낮음 → {tr_key} 진입 무시")
        return
        
    # 🔥 진입 로그 자동 기록
    candle = (
        last_finalized_1min_map.get(tr_key)               # 직전 1분봉이 있으면 그것
        or {                                              # 없으면 즉시 만들기
            "open":   entry_price,
            "high":   entry_price,
            "low":    entry_price,
            "close":  entry_price,
            "volume": cur_volume_map.get(tr_key, 0)
        }
    )
    log_entry_start(
        tr_key=tr_key,
        strategy_name=str(strategy_id),
        entry_price=entry_price,
        candle=candle,
        rsi=rsi_14_1min_map[tr_key].get("now", 0),
        sma30=ma_30_1min_map.get(tr_key, 0),
        volume_now=volume_now,
        volume_10_avg=volume_10_avg,
        cttr=cttr_1s_map[tr_key][-1] if cttr_1s_map[tr_key] else 0,
        tick_net=tick_net_count_map[tr_key][-1] if tick_net_count_map[tr_key] else 0,
        tick_speed=len(tick_time_list_map[tr_key]),
        bid1=last_ask_price_map[tr_key].get("bid1", 0),
        ask1=last_ask_price_map[tr_key].get("ask1", 0),
        bid_vol=bidp_rsqn1_map[tr_key],
        ask_vol=askp_rsqn1_map[tr_key]
    )

    Thread(
        target=update_3min_high_low_later,
        args=(tr_key, str(strategy_id), position_map[tr_key]["entry_time"]),
        daemon=True
    ).start()
    
    ord_no = place_order_market(tr_key, qty)
    save_positions()
    if not ord_no:
        print(f"[전략 실패] 주문 실패 → {tr_key}")
        with state_lock:
            position_map.pop(tr_key, None)
        return
    order_no_map[tr_key] = ord_no

def cancel_order(tr_key, ord_no):
    if not ord_no:
        print(f"[취소 건너뜀] 주문번호가 None 입니다 → {tr_key}")
        return

    def _task():
        url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/trading/order-rvsecncl"
        body = {
            "CANO": config["my_acct"],
            "ACNT_PRDT_CD": config["my_prod"],
            "ACNT_PWD": config["my_pwd"],
            "ORD_NO": ord_no
        }
        headers = {
            "Content-Type": "application/json; charset=utf-8",
            "authorization": f"Bearer {get_access_token()}",
            "appkey": APP_KEY,
            "appsecret": APP_SECRET,
            "tr_id": "TTTC2001U",
            "custtype": "P",
            "hashkey": make_hash(body)
        }
        try:
            res = requests.post(url, headers=headers, json=body)
            print(f"[주문취소] 종목: {tr_key}, 주문번호: {ord_no}")
            print("[응답]", res.status_code, res.text)
        except Exception as e:
            print(f"[ERROR] 주문취소 실패: {e}")

    api_job_queue.put(_task)
        
def submit_sell_order(tr_key: str, req_qty: int | None = None, *, reason="", strategy_id=0, entry_time=None):
    """
    • reason: "익절" / "손절" / "시간청산" 등
    • strategy_id: 전략 번호 (ex: 1~9)
    • entry_time: 진입 시각 (time.time())
    """
    print(f"[매도 시도] {tr_key} (전달 qty={req_qty})")

    # 1️⃣ 실시간 잔고 수량 조회
    def _get_balance_qty() -> int:
        url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/trading/inquire-balance"
        headers = {
            "Content-Type":  "application/json; charset=utf-8",
            "authorization": f"Bearer {get_access_token()}",
            "appkey":  APP_KEY,
            "appsecret": APP_SECRET,
            "tr_id":   "TTTC8434R",
            "custtype":"P"
        }
        params = {
            "CANO":             config["my_acct"],
            "ACNT_PRDT_CD":     config["my_prod"],
            "AFHR_FLPR_YN":     "N",
            "OFL_YN":           "",
            "INQR_DVSN":        "02",
            "UNPR_DVSN":        "01",
            "FUND_STTL_ICLD_YN":"N",
            "FNCG_AMT_AUTO_RDPT_YN":"N",
            "PRCS_DVSN":        "00",
            "CTX_AREA_FK100":   "",
            "CTX_AREA_NK100":   ""
        }
        try:
            r = requests.get(url, headers=headers, params=params, timeout=5)
            r.raise_for_status()
            for item in r.json().get("output1", []):
                if item.get("pdno") == tr_key:
                    return int(item.get("hldg_qty", "0"))
            return 0
        except Exception as e:
            print(f"[ERROR] 잔고 수량 조회 실패: {e}")
            return 0

    real_qty = _get_balance_qty()
    if real_qty == 0:
        real_qty = position_map.get(tr_key, {}).get("qty", 0)
    print(f"[확인] 실시간 잔고수량 = {real_qty}")

    qty = real_qty if req_qty is None or req_qty <= 0 else min(req_qty, real_qty)
    if qty <= 0:
        print(f"[차단] 매도할 수량이 없습니다 → {tr_key}")
        return

    # 3️⃣ 주문 전송 (시장가)
    def _task():
        url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/trading/order-cash"
        body = {
            "CANO":        config["my_acct"],
            "ACNT_PRDT_CD":config["my_prod"],
            "ACNT_PWD":    config["my_pwd"],
            "PDNO":        tr_key,
            "ORD_DVSN":    "01",            # 시장가
            "ORD_QTY":     str(qty),
            "ORD_UNPR":    "0",
            "CTAC_TLNO":   config.get("my_phone","01000000000")
        }
        headers = {
            "Content-Type":"application/json; charset=utf-8",
            "authorization":f"Bearer {get_access_token()}",
            "appkey":  APP_KEY,
            "appsecret": APP_SECRET,
            "tr_id":  "TTTC0801U",
            "custtype":"P",
            "hashkey": make_hash(body)
        }
        try:
            r = requests.post(url, headers=headers, json=body)
            raw = r.content
            try:
                txt = raw.decode("utf-8")
            except UnicodeDecodeError:
                txt = raw.decode("euc-kr", errors="replace")
            data = json.loads(txt)
            if data.get("rt_cd") == "0":
                odno = data["output"].get("ODNO") or data["output"].get("odno")
                print(f"[매도 접수] {tr_key} | 수량:{qty} | 주문번호:{odno}")

                # ✅ 청산 로그 기록 (체결 단가 대신 현재가 사용)
                exec_px    = last_price_map.get(tr_key, 0)
                entry      = position_map.get(tr_key, {}).get("entry_price", 0)
                entry_time = position_map.get(tr_key, {}).get("entry_time", 0)
                strategy_id= position_map.get(tr_key, {}).get("strategy_id", 0)
                track      = mfe_mae_track_map.get(tr_key, {})
                mfe        = track.get("max_price", 0)
                mae        = track.get("min_price", 0)
                
                entry = position_map.get(tr_key, {}).get("entry_price", 0)
                수익률 = (exec_px - entry) / entry * 100 if entry else 0
                print(f"[실현 손익] {tr_key} | 진입가: {entry} → 청산가: {exec_px} | 수익률: {수익률:+.2f}%")
                
                log_entry_finish(
                    tr_key        = tr_key,
                    strategy_name = str(strategy_id),
                    exit_price    = float(exec_px),
                    reason        = reason,
                    mfe           = mfe,
                    mae           = mae,
                    max3          = mfe,
                    min3          = mae,
                    entry_time    = entry_time
                )
            else:
                print(f"[매도 실패] {tr_key} | 코드:{data.get('msg_cd')} | 사유:{data.get('msg1')}")
        except Exception as e:
            print(f"[ERROR] 매도 주문 전송 실패: {e}")

    api_job_queue.put(_task)

def place_short_order(tr_key: str, qty: int) -> str | None:
    def _task():
        url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/trading/order-cash"
        body = {
            "CANO": config["my_acct"],
            "ACNT_PRDT_CD": config["my_prod"],
            "ACNT_PWD": config["my_pwd"],
            "PDNO": tr_key,
            "ORD_DVSN": "01",
            "ORD_QTY": str(qty),
            "ORD_UNPR": "0",
            "CTAC_TLNO": config.get("my_phone", "01000000000"),
            "LOAN_DT": "",
            "ORD_CLS": "01"
        }
        headers = {
            "Content-Type": "application/json; charset=utf-8",
            "authorization": f"Bearer {get_access_token()}",
            "appkey": APP_KEY,
            "appsecret": APP_SECRET,
            "tr_id": "TTTC8011U",
            "custtype": "P",
            "hashkey": make_hash(body)
        }
        try:
            res = requests.post(url, headers=headers, json=body)
            data = res.json()
            if "output" in data and ("ODNO" in data["output"] or "odno" in data["output"]):
                ord_no = data["output"].get("ODNO") or data["output"].get("odno")
                print(f"[전략5 공매도] 시장가 진입 전송 완료 → 주문번호: {ord_no}")
                print("[응답]", res.status_code, res.text)
                return ord_no
            else:
                print(f"[ERROR] 공매도 주문 실패 | msg: {data.get('msg1')}")
                return None
        except Exception as e:
            print(f"[ERROR] 공매도 주문 전송 실패: {e}")
            return None

    result_box = {"ord_no": None}
    def wrapped():
        result_box["ord_no"] = _task()
    api_job_queue.put(wrapped)
    while result_box["ord_no"] is None:
        time.sleep(0.05)
    return result_box["ord_no"]

def cover_short_position(tr_key: str, qty: int):
    def _task():
        url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/trading/order-cash"
        body = {
            "CANO": config["my_acct"],
            "ACNT_PRDT_CD": config["my_prod"],
            "ACNT_PWD": config["my_pwd"],
            "PDNO": tr_key,
            "ORD_DVSN": "01",
            "ORD_QTY": str(qty),
            "ORD_UNPR": "0",
            "CTAC_TLNO": config.get("my_phone", "01000000000"),
            "LOAN_DT": "",
            "ORD_CLS": "02"
        }
        headers = {
            "Content-Type": "application/json; charset=utf-8",
            "authorization": f"Bearer {get_access_token()}",
            "appkey": APP_KEY,
            "appsecret": APP_SECRET,
            "tr_id": "TTTC8012U",
            "custtype": "P",
            "hashkey": make_hash(body)
        }
        try:
            res = requests.post(url, headers=headers, json=body)
            print(f"[전략5 청산] 숏 커버링 전송 완료 → {tr_key}, 수량: {qty}")
            print("[응답]", res.status_code, res.text)
        except Exception as e:
            print(f"[ERROR] 커버링 실패: {e}")

    api_job_queue.put(_task)
        
# ----------------------------------
# [실시간 승인키]
# ----------------------------------
def get_approval_key():
    url = f"{REAL_DOMAIN}/oauth2/Approval"
    headers = {"Content-Type": "application/json; charset=utf-8"}
    body = {
        "grant_type": "client_credentials",
        "appkey": APP_KEY,
        "secretkey": APP_SECRET
    }
    try:
        res = requests.post(url, headers=headers, json=body)
        res.raise_for_status()
        data = res.json()
        if "approval_key" not in data:
            raise ValueError("approval_key not found in response")
        return data["approval_key"]
    except Exception as e:
        print(f"[ERROR] approval_key 요청 실패: {e}")
        raise

# ----------------------------------
# [WebSocket 콜백 - 에러/종료]
# ----------------------------------
def on_error(ws, error):
    print(f"[WebSocket ERROR] {error}")

def on_close(ws, close_status_code, close_msg):
    """
    WebSocket 연결이 끊겼을 때 동작.
    ▸ 2ⁿ-back-off (1→2→4→8→16 초)로 최대 5 회 재연결 시도  
    ▸ 재연결에 성공하면 포지션·전략 그대로 유지하고 함수 종료  
    ▸ 5 회 연속 실패해야만 전량 시장가 청산 뒤 프로그램 종료
    """

    import sys, time, datetime, traceback

    # ✅ 디버깅 로그 추가
    try:
        with open("ws_disconnect_debug.log", "a", encoding="utf-8") as f:
            f.write("\n📴 [WebSocket 연결 종료 감지]\n")
            f.write(f"⏰ 시각              : {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
            f.write(f"🔌 close_status_code : {close_status_code}\n")
            f.write(f"💬 close_msg         : {close_msg}\n")

            try:
                sock = ws.sock
                f.write(f"🧵 ws.sock.connected : {sock and sock.connected}\n")
                f.write(f"📡 ws.sock.sock      : {sock and sock.sock}\n")
            except Exception as e:
                f.write(f"[예외] sock 접근 실패: {e}\n")

            try:
                f.write(f"🧾 최근 전송 시각     : {ws_send_times[-1] if ws_send_times else '없음'}\n")
                f.write(f"🧾 전송 시각 리스트   : {list(ws_send_times)}\n")
            except:
                pass

            try:
                f.write(f"📋 현재 구독 종목 수   : {len(subscribed_codes)}\n")
                f.write(f"📋 구독 종목 리스트     : {list(subscribed_codes)}\n")
            except Exception as e:
                f.write(f"[예외] 구독 리스트 접근 실패: {e}\n")

    except Exception as e:
        print(f"[ERROR] 디버깅 로그 작성 실패: {e}")
        print(traceback.format_exc())

    # ───────────────────────────────────────────────
    print(f"[WebSocket CLOSED] status:{close_status_code}, msg:{close_msg}")
    print(f"[⏰] {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

    max_retries = 5
    for i in range(max_retries):
        wait = min(2 ** i, 30)
        print(f"[재연결 {i+1}/{max_retries}] {wait}s 뒤 시도")
        time.sleep(wait)
        try:
            start_websocket()
            print("[재연결 성공] 포지션/전략 정상 복원")
            return
        except Exception as e:
            print(f"[재연결 실패 {i+1}] {e}")
            traceback.print_exc()

    print("[최대 재연결 실패] 전량 시장가 청산 후 종료")
    try:
        auto_liquidate_all()
    except Exception as e:
        print(f"[일괄청산 오류] {e}")

    save_positions()

# ----------------------------------
# [WebSocket 콜백 - 메시지 수신]
#  체결(H0STCNT0) vs 호가(H0STASP0) 분기
# ----------------------------------
def on_message(ws, raw):
    """
    한국투자증권 WebSocket 수신 콜백
      1) PING·PINGPONG → echo
      2) SUBSCRIBE/ACK JSON → 로그 출력
      3) 실시간 파이프(|) 데이터 → 파서 호출
    """
    # bytes → str
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8")
        except UnicodeDecodeError:
            raw = raw.decode("euc-kr", errors="ignore")

    # 1) Heart-beat
    if "PINGPONG" in raw:
        ws_safe_send(raw)      # 서버가 보낸 그대로 돌려보냄
        return
    if raw.strip() == "PING":
        ws_safe_send("PONG")
        return

    # 2) JSON 패킷 (SUBSCRIBE ACK 등)
    if raw.startswith("{"):
        try:
            j = json.loads(raw)
            tr_id = j["header"].get("tr_id", "")
        except Exception:
            print("[WARN] JSON 파싱 실패:", raw[:120])
            return
        if tr_id != "PINGPONG":
            print("[ACK]", tr_id, j.get("body", {}).get("msg1", ""))
        return

    # 3) 실시간 데이터 (0|… 형식)
    if not raw.startswith("0|"):
        return

    parts = raw.split("|")
    if len(parts) < 4:
        return

    tr_id         = parts[1]
    rec_count_str = parts[2]
    body          = parts[3]
    try:
        rec_cnt = int(rec_count_str)
    except ValueError:
        rec_cnt = 1

    if tr_id == "H0STCNI0":
        parse_execution_data(body.split("^"))
        return
    elif tr_id == "H0STCNT0":
        fields = body.split("^")
        parse_tick_data(fields)
        return

    if tr_id == "H0STCNT0":          # 체결(틱)
        min_fields, rec_len, parse_fn = 23, 50, parse_tick_data
    elif tr_id == "H0STASP0":        # 호가
        min_fields, rec_len, parse_fn = 44, 60, parse_ask_data
    else:
        return

    data = body.split("^")
    for i in range(rec_cnt):
        seg = data[i * rec_len : (i + 1) * rec_len]
        if len(seg) < min_fields:
            continue
        EXECUTOR.submit(parse_fn, seg)

# ----------------------------------
# [호가 데이터 파싱]
# ----------------------------------
def parse_ask_data(fields):
    try:
        tr_key = fields[0]

        now = time.time()
        if now - last_ask_log_time_map[tr_key] < 1:
            return
        last_ask_log_time_map[tr_key] = now

        if tr_key not in last_ask_price_map:
            last_ask_price_map[tr_key] = {
                f"bid{i}": 0 for i in range(1, 6)
            } | {
                f"ask{i}": 0 for i in range(1, 6)
            }

        def get_int(index, key):
            try:
                val = fields[index]
                if val == '':
                    return last_ask_price_map[tr_key][key]
                return int(val)
            except (IndexError, ValueError):
                return last_ask_price_map[tr_key][key]

        # 호가 가격 필드 (정상 순서: bid=6~10, ask=11~15)
        bid_vals = [get_int(6 + i, f"bid{i+1}") for i in range(5)]
        ask_vals = [get_int(11 + i, f"ask{i+1}") for i in range(5)]

        # 호가 잔량 필드 (bid 잔량 = 21, ask 잔량 = 16)
        try:
            bid_qty = int(fields[21]) if fields[21].isdigit() else 0
            ask_qty = int(fields[16]) if fields[16].isdigit() else 0
        except IndexError:
            bid_qty = 0
            ask_qty = 0

        bidp_rsqn1_map[tr_key] = bid_qty
        askp_rsqn1_map[tr_key] = ask_qty
        bidp_rsqn3_map[tr_key] = sum([int(fields[i]) for i in (21, 22, 23) if i < len(fields) and fields[i].isdigit()])
        askp_rsqn3_map[tr_key] = sum([int(fields[i]) for i in (16, 17, 18) if i < len(fields) and fields[i].isdigit()])

        for i in range(5):
            last_ask_price_map[tr_key][f"bid{i+1}"] = bid_vals[i]
            last_ask_price_map[tr_key][f"ask{i+1}"] = ask_vals[i]

        bid_sum = sum(bid_vals)
        ask_sum = sum(ask_vals)

        bid_ho_map[tr_key].append(bid_sum)
        ask_ho_map[tr_key].append(ask_sum)

        bidp_rsqn3_map[tr_key] = sum(bid_vals[:3])
        askp_rsqn3_map[tr_key] = sum(ask_vals[:3])
        호가확인_map[tr_key] = True  # ✅ 호가 수신 완료 표시
        
    except Exception as e:
        print(f"[ERROR] 호가 데이터 파싱 실패: {e}")
        print(traceback.format_exc())
        
def verify_indicators(tr_key):
    """
    1분·3분·3틱 기준 RSI-14 / MA20 / BollingerBands(20,2)를
    ta 라이브러리 기준과 비교하여
    - 오차 범위 이내면: ✅ 수치와 함께 성공 메시지 출력
    - 초과 시: ⚠️ 경고 메시지 출력
    """
    def _diff(a, b):
        return abs(a - b) if a is not None and b is not None else 999

    def _print_check(tf, my_rsi, lib_rsi, my_ma, lib_ma,
                     my_up, lib_up, my_lo, lib_lo):
        def _fmt(x):
            return f"{x:.2f}" if isinstance(x, (float, int)) else "N/A"

        ok = True
        details = []

        if my_rsi is None or lib_rsi is None or abs(my_rsi - lib_rsi) > 1:
            details.append(f"RSI {_fmt(my_rsi)}/{_fmt(lib_rsi)}")
            ok = False
        else:
            details.append(f"RSI {_fmt(my_rsi)}")

        if my_ma is None or lib_ma is None or abs(my_ma - lib_ma) > 0.01:
            details.append(f"MA20 {_fmt(my_ma)}/{_fmt(lib_ma)}")
            ok = False
        else:
            details.append(f"MA20 {_fmt(my_ma)}")

        if (my_up is None or lib_up is None or my_lo is None or lib_lo is None or
            abs(my_up - lib_up) > 0.05 or abs(my_lo - lib_lo) > 0.05):
            details.append("BB ±2σ 차이 있음")
            ok = False
        else:
            details.append("BB ±2σ OK")

        if not ok:
            print(f"⚠️  지표검증 실패 [{tf}] {tr_key} → " + ', '.join(details))
    # ---------- 1분 ----------
    if len(candle_1min_map[tr_key]) >= 20:
        closes = [c["close"] for c in list(candle_1min_map[tr_key])[-20:]]
        df = pd.DataFrame({"close": closes})
        lib_rsi = RSIIndicator(df["close"], 14).rsi().iloc[-1]
        lib_ma  = SMAIndicator(df["close"], 20).sma_indicator().iloc[-1]
        bb = BollingerBands(df["close"], 20, 2)
        lib_up = bb.bollinger_hband().iloc[-1]
        lib_lo = bb.bollinger_lband().iloc[-1]
        my_rsi = rsi_14_1min_map[tr_key].get("now")
        my_ma = ma_20_1min_map[tr_key]
        std = (sum((c - my_ma) ** 2 for c in closes) / 20) ** 0.5
        my_up = my_ma + 2 * std
        my_lo = my_ma - 2 * std
        _print_check("1분", my_rsi, lib_rsi, my_ma, lib_ma, my_up, lib_up, my_lo, lib_lo)

    # ---------- 3분 ----------
    if len(candle_3min_map[tr_key]) >= 20:
        closes = [c["close"] for c in list(candle_3min_map[tr_key])[-20:]]
        df = pd.DataFrame({"close": closes})
        lib_rsi = RSIIndicator(df["close"], 14).rsi().iloc[-1]
        lib_ma  = SMAIndicator(df["close"], 20).sma_indicator().iloc[-1]
        bb = BollingerBands(df["close"], 20, 2)
        lib_up = bb.bollinger_hband().iloc[-1]
        lib_lo = bb.bollinger_lband().iloc[-1]
        my_rsi = rsi_14_3min_map[tr_key].get("now")
        my_ma = ma_20_3min_map[tr_key]
        std = (sum((c - my_ma) ** 2 for c in closes) / 20) ** 0.5
        my_up = my_ma + 2 * std
        my_lo = my_ma - 2 * std
        _print_check("3분", my_rsi, lib_rsi, my_ma, lib_ma, my_up, lib_up, my_lo, lib_lo)

    # ---------- 3틱 ----------
    if len(candle_3tick_map[tr_key]) >= 20:
        closes = [c["close"] for c in list(candle_3tick_map[tr_key])[-20:]]
        df = pd.DataFrame({"close": closes})
        lib_rsi = RSIIndicator(df["close"], 14).rsi().iloc[-1]
        lib_ma  = SMAIndicator(df["close"], 20).sma_indicator().iloc[-1]
        bb = BollingerBands(df["close"], 20, 2)
        lib_up = bb.bollinger_hband().iloc[-1]
        lib_lo = bb.bollinger_lband().iloc[-1]
        my_rsi = rsi_14_3tick_map[tr_key].get("now")
        my_ma = ma_20_3tick_map[tr_key]
        std = (sum((c - my_ma) ** 2 for c in closes) / 20) ** 0.5
        my_up = my_ma + 2 * std
        my_lo = my_ma - 2 * std
        _print_check("3틱", my_rsi, lib_rsi, my_ma, lib_ma, my_up, lib_up, my_lo, lib_lo)

def subscribe_realtime(code):
    global approval_key
    if not approval_key:
        return

    try:
        with open("subscribe_debug.log", "a", encoding="utf-8") as f:
            f.write("\n🟡 [구독요청 시도] {}\n".format(code))
            f.write("  ⏰ 시각          : {}\n".format(datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')))
            f.write("  🧾 subscribed    : {}\n".format(code in subscribed_codes))
            f.write("  📦 큐에 있음     : {}\n".format(code in list(subscribe_job_queue.queue)))
            f.write("  🌐 연결 상태     : {}\n".format(ws_instance and ws_instance.sock and ws_instance.sock.connected))
    except Exception as e:
        print(f"[구독 디버깅 로그 실패] {e}")

    if code in subscribed_codes:
        return

    # 큐에도 이미 들어있으면 무시 (중복 방지)
    with subscribe_job_queue.mutex:
        if code in subscribe_job_queue.queue:
            return

    subscribe_job_queue.put(code)

def unsubscribe_realtime(code):
    """
    관심종목 제거 시 실시간 해제 호출
    • TPS 제한(5건/초) 준수 위해 패킷 2건 사이·마지막 전송 후
      각각 0.21초 지연 추가
    """
    global approval_key, ws_instance

    if not approval_key:
        return
    if not ws_instance or not ws_instance.sock or not ws_instance.sock.connected:
        print(f"[구독해제 생략] WebSocket 연결 안 됨 → {code}")
        time.sleep(0.21)    # 다른 작업과의 간격 확보
        return

    data_tick = {
        "header": {
            "approval_key": approval_key,
            "custtype": "P",
            "tr_type": "2",
            "content-type": "utf-8"
        },
        "body": {
            "input": {
                "tr_id": TR_ID_TICK,
                "tr_key": code
            }
        }
    }
    data_ask = {
        "header": {
            "approval_key": approval_key,
            "custtype": "P",
            "tr_type": "2",
            "content-type": "utf-8"
        },
        "body": {
            "input": {
                "tr_id": TR_ID_ASK,
                "tr_key": code
            }
        }
    }

    try:
        ws_safe_send(json.dumps(data_tick))
        ws_safe_send(json.dumps(data_ask))
        subscribed_codes.discard(code)
        print(f"[구독 해제] {code}")
    except Exception as e:
        print(f"[해제 실패] {code} 구독 해제 중 에러: {e}")

    subscribed_codes.discard(code)
    
def clear_stock_data(code):
    for m in [
        candle_1min_map, candle_3min_map, candle_3tick_map,
        cttr_1s_map, buy_volume_3s_map, sell_volume_3s_map,
        total_volume_3s_map, tick_time_list_map, tick_net_count_time_map,
        close_1min_20_map, close_3min_20_map, close_3tick_20_map,
        ma_20_1min_map, ma_20_3min_map, ma_20_3tick_map,
        high_1min_map, high_200tick_map, low_200tick_map,
        vwap_price_volume_map, vwap_volume_map,
        rsi_14_1min_map, rsi_14_3min_map, rsi_14_3tick_map,
        bid_ho_map, ask_ho_map, last_ask_price_map,
        bidp_rsqn1_map, askp_rsqn1_map, bidp_rsqn3_map, askp_rsqn3_map,
        position_map, strategy_log_time_map, last_log_time_map,
        tick_surge_flag_map, vwap_hold_flag_map,
        minute_tracker_map, cur_open_map, cur_high_map, cur_low_map,
        cur_volume_map, last_price_map
    ]:
        m.pop(code, None)
    print(f"[데이터 초기화] {code}")

def fetch_hts_interest_list() -> list[tuple[str, str]]:
    """HTS 관심그룹(001+) 종목 코드·이름 리스트 반환"""
    try:
        bearer = f"Bearer {get_access_token()}"
        url_g = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/quotations/intstock-grouplist"
        head  = {
            "Content-Type": "application/json; charset=utf-8",
            "authorization": bearer,
            "appkey": APP_KEY,
            "appsecret": APP_SECRET,
            "custtype": "P",
            "gt_uid": uuid.uuid4().hex,
            "tr_id": "HHKCM113004C7"
        }
        p_g = {"TYPE": "1", "FID_ETC_CLS_CODE": "00", "USER_ID": HTS_ID}
        data, _ = call_api("GET", url_g, headers=head, params=p_g)
        grp = next((g for g in data.get("output2", []) if g["inter_grp_code"] != "000"), None)
        if not grp:
            return []

        url_s = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/quotations/intstock-stocklist-by-group"
        head["tr_id"] = "HHKCM113004C6"
        head["gt_uid"] = uuid.uuid4().hex
        p_s = {
            "TYPE": "1",
            "USER_ID": HTS_ID,
            "INTER_GRP_CODE": grp["inter_grp_code"],
            "DATA_RANK": "",
            "INTER_GRP_NAME": "",
            "HTS_KOR_ISNM": "",
            "CNTG_CLS_CODE": "",
            "FID_ETC_CLS_CODE": "4"
        }
        d2, _ = call_api("GET", url_s, headers=head, params=p_s)
        return [(s.get("stck_shrn_iscd") or s.get("jong_code"), s["hts_kor_isnm"])
                for s in d2.get("output2", []) if s.get("hts_kor_isnm")]
    except Exception as e:
        print("[ERROR] HTS 관심목록 조회 실패:", e)
        return []


def refresh_interest_stocks_once():
    """HTS ↔ 현재 내부 목록 동기화: 새 종목 ➕, 빠진 종목 ➖"""
    hts_list = fetch_hts_interest_list()                 # [(code, name), ...]
    hts_set  = {c for c, _ in hts_list}
    with state_lock:
        cur_set = set(interest_stocks)

    # ➕ 추가
    for code, name in hts_list:
        if code not in cur_set:
            print(f"[SYNC] +{code} 추가")
            add_stock_realtime(code, name)

    # ➖ 삭제 (단, 현재 보유 중인 종목은 절대 제거하지 않음)
    for code in (cur_set - hts_set):
        # 포지션이 있으면 실시간·데이터 유지
        if code in position_map:
            continue                       # 🔒 보호
        print(f"[SYNC] -{code} 제거")
        unsubscribe_realtime(code)
        clear_stock_data(code)
        with state_lock:
            if code in interest_stocks:
                interest_stocks.remove(code)
            stock_name_map.pop(code, None)

def interest_sync_worker():
    while True:
        try:
            refresh_interest_stocks_once()
        except Exception as e:
            print("[SYNC-WORKER ERROR]", e)
        time.sleep(HTS_SYNC_INTERVAL)
        
# ----------------------------------
# [체결(틱) 데이터 파싱]
# ----------------------------------
# parse_tick_data 함수 전체 교체
def parse_tick_data(fields):
    tr_key = fields[0]
    with symbol_locks[tr_key]:
        global 체결확인, last_strategy_check_ts
        try:
            체결확인
        except NameError:
            체결확인 = False

        if not 체결확인:
            체결확인 = True
            print("🔥 체결데이터 수신 성공 → 전략 조건 확인 시작됨")

        tr_key = fields[0]
        if tr_key not in interest_stocks and tr_key not in position_map:
            return

        try:
            # --- 가격 · 거래량 파싱 --------------------------------
            price = int(fields[2]) if fields[2].isdigit() else 0   
            
            if warmup_start_time_map[tr_key] == 0:
                warmup_start_time_map[tr_key] = time.time()
        # ───────── MFE / MAE 실시간 최대·최소 갱신 ─────────
            if tr_key in mfe_mae_track_map:
                track = mfe_mae_track_map[tr_key]
                track["max_price"] = max(track["max_price"], price)
                track["min_price"] = min(track["min_price"], price)
    #        if not verify_done_map[tr_key]:
    #            rest_price = fetch_cur_price(tr_key)
    #            latest_1m = candle_1min_map[tr_key][-1]["close"] if candle_1min_map[tr_key] else None
    #            if rest_price is not None and (price != rest_price or (latest_1m and price != latest_1m)):
    #                print(f"\n📌 [데이터 검증] {tr_key}")
    #                print(f"  - WS 현재가:     {price}")
    #                print(f"  - REST 현재가:   {rest_price}")
    #                print(f"  - 1분봉 종가:    {latest_1m}")
    #                print(f"  → WS↔REST 차이:  {abs(price - rest_price)}")
    #                if latest_1m:
    #                    print(f"  → WS↔1분봉 차이: {abs(price - latest_1m)}")
    #                print("  ⚠️ WS/REST/1분봉 값 불일치 검출\n")
    #            verify_done_map[tr_key] = True
            volume  = int(fields[10]) if fields[10].isdigit() else 0
            # 이번 체결 건수 (cntg_vol = fields[10]) 를 그대로 사용
            try:
                volume = int(fields[10])            # cntg_vol
            except (IndexError, ValueError):
                volume = 0

            # -------------------------------------------------------
            vwap_price_volume_map[tr_key] += price * volume
            vwap_volume_map[tr_key] += volume
            cttr = float(fields[18]) if fields[18] else 0.0
            seln_cntg_csnu = int(fields[15]) if fields[15].isdigit() else 0
            shnu_cntg_csnu = int(fields[16]) if fields[16].isdigit() else 0

            hhmmss = fields[1]
            hh = int(hhmmss[0:2])
            mm = int(hhmmss[2:4])
            ss = int(hhmmss[4:6])
            cur_min = hh * 60 + mm
            now_ts = time.time()

            if tr_key not in minute_tracker_map:
                if candle_1min_map[tr_key]:
                    # fetch_today_1min()으로 이미 불러온 1분봉이 존재 → 지우지 말고 그대로 이어받음
                    last_candle = candle_1min_map[tr_key][-1]
                    minute_tracker_map[tr_key] = last_candle["time"]
                    cur_open_map[tr_key]       = last_candle["open"]
                    cur_high_map[tr_key]       = last_candle["high"]
                    cur_low_map[tr_key]        = last_candle["low"]
                    cur_volume_map[tr_key]     = last_candle["volume"]
                    last_price_map[tr_key]     = last_candle["close"]
                    day_open_price_map[tr_key] = candle_1min_map[tr_key][0]["open"]
                else:
                    # 선로딩 데이터가 아예 없을 때만 새로 초기 캔들 생성
                    minute_tracker_map[tr_key] = cur_min
                    cur_open_map[tr_key]       = price
                    cur_high_map[tr_key]       = price
                    cur_low_map[tr_key]        = price
                    cur_volume_map[tr_key]     = volume
                    last_price_map[tr_key]     = price
                    day_open_price_map[tr_key] = price
                    candle_1min_map[tr_key].append({
                        "time": cur_min,
                        "open": price,
                        "high": price,
                        "low": price,
                        "close": price,
                        "volume": volume
                    })
                return
               
            last_price = last_price_map.get(tr_key)
            now_minute = int(now_ts // 60)

            key = tr_key if tr_key.startswith("A") else f"A{tr_key}"
            if gap_log_time_map[tr_key] == 0:
                prev = prev_close_price_map.get(key, 0)

                if not prev or prev == 0:
                    pass
                else:
                    gap_rate = ((price - prev) / prev) * 100

                gap_log_time_map[tr_key] = -1  # 한 번 출력 후 다시는 안 뜨게 만듦

            cur_open = cur_open_map.get(tr_key)
            cur_high = cur_high_map.get(tr_key)
            cur_low = cur_low_map.get(tr_key)
            cur_vol = cur_volume_map.get(tr_key, 0)
            minute_tracker = minute_tracker_map.get(tr_key)

            finalized_candle = None

            if minute_tracker is None and len(candle_1min_map[tr_key]) == 1:
                first = candle_1min_map[tr_key][0]
                finalized_candle = {
                    "time": first["time"],
                    "open": first["open"],
                    "high": first["high"],
                    "low": first["low"],
                    "close": first["close"],
                    "volume": first["volume"]
                }
                snapshot = snapshot_row_for_strategy11(tr_key)
                snapshot.update(finalized_candle)           # 기본 OHLC 정보도 유지
                last_finalized_1min_map[tr_key] = snapshot
                close_1min_20_map[tr_key].append(first["close"])
                high_1min_map[tr_key].append(first["high"])
                
                minute_tracker_map[tr_key] = cur_min
                cur_open_map[tr_key] = price
                cur_high_map[tr_key] = price
                cur_low_map[tr_key] = price
                cur_volume_map[tr_key] = volume
                last_price_map[tr_key] = price
                candle_1min_map[tr_key].append({
                    "time": cur_min,
                    "open": price,
                    "high": price,
                    "low": price,
                    "close": price,
                    "volume": volume
                })
            else:
                if minute_tracker == cur_min:
                    cur_high_map[tr_key] = max(cur_high or price, price)
                    cur_low_map[tr_key] = min(cur_low or price, price)
                    cur_volume_map[tr_key] = cur_vol + volume
                    
                    last_candle = candle_1min_map[tr_key][-1]
                    last_candle["high"]    = cur_high_map[tr_key]
                    last_candle["low"]     = cur_low_map[tr_key]
                    last_candle["close"]   = price
                    last_candle["volume"]  = cur_volume_map[tr_key]     
                    last_price_map[tr_key] = price                              
                else:
                    finalized_candle = {
                        "time": minute_tracker,
                        "open": cur_open if cur_open is not None else price,
                        "high": cur_high if cur_high is not None else price,
                        "low": cur_low if cur_low is not None else price,
                        "close": last_price if last_price is not None else price,
                        "volume": cur_vol
                    }
                    candle_1min_map[tr_key].append(finalized_candle)
                    if len(candle_1min_map[tr_key]) > 120:
                        candle_1min_map[tr_key].popleft()

                    minute_tracker_map[tr_key] = cur_min
                    cur_open_map[tr_key] = price
                    cur_high_map[tr_key] = price
                    cur_low_map[tr_key] = price
                    cur_volume_map[tr_key] = volume

                    candle_1min_map[tr_key].append({
                        "time": cur_min,
                        "open": price,
                        "high": price,
                        "low": price,
                        "close": price,
                        "volume": volume
                    })

            last_price_map[tr_key] = price

            last_strategy_check_ts = time.time()
            
            for _fn in [
                strategy_1, strategy_2, strategy_3, strategy_4, strategy_5,
                strategy_6, strategy_7, strategy_8, strategy_9, strategy_10,
                strategy_11
            ]:
                # 같은 종목에 대해선 _run_strategy_safe()가 mutex 역할을 한다
                EXECUTOR.submit(_run_strategy_safe, _fn, tr_key)

            is_vwap_held_1min = False

            vwap = vwap_price_volume_map[tr_key] / vwap_volume_map[tr_key] if vwap_volume_map[tr_key] > 0 else 0
            if vwap > 0:
                if price >= vwap * 1.001:
                    if vwap_check_start_time_map[tr_key] == 0:
                        vwap_check_start_time_map[tr_key] = now_ts
                    elif now_ts - vwap_check_start_time_map[tr_key] >= 60:
                        is_vwap_held_1min = True
                    # else는 유지 중이라 pass (굳이 False로 덮을 필요 없음)
                else:
                    # 단기 이탈인지 여부 확인 후 초기화
                    if (
                        vwap_check_start_time_map[tr_key] > 0
                        and now_ts - vwap_check_start_time_map[tr_key] > 2
                    ):
                        vwap_check_start_time_map[tr_key] = 0
                    is_vwap_held_1min = False

            vwap_hold_flag_map[tr_key] = is_vwap_held_1min

            cttr_1s_map[tr_key].append(cttr)
            buy_volume_3s_map[tr_key].append(shnu_cntg_csnu)
            sell_volume_3s_map[tr_key].append(seln_cntg_csnu)
            total_volume_3s_map[tr_key].append(seln_cntg_csnu + shnu_cntg_csnu)
            # ─── OBV 누적 업데이트 ───
            prev_obv   = obv_map[tr_key][-1] if obv_map[tr_key] else 0
            prev_price = last_price_map.get(tr_key)
            if prev_price is not None:
                if price > prev_price:
                    obv_val = prev_obv + volume
                elif price < prev_price:
                    obv_val = prev_obv - volume
                else:
                    obv_val = prev_obv
                obv_map[tr_key].append(obv_val)
            # ──────────────────────────
            rsi = None
            ma = upper = lower = None

            if finalized_candle:
                close_1min_20_map[tr_key].append(finalized_candle["close"])
                high_1min_map[tr_key].append(finalized_candle["high"])
                snapshot = snapshot_row_for_strategy11(tr_key)
                snapshot.update(finalized_candle)           # 기본 OHLC 정보도 유지
                last_finalized_1min_map[tr_key] = snapshot

                if len(candle_1min_map[tr_key]) >= 3:
                    warmup_done_map[tr_key] = True  # 워밍업 완료 표시

                if "now" in rsi_14_3min_map[tr_key]:
                    rsi_14_3min_map[tr_key]["prev"] = rsi_14_3min_map[tr_key]["now"]

            else:
                return  # finalized_candle 없으면 바로 종료
                
            update_ta_indicators(tr_key)
            verify_indicators(tr_key)   

            current_3min = cur_min // 3

            if tr_key not in candle_3min_temp_map:
                candle_3min_temp_map[tr_key] = []

            last_idx = last_3min_index_map[tr_key]

            if last_idx == -1:
                last_3min_index_map[tr_key] = current_3min
                candle_3min_temp_map[tr_key] = [finalized_candle]

            elif current_3min == last_idx:
                temp = candle_3min_temp_map[tr_key][-1]
                temp["high"] = max(temp["high"], finalized_candle["high"])
                temp["low"] = min(temp["low"], finalized_candle["low"])
                temp["close"] = finalized_candle["close"]
                temp["volume"] += finalized_candle["volume"]

            else:
                last_3min_index_map[tr_key] = current_3min
                if candle_3min_temp_map[tr_key]:
                    candle_3min_map[tr_key].append(candle_3min_temp_map[tr_key][-1])
                candle_3min_temp_map[tr_key] = [finalized_candle]

            # 3분봉 지표 계산
            if len(candle_3min_map[tr_key]) >= 15:
                closes = [x["close"] for x in list(candle_3min_map[tr_key])[-15:]]
                deltas = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
                gains = [d for d in deltas if d > 0]
                losses = [-d for d in deltas if d < 0]
                avg_gain = sum(gains) / 14 if gains else 0
                avg_loss = sum(losses) / 14 if losses else 0
                if avg_loss != 0:
                    rs = avg_gain / avg_loss
                    rsi = 100 - (100 / (1 + rs))
                    _set_rsi(rsi_14_3min_map, tr_key, rsi)

            if len(candle_3min_map[tr_key]) >= 20:
                closes = [x["close"] for x in list(candle_3min_map[tr_key])[-20:]]
                close_3min_20_map[tr_key] = deque(closes, maxlen=20)
                ma = sum(closes) / 20
                ma_20_3min_map[tr_key] = ma

            if len(candle_1min_map[tr_key]) >= 15:
                closes = [c["close"] for c in list(candle_1min_map[tr_key])[-15:]]
                deltas = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
                gains = [d for d in deltas if d > 0]
                losses = [-d for d in deltas if d < 0]
                avg_gain = sum(gains) / 14 if gains else 0
                avg_loss = sum(losses) / 14 if losses else 0
                if avg_loss != 0:
                    rs = avg_gain / avg_loss
                    rsi = 100 - (100 / (1 + rs))
                    _set_rsi(rsi_14_1min_map, tr_key, rsi)

            if len(close_1min_20_map[tr_key]) >= 20:
                closes = list(close_1min_20_map[tr_key])
                ma = sum(closes) / 20
                std = (sum((c - ma) ** 2 for c in closes) / 20) ** 0.5
                upper = ma + 2 * std
                lower = ma - 2 * std
                ma_20_1min_map[tr_key] = ma

            tick_time_list_map[tr_key].append(now_ts)
            net = 1 if shnu_cntg_csnu > seln_cntg_csnu else -1
            tick_net_count_time_map[tr_key].append((now_ts, net))
            tick_net_count_time_map[tr_key] = deque([
                (t, v) for t, v in tick_net_count_time_map[tr_key] if now_ts - t <= 60
            ])
            
            tick_net_sum = sum(v for t, v in tick_net_count_time_map[tr_key])
            tick_net_count_map[tr_key].append(tick_net_sum)
            is_tick_surge_30 = tick_net_sum >= 30
            tick_surge_flag_map[tr_key] = is_tick_surge_30
            tick_net_sum = sum(v for t, v in tick_net_count_time_map[tr_key])

            close_3tick_map[tr_key].append(price)
            high_200tick_map[tr_key].append(price)
            low_200tick_map[tr_key].append(price)

            tick_3_count_map[tr_key] += 1
            tick_3_price_list_map[tr_key].append(price)
            tick_3_volume_list_map[tr_key].append(volume)
            if tick_3_count_map[tr_key] == 3:
                o = tick_3_price_list_map[tr_key][0]
                h = max(tick_3_price_list_map[tr_key])
                l = min(tick_3_price_list_map[tr_key])
                c = tick_3_price_list_map[tr_key][-1]
                v = sum(tick_3_volume_list_map[tr_key])
                candle_3tick_map[tr_key].append({
                    "open": o, "high": h, "low": l, "close": c, "volume": v
                })
                volume_3tick_map[tr_key].append(v)  # ← 이 줄 추가
                tick_3_count_map[tr_key] = 0
                tick_3_price_list_map[tr_key].clear()
                tick_3_volume_list_map[tr_key].clear()

            if len(candle_3tick_map[tr_key]) >= 20:
                closes = [x["close"] for x in list(candle_3tick_map[tr_key])[-20:]]
                close_3tick_20_map[tr_key] = deque(closes, maxlen=20)
                ma = sum(closes) / 20
                ma_20_3tick_map[tr_key] = ma
                std = (sum((c - ma) ** 2 for c in closes) / 20) ** 0.5
                upper_3 = ma + 2 * std
                lower_3 = ma - 2 * std

            if len(candle_3tick_map[tr_key]) >= 15:
                closes = [x["close"] for x in list(candle_3tick_map[tr_key])[-15:]]
                deltas = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
                gains = [d for d in deltas if d > 0]
                losses = [-d for d in deltas if d < 0]
                avg_gain = sum(gains) / 14 if gains else 0
                avg_loss = sum(losses) / 14 if losses else 0
                if avg_loss != 0:
                    rs = avg_gain / avg_loss
                    rsi = 100 - (100 / (1 + rs))
                    _set_rsi(rsi_14_3tick_map, tr_key, rsi)

        except Exception as e:
            print(f"[ERROR] 체결 데이터 처리 중 예외: {e}")
            print(traceback.format_exc())

        try:
            closes = [c["close"] for c in list(candle_1min_map[tr_key])[-20:]]
            if len(closes) == 20:
                if any(x == 0 for x in closes):
                    print(f"📛 [종가0] {tr_key} → 종가에 0 포함됨: {closes}")
                elif len(set(closes)) == 1:
                    print(f"📛 [종가고정] {tr_key} → 종가 20개 전부 동일: {closes[0]}")
        except Exception as e:
            print(f"[DEBUG] 종가 검사 중 오류: {e}")
            
def parse_execution_data(fields):
    try:
        global current_position_code

        raw_code = fields[0]
        tr_key = raw_code[1:] if raw_code.startswith("A") else raw_code  # A 접두어 제거
        ord_no   = fields[1]
        exec_qty = int(fields[3]) if fields[3].isdigit() else 0
        exec_px  = int(fields[4]) if fields[4].isdigit() else 0
        buy_sell = fields[5]

        if buy_sell == "01":             # ✅ 매수 체결
            print(f"[디버깅] 매수 체결 감지 | 종목:{tr_key} | 수량:{exec_qty} | 단가:{exec_px}")
            with state_lock:
                prev        = position_map.get(tr_key, {})
                strategy_id = prev.get("strategy_id", 0)

                # 이전 entry_time 이 있으면 그대로 보존
                entry_ts = prev.get("entry_time") or time.time()

                position_map[tr_key] = {
                    "entry_price": exec_px,      # 체결 단가
                    "entry_time":  entry_ts,     # ★ 진입 시각 유지
                    "strategy_id": strategy_id,
                    "qty":         exec_qty
                }
                last_price_map[tr_key] = exec_px
                print(f"[진입가 갱신 시도] {tr_key} | entry_ts: {entry_ts} | exec_px: {exec_px}")
                current_position_code = tr_key   # ← 이 줄 바로 아래에 붙여라

                # ✅ HTS 체결가로 진입가 강제 덮어쓰기
                def _force_sync_real_exec_price(tr_key):
                    try:
                        url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/trading/inquire-balance"
                        headers = {
                            "authorization": f"Bearer {get_access_token()}",
                            "appkey":  APP_KEY,
                            "appsecret": APP_SECRET,
                            "tr_id": "TTTC8434R",
                            "custtype": "P",
                            "Content-Type": "application/json; charset=utf-8"
                        }
                        params = {
                            "CANO": config["my_acct"],
                            "ACNT_PRDT_CD": config["my_prod"],
                            "AFHR_FLPR_YN": "N",
                            "OFL_YN": "",
                            "INQR_DVSN": "02",
                            "UNPR_DVSN": "01",
                            "FUND_STTL_ICLD_YN": "N",
                            "FNCG_AMT_AUTO_RDPT_YN": "N",
                            "PRCS_DVSN": "00",
                            "CTX_AREA_FK100": "",
                            "CTX_AREA_NK100": ""
                        }
                        data, err = call_api("GET", url, headers=headers, params=params)
                        if err:
                            print(f"[HTS체결가조회 실패] {err}")
                            return
                        for item in data.get("output1", []):
                            if item.get("pdno") == tr_key:
                                avg = item.get("pchs_avg_pric", "").replace(",", "")
                                if avg:
                                    avg_price = float(avg)
                                    position_map[tr_key]["entry_price"] = avg_price
                                    print(f"[진짜 체결가 동기화] {tr_key} → {avg_price}")
                    except Exception as e:
                        print(f"[ERROR] 진짜 체결가 동기화 실패: {e}")

                _force_sync_real_exec_price(tr_key)
            print(f"[체결알림] 매수 체결 | {tr_key} | 수량:{exec_qty} 단가:{exec_px}")

            # ✔ 진짜 체결가로 로그 파일 속 진입가 덮어쓰기
            try:
                date_str = datetime.datetime.now().strftime("%Y%m%d")
                fname = f"logs/{strategy_id}전략_{date_str}.csv"
                if os.path.exists(fname):
                    with log_lock:
                        with open(fname, newline="", encoding="utf-8") as f:
                            rows = list(csv.DictReader(f))
                        target_idx = None
                        for i in reversed(range(len(rows))):
                            row = rows[i]
                            if (row.get("종목코드") == tr_key and
                                row.get("전략 이름") == str(strategy_id) and
                                not row.get("청산 시각")):
                                target_idx = i
                                break
                        if target_idx is not None:
                            rows[target_idx]["진입가"] = f"{exec_px:.2f}"
                            print(f"[디버깅] 진입 로그 덮어쓰기 완료 → 체결가 기준 진입가: {exec_px}")
                            print(f"[진입가 덮어쓰기 완료] {fname} | index: {target_idx}")
                            with open(fname, "w", newline="", encoding="utf-8") as f:
                                wr = csv.DictWriter(f, fieldnames=rows[0].keys())
                                wr.writeheader()
                                wr.writerows(rows)
            except Exception as e:
                print(f"[오류] 진입가 갱신 실패: {e}")

        elif buy_sell == "02":           # ✅ 매도(청산) 체결     
            print(f"[디버깅] 매도 체결 감지 | 종목:{tr_key} | 수량:{exec_qty} | 단가:{exec_px}")
            print(f"[체결알림] 매도 체결 | {tr_key} | 수량:{exec_qty} 단가:{exec_px}")

            entry       = position_map.get(tr_key, {}).get("entry_price", 0)
            entry_time  = position_map.get(tr_key, {}).get("entry_time", 0)
            strategy_id = position_map.get(tr_key, {}).get("strategy_id", 0)

            track = mfe_mae_track_map.get(tr_key, {})
            mfe   = track.get("max_price", 0)
            mae   = track.get("min_price", 0)

            수익률 = (exec_px - entry) / entry if entry else 0
            reason  = ("익절" if 수익률 > 0 else
                       "손절" if 수익률 < 0 else
                       "본절")

            with open("log_finish_debug.txt", "a", encoding="utf-8") as f:
                f.write(f"[DEBUG] 청산 호출됨 | 종목: {tr_key} | 전략: {strategy_id} | 진입가: {entry} | 진입시각: {entry_time} | 청산가: {exec_px} | MFE: {mfe} | MAE: {mae}\n")
            print(f"[디버깅] 청산 로그 기록 직전 → entry: {entry}, entry_time: {entry_time}, strategy_id: {strategy_id}, 청산가: {exec_px}")
            Thread(target=log_entry_finish, kwargs={
                "tr_key": tr_key,
                "strategy_name": str(strategy_id),
                "exit_price": float(exec_px),
                "reason": reason,
                "mfe": mfe,
                "mae": mae,
                "entry_time": entry_time,
                "max3": None,
                "min3": None
            }, daemon=True).start()
            
            _force_sync_real_exec_price(tr_key)
            # ✔ 매도 후 진입가 재반영 (혹시 덮어쓰기 실패했을 경우 보완)
            try:
                date_str = datetime.datetime.now().strftime("%Y%m%d")
                fname = f"logs/{strategy_id}전략_{date_str}.csv"
                if os.path.exists(fname):
                    with log_lock:
                        with open(fname, newline="", encoding="utf-8") as f:
                            rows = list(csv.DictReader(f))
                        target_idx = None
                        for i in reversed(range(len(rows))):
                            row = rows[i]
                            if (row.get("종목코드") == tr_key and
                                row.get("전략 이름") == str(strategy_id) and
                                not row.get("청산 시각")):
                                target_idx = i
                                break
                        if target_idx is not None:
                            rows[target_idx]["진입가"] = f"{entry:.2f}" if entry else ""
                            with open(fname, "w", newline="", encoding="utf-8") as f:
                                wr = csv.DictWriter(f, fieldnames=rows[0].keys())
                                wr.writeheader()
                                wr.writerows(rows)
            except Exception as e:
                print(f"[오류] 매도 진입가 갱신 실패: {e}")

            with state_lock:
                if tr_key in position_map:
                    position_map[tr_key]["qty"] -= exec_qty
                    if position_map[tr_key]["qty"] <= 0:
                        position_map.pop(tr_key, None)
                        print(f"[정리완료] {tr_key} 포지션 제거 (수량 0)")
                        save_positions()

            current_position_code = None
            _held_cache.pop(tr_key, None)

    except Exception as e:
        print(f"[ERROR] 체결 데이터 처리 실패: {e}")

def update_strategy_timestamp():
    global last_strategy_check_ts
    last_strategy_check_ts = time.time()
    
def strategy_1(tr_key):
    update_strategy_timestamp()
    if (not 체결확인 or not 호가확인_map[tr_key] or not warmup_done_map[tr_key]):
        return
    if time.time() - warmup_start_time_map[tr_key] < 60:
        return
    if tr_key in position_map:
        if position_map[tr_key].pop("_need_monitor", False):
            Thread(target=start_monitor_strategy1, args=(tr_key,), daemon=True).start()
        return
    if len(close_1min_20_map[tr_key]) < 20 or "now" not in rsi_14_1min_map[tr_key]:
        return
    price = last_price_map.get(tr_key)
    rsi = rsi_14_1min_map[tr_key]["now"]
    ma = ma_20_1min_map[tr_key]
    closes = list(close_1min_20_map[tr_key])
    std = (sum((c - ma) ** 2 for c in closes) / 20) ** 0.5
    lower = ma - 2 * std
    prev_rsi = rsi_14_1min_map[tr_key].get("prev", rsi)
    was_below = (closes[-2] < lower) and (prev_rsi < 30)
    now_above = (price >= lower) or (rsi >= 30)
    if not (was_below and now_above):
        return
    ask1 = last_ask_price_map[tr_key].get("ask1", 0)
    if ask1 > int(price * 1.004):
        return
    print(f"[전략1] 조건 충족 → {tr_key}")
    entry_time = time.time()
    position_map[tr_key] = {
        "entry_price": price,
        "entry_time": entry_time,
        "strategy_id": 1,
        "qty": 1
    }
    submit_order(tr_key, price, strategy_id=1)
    mfe_mae_track_map[tr_key] = {
        "start_time": entry_time,
        "max_price": price,
        "min_price": price
    }
    position_map[tr_key]["_need_monitor"] = True

def start_monitor_strategy1(tr_key):
    try:
        price = position_map[tr_key]["entry_price"]
        entry_time = position_map[tr_key]["entry_time"]
        
        for _ in range(600):
            time.sleep(0.1)
            now = last_price_map.get(tr_key)
            bid1 = last_ask_price_map[tr_key].get("bid1", 0)

            if not now:
                continue
            if bid1 >= int(price * TP_RATIO):
                submit_sell_order(tr_key, 0, reason="익절", strategy_id=1, entry_time=entry_time)
                return
            if now <= int(price * SL_RATIO):
                submit_sell_order(tr_key, 0, reason="손절", strategy_id=1, entry_time=entry_time)
                return

        submit_sell_order(tr_key, 0, reason="시간청산", strategy_id=1, entry_time=entry_time)
    except Exception as e:
        print(f"[전략1 오류] {e}")

def strategy_2(tr_key):
    update_strategy_timestamp()
    if (not 체결확인 or not 호가확인_map[tr_key] or not warmup_done_map[tr_key]):
        return
    if time.time() - warmup_start_time_map[tr_key] < 60:
        return
    if tr_key in position_map:
        if position_map[tr_key].pop("_need_monitor", False):
            Thread(target=start_monitor_strategy2, args=(tr_key,), daemon=True).start()
        return
    if (vwap_volume_map[tr_key] <= 0 or
        "now" not in rsi_14_1min_map[tr_key] or
        len(obv_map[tr_key]) < 2):
        return
    price = last_price_map.get(tr_key)
    vwap = vwap_price_volume_map[tr_key] / vwap_volume_map[tr_key]
    rsi = rsi_14_1min_map[tr_key]["now"]
    prev_close = candle_1min_map[tr_key][-2]["close"] if len(candle_1min_map[tr_key]) >= 2 else 0
    crossed_up = (prev_close < vwap) and (price >= vwap)
    obv_now = obv_map[tr_key][-1]
    obv_prev = obv_map[tr_key][-2]
    if not (price and crossed_up and rsi > 50 and obv_now > obv_prev):
        return
    print(f"[전략2] 조건 충족 → {tr_key}")
    entry_time = time.time()
    position_map[tr_key] = {
        "entry_price": price,
        "entry_time": entry_time,
        "strategy_id": 2,
        "qty": 1
    }
    submit_order(tr_key, price, strategy_id=2)
    mfe_mae_track_map[tr_key] = {
        "start_time": entry_time,
        "max_price": price,
        "min_price": price
    }
    position_map[tr_key]["_need_monitor"] = True

def start_monitor_strategy2(tr_key):
    try:
        price = position_map[tr_key]["entry_price"]
        entry_time = position_map[tr_key]["entry_time"]

        for _ in range(600):
            time.sleep(0.1)
            now = last_price_map.get(tr_key)
            bid1 = last_ask_price_map[tr_key].get("bid1", 0)

            if not now:
                continue
            if bid1 >= int(price * TP_RATIO):
                submit_sell_order(tr_key, 0, reason="익절", strategy_id=2, entry_time=entry_time)
                return
            if now <= int(price * SL_RATIO):
                submit_sell_order(tr_key, 0, reason="손절", strategy_id=2, entry_time=entry_time)
                return

        submit_sell_order(tr_key, 0, reason="시간청산", strategy_id=2, entry_time=entry_time)
    except Exception as e:
        print(f"[전략2 오류] {e}")

def strategy_3(tr_key):
    update_strategy_timestamp()
    if not 체결확인 or not 호가확인_map[tr_key] or not warmup_done_map[tr_key]:
        return
    if time.time() - warmup_start_time_map[tr_key] < 60:
        return
    if tr_key in position_map:
        if position_map[tr_key].pop("_need_monitor", False):
            Thread(target=start_monitor_strategy3, args=(tr_key,), daemon=True).start()
        return
    if vwap_volume_map[tr_key] <= 0 or "now" not in rsi_14_1min_map[tr_key]:
        return
    price = last_price_map.get(tr_key)
    vwap = vwap_price_volume_map[tr_key] / vwap_volume_map[tr_key]
    rsi = rsi_14_1min_map[tr_key]["now"]
    if not price or price > vwap * 0.99 or rsi >= 30:
        return
    print(f"[전략3] VWAP 괴리 + RSI 과매도 조건 충족 → {tr_key}")
    qty = 1
    entry_time = time.time()
    position_map[tr_key] = {
        "entry_price": price,
        "entry_time": entry_time,
        "strategy_id": 3,
        "qty": qty
    }
    submit_order(tr_key, price, strategy_id=3)
    mfe_mae_track_map[tr_key] = {
        "start_time": entry_time,
        "max_price": price,
        "min_price": price
    }
    position_map[tr_key]["_need_monitor"] = True

def start_monitor_strategy3(tr_key):
    try:
        price = position_map[tr_key]["entry_price"]
        entry_time = position_map[tr_key]["entry_time"]

        for _ in range(600):
            time.sleep(0.1)
            now = last_price_map.get(tr_key)
            bid1 = last_ask_price_map[tr_key].get("bid1", 0)

            if not now:
                continue
            if bid1 >= int(price * TP_RATIO):
                submit_sell_order(tr_key, 0, reason="익절", strategy_id=3, entry_time=entry_time)
                return
            if now <= int(price * SL_RATIO):
                submit_sell_order(tr_key, 0, reason="손절", strategy_id=3, entry_time=entry_time)
                return

        submit_sell_order(tr_key, 0, reason="시간청산", strategy_id=3, entry_time=entry_time)
    except Exception as e:
        print(f"[전략3 오류] {e}")

def strategy_4(tr_key):
    update_strategy_timestamp()
    if not 체결확인 or not 호가확인_map[tr_key] or not warmup_done_map[tr_key]:
        return
    if time.time() - warmup_start_time_map[tr_key] < 60:
        return
    if tr_key in position_map:
        if position_map[tr_key].pop("_need_monitor", False):
            Thread(target=start_monitor_strategy4, args=(tr_key,), daemon=True).start()
        return
    if len(candle_1min_map[tr_key]) < 20 or "now" not in rsi_14_1min_map[tr_key]:
        return
    df = pd.DataFrame(candle_1min_map[tr_key])[-20:]
    ema5 = df["close"].ewm(span=5).mean()
    ema20 = df["close"].ewm(span=20).mean()
    if not (ema5.iloc[-2] < ema20.iloc[-2] and ema5.iloc[-1] > ema20.iloc[-1]):
        return
    vwap = vwap_price_volume_map[tr_key] / vwap_volume_map[tr_key]
    price = last_price_map.get(tr_key)
    if not price or price < vwap or rsi_14_1min_map[tr_key]["now"] < 50:
        return
    print(f"[전략4] EMA 골든크로스 + VWAP 위 + RSI 50↑ → {tr_key}")
    qty = 1
    entry_time = time.time()
    position_map[tr_key] = {
        "entry_price": price,
        "entry_time": entry_time,
        "strategy_id": 4,
        "qty": qty
    }
    submit_order(tr_key, price, strategy_id=4)
    mfe_mae_track_map[tr_key] = {
        "start_time": entry_time,
        "max_price": price,
        "min_price": price
    }
    position_map[tr_key]["_need_monitor"] = True

def start_monitor_strategy4(tr_key):
    try:
        price = position_map[tr_key]["entry_price"]
        entry_time = position_map[tr_key]["entry_time"]

        for _ in range(600):
            time.sleep(0.1)
            now = last_price_map.get(tr_key)
            bid1 = last_ask_price_map[tr_key].get("bid1", 0)

            if not now:
                continue
            if bid1 >= int(price * TP_RATIO):
                submit_sell_order(tr_key, 0, reason="익절", strategy_id=4, entry_time=entry_time)
                return
            if now <= int(price * SL_RATIO):
                submit_sell_order(tr_key, 0, reason="손절", strategy_id=4, entry_time=entry_time)
                return

        submit_sell_order(tr_key, 0, reason="시간청산", strategy_id=4, entry_time=entry_time)
    except Exception as e:
        print(f"[전략4 오류] {e}")

def strategy_5(tr_key):
    update_strategy_timestamp()
    if (not 체결확인 or not 호가확인_map[tr_key] or not warmup_done_map[tr_key]):
        return
    if time.time() - warmup_start_time_map[tr_key] < 60:
        return
    if tr_key in position_map:
        if position_map[tr_key].pop("_need_monitor", False):
            Thread(target=start_monitor_strategy5, args=(tr_key,), daemon=True).start()
        return
    if len(candle_1min_map[tr_key]) < 10 or len(obv_map[tr_key]) < 10:
        return
    price = last_price_map.get(tr_key)
    highs = [c["high"] for c in candle_1min_map[tr_key][-10:]]
    rsi = rsi_14_1min_map[tr_key]["now"]
    vwap = vwap_price_volume_map[tr_key] / vwap_volume_map[tr_key]
    obv_now = obv_map[tr_key][-1]
    obv_max_prev = max(obv_map[tr_key][-10:-1])
    if (price < max(highs) * 0.995 or obv_now <= obv_max_prev or not (50 <= rsi <= 60) or price < vwap):
        return
    print(f"[전략5] 조건 충족 → {tr_key}")
    entry_time = time.time()
    position_map[tr_key] = {
        "entry_price": price,
        "entry_time": entry_time,
        "strategy_id": 5,
        "qty": 1
    }
    submit_order(tr_key, price, strategy_id=5)
    mfe_mae_track_map[tr_key] = {
        "start_time": entry_time,
        "max_price": price,
        "min_price": price
    }
    position_map[tr_key]["_need_monitor"] = True

def start_monitor_strategy5(tr_key):
    try:
        price = position_map[tr_key]["entry_price"]
        entry_time = position_map[tr_key]["entry_time"]

        for _ in range(600):
            time.sleep(0.1)
            now = last_price_map.get(tr_key)
            bid1 = last_ask_price_map[tr_key].get("bid1", 0)

            if not now:
                continue
            if bid1 >= int(price * TP_RATIO):
                submit_sell_order(tr_key, 0, reason="익절", strategy_id=5, entry_time=entry_time)
                return
            if now <= int(price * SL_RATIO):
                submit_sell_order(tr_key, 0, reason="손절", strategy_id=5, entry_time=entry_time)
                return

        submit_sell_order(tr_key, 0, reason="시간청산", strategy_id=5, entry_time=entry_time)
    except Exception as e:
        print(f"[전략5 오류] {e}")

def strategy_6(tr_key):
    update_strategy_timestamp()
    if (not 체결확인 or not 호가확인_map[tr_key] or not warmup_done_map[tr_key]):
        return
    if time.time() - warmup_start_time_map[tr_key] < 60:
        return
    if tr_key in position_map:
        if position_map[tr_key].pop("_need_monitor", False):
            Thread(target=start_monitor_strategy6, args=(tr_key,), daemon=True).start()
        return
    if (vwap_volume_map[tr_key] <= 0 or
        "now" not in rsi_14_1min_map[tr_key] or
        len(obv_map[tr_key]) < 2):
        return
    price = last_price_map.get(tr_key)
    vwap = vwap_price_volume_map[tr_key] / vwap_volume_map[tr_key]
    rsi = rsi_14_1min_map[tr_key]["now"]
    obv_now = obv_map[tr_key][-1]
    obv_prev = obv_map[tr_key][-2]
    if (not price or price > vwap * 0.995 or rsi > 30 or obv_now < obv_prev):
        return
    print(f"[전략6] 조건 충족 → {tr_key}")
    entry_time = time.time()
    position_map[tr_key] = {
        "entry_price": price,
        "entry_time": entry_time,
        "strategy_id": 6,
        "qty": 1
    }
    submit_order(tr_key, price, strategy_id=6)
    mfe_mae_track_map[tr_key] = {
        "start_time": entry_time,
        "max_price": price,
        "min_price": price
    }
    position_map[tr_key]["_need_monitor"] = True

def start_monitor_strategy6(tr_key):
    try:
        price = position_map[tr_key]["entry_price"]
        entry_time = position_map[tr_key]["entry_time"]

        for _ in range(600):
            time.sleep(0.1)
            now = last_price_map.get(tr_key)
            bid1 = last_ask_price_map[tr_key].get("bid1", 0)

            if not now:
                continue
            if bid1 >= int(price * TP_RATIO):
                submit_sell_order(tr_key, 0, reason="익절", strategy_id=6, entry_time=entry_time)
                return
            if now <= int(price * SL_RATIO):
                submit_sell_order(tr_key, 0, reason="손절", strategy_id=6, entry_time=entry_time)
                return

        submit_sell_order(tr_key, 0, reason="시간청산", strategy_id=6, entry_time=entry_time)
    except Exception as e:
        print(f"[전략6 오류] {e}")

def strategy_7(tr_key):
    update_strategy_timestamp()
    if (not 체결확인 or not 호가확인_map[tr_key] or not warmup_done_map[tr_key]):
        return
    if time.time() - warmup_start_time_map[tr_key] < 60:
        return
    if tr_key in position_map:
        if position_map[tr_key].pop("_need_monitor", False):
            Thread(target=start_monitor_strategy7, args=(tr_key,), daemon=True).start()
        return
    if len(candle_1min_map[tr_key]) < 20 or len(obv_map[tr_key]) < 2:
        return
    df = pd.DataFrame(candle_1min_map[tr_key])[-20:]
    ema5 = df["close"].ewm(span=5).mean()
    ema20 = df["close"].ewm(span=20).mean()
    cross_up = (ema5.iloc[-2] < ema20.iloc[-2]) and (ema5.iloc[-1] > ema20.iloc[-1])
    price = last_price_map.get(tr_key)
    vwap = vwap_price_volume_map[tr_key] / vwap_volume_map[tr_key]
    rsi = rsi_14_1min_map[tr_key]["now"]
    obv_now = obv_map[tr_key][-1]
    obv_prev = obv_map[tr_key][-2]
    if (not price or price < vwap or rsi < 50 or not cross_up or obv_now <= obv_prev):
        return
    print(f"[전략7] 조건 충족 → {tr_key}")
    entry_time = time.time()
    position_map[tr_key] = {
        "entry_price": price,
        "entry_time": entry_time,
        "strategy_id": 7,
        "qty": 1
    }
    submit_order(tr_key, price, strategy_id=7)
    mfe_mae_track_map[tr_key] = {
        "start_time": entry_time,
        "max_price": price,
        "min_price": price
    }
    position_map[tr_key]["_need_monitor"] = True

def start_monitor_strategy7(tr_key):
    try:
        price = position_map[tr_key]["entry_price"]
        entry_time = position_map[tr_key]["entry_time"]

        for _ in range(600):
            time.sleep(0.1)
            now = last_price_map.get(tr_key)
            bid1 = last_ask_price_map[tr_key].get("bid1", 0)

            if not now:
                continue
            if bid1 >= int(price * TP_RATIO):
                submit_sell_order(tr_key, 0, reason="익절", strategy_id=7, entry_time=entry_time)
                return
            if now <= int(price * SL_RATIO):
                submit_sell_order(tr_key, 0, reason="손절", strategy_id=7, entry_time=entry_time)
                return

        submit_sell_order(tr_key, 0, reason="시간청산", strategy_id=7, entry_time=entry_time)
    except Exception as e:
        print(f"[전략7 오류] {e}")

def strategy_8(tr_key):
    update_strategy_timestamp()
    if (not 체결확인 or not 호가확인_map[tr_key] or not warmup_done_map[tr_key]):
        return
    if time.time() - warmup_start_time_map[tr_key] < 60:
        return
    if tr_key in position_map:
        if position_map[tr_key].pop("_need_monitor", False):
            Thread(target=start_monitor_strategy8, args=(tr_key,), daemon=True).start()
        return
    if (len(close_1min_20_map[tr_key]) < 20 or
        "now" not in rsi_14_1min_map[tr_key] or
        len(obv_map[tr_key]) < 5):
        return
    price = last_price_map.get(tr_key)
    rsi = rsi_14_1min_map[tr_key]["now"]
    ma = ma_20_1min_map[tr_key]
    closes = list(close_1min_20_map[tr_key])
    std = (sum((c - ma) ** 2 for c in closes) / 20) ** 0.5
    lower = ma - 2 * std
    obv_now = obv_map[tr_key][-1]
    obv_min_5 = min(obv_map[tr_key][-5:-1])
    lows_5 = [c["low"] for c in candle_1min_map[tr_key][-5:]]
    if (not price or price > lower or rsi > 30 or lows_5[-1] >= min(lows_5[:-1]) or obv_now <= obv_min_5):
        return
    print(f"[전략8] 조건 충족 → {tr_key}")
    entry_time = time.time()
    position_map[tr_key] = {
        "entry_price": price,
        "entry_time": entry_time,
        "strategy_id": 8,
        "qty": 1
    }
    submit_order(tr_key, price, strategy_id=8)
    mfe_mae_track_map[tr_key] = {
        "start_time": entry_time,
        "max_price": price,
        "min_price": price
    }
    position_map[tr_key]["_need_monitor"] = True

def start_monitor_strategy8(tr_key):
    try:
        price = position_map[tr_key]["entry_price"]
        entry_time = position_map[tr_key]["entry_time"]

        for _ in range(600):
            time.sleep(0.1)
            now = last_price_map.get(tr_key)
            bid1 = last_ask_price_map[tr_key].get("bid1", 0)

            if not now:
                continue
            if bid1 >= int(price * TP_RATIO):
                submit_sell_order(tr_key, 0, reason="익절", strategy_id=8, entry_time=entry_time)
                return
            if now <= int(price * SL_RATIO):
                submit_sell_order(tr_key, 0, reason="손절", strategy_id=8, entry_time=entry_time)
                return

        submit_sell_order(tr_key, 0, reason="시간청산", strategy_id=8, entry_time=entry_time)
    except Exception as e:
        print(f"[전략8 오류] {e}")

def strategy_9(tr_key):
    update_strategy_timestamp()
    if (not 체결확인 or not 호가확인_map[tr_key] or not warmup_done_map[tr_key]):
        return
    if time.time() - warmup_start_time_map[tr_key] < 60:
        return
    if tr_key in position_map:
        if position_map[tr_key].pop("_need_monitor", False):
            Thread(target=start_monitor_strategy9, args=(tr_key,), daemon=True).start()
        return
    if len(candle_1min_map[tr_key]) < 10 or len(obv_map[tr_key]) < 10:
        return
    price = last_price_map.get(tr_key)
    highs = [c["high"] for c in candle_1min_map[tr_key][-10:]]
    rsi = rsi_14_1min_map[tr_key]["now"]
    vwap = vwap_price_volume_map[tr_key] / vwap_volume_map[tr_key]
    obv_now = obv_map[tr_key][-1]
    obv_max_prev = max(obv_map[tr_key][-10:-1])
    near_resistance = price >= max(highs) * 0.99
    if (not price or not near_resistance or obv_now <= obv_max_prev or not (50 <= rsi <= 60) or price < vwap):
        return
    if len(volume_3tick_map[tr_key]) < 5:
        return
    vol_5_avg = sum(volume_3tick_map[tr_key]) / 5
    if volume_3tick_map[tr_key][-1] < vol_5_avg * 1.5:
        return
    print(f"[전략9] 조건 충족 → {tr_key}")
    entry_time = time.time()
    position_map[tr_key] = {
        "entry_price": price,
        "entry_time": entry_time,
        "strategy_id": 9,
        "qty": 1
    }
    submit_order(tr_key, price, strategy_id=9)
    mfe_mae_track_map[tr_key] = {
        "start_time": entry_time,
        "max_price": price,
        "min_price": price
    }
    position_map[tr_key]["_need_monitor"] = True

def start_monitor_strategy9(tr_key):
    try:
        price = position_map[tr_key]["entry_price"]
        entry_time = position_map[tr_key]["entry_time"]

        for _ in range(600):
            time.sleep(0.1)
            now = last_price_map.get(tr_key)
            bid1 = last_ask_price_map[tr_key].get("bid1", 0)

            if not now:
                continue
            if bid1 >= int(price * TP_RATIO):
                submit_sell_order(tr_key, 0, reason="익절", strategy_id=9, entry_time=entry_time)
                return
            if now <= int(price * SL_RATIO):
                submit_sell_order(tr_key, 0, reason="손절", strategy_id=9, entry_time=entry_time)
                return

        submit_sell_order(tr_key, 0, reason="시간청산", strategy_id=9, entry_time=entry_time)
    except Exception as e:
        print(f"[전략9 오류] {e}")

def strategy_10(tr_key):
    update_strategy_timestamp()
    if not 체결확인 or not 호가확인_map[tr_key] or not warmup_done_map[tr_key]:
        return
    if time.time() - warmup_start_time_map[tr_key] < 60:
        return
    if tr_key in position_map:
        if position_map[tr_key].pop("_need_monitor", False):
            Thread(target=start_monitor_strategy10, args=(tr_key,), daemon=True).start()
        return
    price = last_price_map.get(tr_key)
    vwap = vwap_price_volume_map[tr_key] / vwap_volume_map[tr_key]
    rsi = rsi_14_1min_map[tr_key]["now"]
    if not price or abs(price - vwap) > price * 0.001 or not (40 <= rsi <= 50):
        return
    if len(obv_map[tr_key]) < 2:
        return
    if obv_map[tr_key][-1] < obv_map[tr_key][-2]:
        return
    print(f"[전략10] VWAP 눌림목 + RSI 반등 조건 충족 → {tr_key}")
    entry_time = time.time()
    position_map[tr_key] = {
        "entry_price": price,
        "entry_time": entry_time,
        "strategy_id": 10,
        "qty": 1
    }
    submit_order(tr_key, price, strategy_id=10)
    mfe_mae_track_map[tr_key] = {
        "start_time": entry_time,
        "max_price": price,
        "min_price": price
    }
    position_map[tr_key]["_need_monitor"] = True

def start_monitor_strategy10(tr_key):
    try:
        price = position_map[tr_key]["entry_price"]
        entry_time = position_map[tr_key]["entry_time"]

        for _ in range(600):
            time.sleep(0.1)
            now = last_price_map.get(tr_key)
            bid1 = last_ask_price_map[tr_key].get("bid1", 0)

            if not now:
                continue
            if bid1 >= int(price * TP_RATIO):
                submit_sell_order(tr_key, 0, reason="익절", strategy_id=10, entry_time=entry_time)
                return
            if now <= int(price * SL_RATIO):
                submit_sell_order(tr_key, 0, reason="손절", strategy_id=10, entry_time=entry_time)
                return

        submit_sell_order(tr_key, 0, reason="시간청산", strategy_id=10, entry_time=entry_time)
    except Exception as e:
        print(f"[전략10 오류] {e}")

def update_strategy_11_conditions() -> None:
    global strategy_11_conditions, latest_strategy_log_count

    TOP_N_FIELDS = 5

    files = glob.glob("logs/*.csv")
    logs = []
    for f in files:
        try:
            df = pd.read_csv(f)
            if "수익률(%)" in df.columns:
                logs.append(df)
        except Exception:
            continue
    if not logs:
        return

    df_all = pd.concat(logs, ignore_index=True)
    # ── 로그 수가 변하지 않았으면 재계산 생략 ──
    global latest_strategy_log_count
    if len(df_all) == latest_strategy_log_count:
        return
    # ✅ 수익률 컬럼 숫자화 (꼭 필요)
    df_all["수익률(%)"] = pd.to_numeric(df_all["수익률(%)"], errors="coerce")
    df_all = df_all.dropna(subset=["수익률(%)"])

    df_win = df_all[df_all["수익률(%)"] > 0]
    df_lose = df_all[df_all["수익률(%)"] <= 0]
    if len(df_win) < 10 or len(df_lose) < 10:
        return

    ignore = [
        "전략 이름", "종목코드", "종목명", "진입 시각", "진입가",
        "청산 시각", "청산가", "종료 사유", "수익률(%)", "MFE", "MAE",
        "3분 최고가", "3분 최저가", "시가", "고가", "저가", "종가",
        "현재 거래량", "10분 평균 거래량", "틱속도", "틱순매수", "체결강도", "체결량(3초)",
        "매수호가1", "매도호가1", "매수호가잔량", "매도호가잔량",
        "OrderFlowImbalance", "BidAskSpread", "호가 스프레드", 
        "BidAskRatio", "MarketDepthRatio", "SpreadSqueeze", "OrderBookDivIdx"
    ]
              
    num_cols = [c for c in df_all.select_dtypes(include=["float", "int"]).columns
                if c not in ignore]

    diffs = {}
    for col in num_cols:
        try:
            win_avg = df_win[col].mean()
            lose_avg = df_lose[col].mean()
            if pd.isna(win_avg) or pd.isna(lose_avg):
                continue
            if abs(lose_avg) < 1e-9:          # 0 Division 방지
                continue
            if win_avg > lose_avg:
                diffs[col] = ((win_avg - lose_avg) / abs(lose_avg), win_avg)
        except Exception:
            continue

    if not diffs:
        return

    prev_conditions = strategy_11_conditions.copy() if strategy_11_conditions else {}
    sorted_cols = sorted(diffs.items(), key=lambda x: x[1][0], reverse=True)[:TOP_N_FIELDS]
    strategy_11_conditions = {k: round(v[1], 4) for k, v in sorted_cols}

    if strategy_11_conditions != prev_conditions:
        print(f"[strategy_11 업데이트] 익절vs손절 기준 적용 (로그 {len(df_all)}건)")
        for k, v in strategy_11_conditions.items():
            print(f"  - {k} ≥ {v}")
        latest_strategy_log_count = len(df_all)

def strategy_11(tr_key: str) -> None:
    update_strategy_timestamp()
    if (not 체결확인 or not 호가확인_map[tr_key] or not warmup_done_map[tr_key]):
        return
    if time.time() - warmup_start_time_map[tr_key] < 60:
        return
    if tr_key in position_map:
        if position_map[tr_key].pop("_need_monitor", False):
            Thread(target=monitor_strategy_11, args=(tr_key,), daemon=True).start()
        return
    update_strategy_11_conditions()
    cond = strategy_11_conditions
    row = last_finalized_1min_map.get(tr_key)
    if not cond or not row:
        return
    for k, v in cond.items():
        val = row.get(k)
        try:
            val = float(val)
        except (TypeError, ValueError):
            return
        if math.isnan(val) or val < v:
            return
    entry_price = row["close"]
    entry_time = time.time()
    position_map[tr_key] = {
        "entry_price": entry_price,
        "entry_time": entry_time,
        "strategy_id": 11,
        "qty": 1
    }
    submit_order(tr_key, entry_price, strategy_id=11)
    mfe_mae_track_map[tr_key] = {
        "start_time": entry_time,
        "max_price": entry_price,
        "min_price": entry_price
    }
    position_map[tr_key]["_need_monitor"] = True

def monitor_strategy_11(tr_key: str) -> None:
    """
    3 분 동안 모니터링  
    ▸ +0.7 % 익절  
    ▸ –0.4 % 손절  
    ▸ 시간 만료 시 시장가 청산
    """
    try:
        info       = position_map[tr_key]
        price_in   = info["entry_price"]
        entry_time = info["entry_time"]

        for _ in range(180):                 # 3분 = 180초
            time.sleep(0.1)
            now = last_price_map.get(tr_key)
            bid1 = last_ask_price_map[tr_key].get("bid1", 0)

            if now is None:
                continue
            if bid1 >= int(price_in * TP_RATIO):
                submit_sell_order(tr_key, 0, reason="익절", strategy_id=11, entry_time=entry_time)
                return
            if now <= price_in * SL_RATIO:      # –0.4 %
                submit_sell_order(tr_key, 0, reason="손절",
                                  strategy_id=11, entry_time=entry_time)
                return

        submit_sell_order(tr_key, 0, reason="시간청산",
                          strategy_id=11, entry_time=entry_time)
    except Exception as e:
        print(f"[전략11 오류] {e}") 

def monitor_strategy_alive():
    while True:
        now = time.time()
        diff = now - last_strategy_check_ts
        if diff > 10:
            print(f"[경고] 전략 조건 체크가 {int(diff)}초 동안 멈춰 있음")
        elif int(diff) > 0:
            print(f"[모니터] 전략 조건 체크 정상 작동 중 ({int(diff)}초 전)")
        time.sleep(10)

def add_stock_realtime(code: str, name: str) -> None:
    global pending_subs
    """
    관심종목 등록 + 실시간 구독 요청을 ‘한 번만’ 큐에 넣는다.
    • WebSocket 연결 유무와 상관없이 무조건 subscribe_job_queue 로만 전송
      (즉시 전송 ❌ → 중복 위험 제거)
    """
    with state_lock:
        if code in interest_stocks:
            return
        interest_stocks.append(code)
        stock_name_map[code] = name

    if code in subscribed_codes or code in pending_subs:
        return            # 이미 요청-또는-완료 상태면 무시

    pending_subs.add(code)
    subscribe_job_queue.put(code)
    print(f"[대기] {code} 구독 요청 큐에 등록")
            
def subscribe_worker():
    global exec_subscribed   # ← 이거 꼭 필요함
    """
    subscribe_job_queue → WebSocket 로 실시간 구독을 직렬 처리
    • ‘pending_subs’ 로 중복 차단
    • 전송 직전에 subscribed_codes 에 미리 넣어 race condition 제거
    """
    while True:
        code = subscribe_job_queue.get()

        # 연결 확인 — 안 되어 있으면 뒤로 미룸
        if not (ws_instance and ws_instance.sock and ws_instance.sock.connected):
            time.sleep(0.5)
            subscribe_job_queue.put(code)
            subscribe_job_queue.task_done()
            continue

        if code in subscribed_codes:
            pending_subs.discard(code)
            subscribe_job_queue.task_done()
            continue

        tick_msg = {
            "header": {"approval_key": approval_key, "custtype": "P",
                       "tr_type": "1", "content-type": "utf-8"},
            "body": {"input": {"tr_id": TR_ID_TICK, "tr_key": code}}
        }
        ask_msg  = {
            "header": {"approval_key": approval_key, "custtype": "P",
                       "tr_type": "1", "content-type": "utf-8"},
            "body": {"input": {"tr_id": TR_ID_ASK,  "tr_key": code}}
        }

        try:
            subscribed_codes.add(code)
            ws_safe_send(json.dumps(tick_msg))
            time.sleep(0.25)
            ws_safe_send(json.dumps(ask_msg))

            # ✅ H0STCNI0은 단 1번만 전송
            if not exec_subscribed:
                execution_msg = {
                    "header": {
                        "approval_key": approval_key,
                        "custtype": "P",
                        "tr_type": "1",
                        "content-type": "utf-8"
                    },
                    "body": {
                        "input": {
                            "tr_id": "H0STCNI0",
                            "tr_key": config["my_userid"]
                        }
                    }
                }
                ws_safe_send(json.dumps(execution_msg))
                exec_subscribed = True

            time.sleep(0.25)
            print(f"[구독 완료] {code}")
        except Exception as e:
            print(f"[구독 실패] {code}: {e}")
            subscribed_codes.discard(code)
            subscribe_job_queue.put(code)  # 재시도
        finally:
            pending_subs.discard(code)
            subscribe_job_queue.task_done()

def tps_worker():
    while True:
        func = api_job_queue.get()
        try:
            func()
        except Exception as e:
            print(f"[TPS 처리 실패] {e}")
        time.sleep(0.2)

Thread(target=tps_worker, daemon=True).start()

Thread(target=subscribe_worker, daemon=True).start()

@lru_cache(maxsize=2048)
def _cached_prev_close(code: str, ymd: str) -> int:
    time.sleep(0.12)
    url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/quotations/inquire-price"
    headers = {
        "Content-Type": "application/json; charset=utf-8",
        "authorization": f"Bearer {get_access_token()}",
        "appkey": APP_KEY,
        "appsecret": APP_SECRET,
        "tr_id": "FHKST01010100",
        "custtype": "P"
    }
    params = {
        "fid_cond_mrkt_div_code": "J",
        "fid_input_iscd": code
    }
    data, err = call_api("GET", url, headers=headers, params=params)
    if err:
        print(f"[ERROR] 전일 종가 조회 실패: {err}")
        return 0
    기준가 = data.get("output", {}).get("stck_sdpr", "")
    return int(기준가) if 기준가.isdigit() else 0

def get_prev_close(code: str) -> int:
    return _cached_prev_close(code, datetime.date.today().strftime("%Y%m%d"))

def fetch_cur_price(code: str) -> int | None:
    """REST 현재가 조회 (실제 가격 확인용)"""
    url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/quotations/inquire-price"
    headers = {
        "Content-Type": "application/json; charset=utf-8",
        "authorization": f"Bearer {get_access_token()}",
        "appkey": APP_KEY,
        "appsecret": APP_SECRET,
        "tr_id": "FHKST01010100",
        "custtype": "P"
    }
    params = {
        "fid_cond_mrkt_div_code": "J",
        "fid_input_iscd": code
    }

    data, err = call_api("GET", url, headers=headers, params=params)
    if err:
        print(f"[검증] REST 현재가 조회 실패: {err}")
        return None

    try:
        return int(data["output"]["stck_prpr"])
    except:
        print("[검증] 현재가 응답값 파싱 실패")
        return None

def load_interest_stocks_from_hts():
    """
    HTS 사용자 관심그룹(001 이상) 종목을 불러와 interest_stocks 에 등록.
    stocks.txt 의존성을 완전히 제거한다.
    """
    try:
        bearer = f"Bearer {get_access_token()}"

        # ① 관심 그룹 목록 조회
        url_grp = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/quotations/intstock-grouplist"
        headers = {
            "Content-Type": "application/json; charset=utf-8",
            "authorization": bearer,
            "appkey":  APP_KEY,
            "appsecret": APP_SECRET,
            "custtype": "P",
            "gt_uid":  uuid.uuid4().hex,
            "tr_id":   "HHKCM113004C7"
        }
        params_grp = {"TYPE": "1", "FID_ETC_CLS_CODE": "00", "USER_ID": HTS_ID}
        data, err = call_api("GET", url_grp, headers=headers, params=params_grp)
        if err:
            print(f"[ERROR] 관심 그룹 조회 실패: {err}")
            return

        groups = data.get("output2", [])
        user_grp = next((g for g in groups if g.get("inter_grp_code") != "000"), None)
        if not user_grp:
            print("[INFO] 사용자 관심그룹(001+)이 없습니다.")
            return

        grp_code = user_grp["inter_grp_code"]
        grp_name = user_grp["inter_grp_name"]
        print(f"[관심그룹] {grp_code} ({grp_name}) 선택")

        # ② 그룹별 종목 목록 조회
        headers["tr_id"] = "HHKCM113004C6"
        headers["gt_uid"] = uuid.uuid4().hex
        url_stk = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/quotations/intstock-stocklist-by-group"
        params_stk = {
            "TYPE": "1",
            "USER_ID": HTS_ID,
            "INTER_GRP_CODE": grp_code,
            "DATA_RANK": "",
            "INTER_GRP_NAME": "",
            "HTS_KOR_ISNM": "",
            "CNTG_CLS_CODE": "",
            "FID_ETC_CLS_CODE": "4"
        }
        data2, err2 = call_api("GET", url_stk, headers=headers, params=params_stk)
        if err2:
            print(f"[ERROR] 관심 종목 조회 실패: {err2}")
            return

        stocks = data2.get("output2", [])
        if not stocks:
            print(f"[INFO] 그룹 {grp_code} 종목이 없습니다.")
            return

        for s in stocks:
            code = s.get("stck_shrn_iscd") or s.get("jong_code")      # 
            name = s.get("hts_kor_isnm")
            if code and name:
                add_stock_realtime(code, name)

        print(f"[관심종목] {len(stocks)}개 종목 등록 완료")

    except Exception as e:
        print(f"[ERROR] HTS 관심종목 로드 실패: {e}")
        
# ----------------------------------
# [오늘 1분봉 선로딩]
# ----------------------------------
def fetch_today_1min(code: str):
    import datetime

    url = f"{REAL_DOMAIN}/uapi/domestic-stock/v1/quotations/inquire-time-dailychartprice"
    headers = {
        "Content-Type": "application/json; charset=utf-8",
        "authorization": f"Bearer {get_access_token()}",
        "appkey": APP_KEY,
        "appsecret": APP_SECRET,
        "tr_id": "FHKST03010230",
        "custtype": "P"
    }
    now = datetime.datetime.now()
    params = {
        "FID_COND_MRKT_DIV_CODE": "J",
        "FID_INPUT_ISCD": code,
        "FID_INPUT_DATE_1": now.strftime("%Y%m%d"),
        "FID_INPUT_HOUR_1": now.strftime("%H%M%S"),
        "FID_PW_DATA_INCU_YN": "Y",
        "FID_FAKE_TICK_INCU_YN": "N"
    }

    try:
        res = requests.get(url, headers=headers, params=params, timeout=10)
        data = res.json()
        recs = data.get("output2", [])
        if not recs:
            print(f"[초기로드] {code}: 데이터 없음")
            return

        for rec in recs:
            hhmmss = rec["stck_cntg_hour"]
            t_min  = int(hhmmss[:2]) * 60 + int(hhmmss[2:4])
            o = int(rec["stck_oprc"]);  h = int(rec["stck_hgpr"])
            l = int(rec["stck_lwpr"]);  c = int(rec["stck_prpr"])
            v = int(rec["cntg_vol"])

            candle_1min_map[code].append({
                "time": t_min, "open": o, "high": h,
                "low": l, "close": c, "volume": v
            })
            close_1min_20_map[code].append(c)
            high_1min_map[code].append(h)
            vwap_price_volume_map[code] += c * v
            vwap_volume_map[code]       += v

        # ✅ 1분봉 지표 계산
        closes = [c["close"] for c in list(candle_1min_map[code])]
        if len(closes) >= 15:
            deltas = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
            gains = [d for d in deltas if d > 0]
            losses = [-d for d in deltas if d < 0]
            avg_gain = sum(gains) / 14 if gains else 0
            avg_loss = sum(losses) / 14 if losses else 0
            if avg_loss != 0:
                rs = avg_gain / avg_loss
                rsi_14_1min_map[code]["now"] = 100 - (100 / (1 + rs))

        if len(closes) >= 20:
            ma = sum(closes[-20:]) / 20
            ma_20_1min_map[code] = ma
            std = (sum((c - ma) ** 2 for c in closes[-20:]) / 20) ** 0.5
            close_1min_20_map[code] = deque(closes[-20:], maxlen=20)

        # ✅ 3분봉 생성
        one_min_list = list(candle_1min_map[code])
        candle_3min_map[code].clear()
        for i in range(0, len(one_min_list) - 2, 3):
            m1, m2, m3 = one_min_list[i:i+3]
            candle_3min_map[code].append({
                "open": m1["open"],
                "high": max(m1["high"], m2["high"], m3["high"]),
                "low":  min(m1["low"],  m2["low"],  m3["low"]),
                "close": m3["close"],
                "volume": m1["volume"] + m2["volume"] + m3["volume"]
            })

        # ✅ 3분봉 지표 계산
        closes_3 = [c["close"] for c in list(candle_3min_map[code])]
        if len(closes_3) >= 15:
            deltas = [closes_3[i] - closes_3[i - 1] for i in range(1, len(closes_3))]
            gains = [d for d in deltas if d > 0]
            losses = [-d for d in deltas if d < 0]
            avg_gain = sum(gains) / 14 if gains else 0
            avg_loss = sum(losses) / 14 if losses else 0
            if avg_loss != 0:
                rs = avg_gain / avg_loss
                rsi_14_3min_map[code]["now"] = 100 - (100 / (1 + rs))

        if len(closes_3) >= 20:
            ma = sum(closes_3[-20:]) / 20
            ma_20_3min_map[code] = ma
            std = (sum((c - ma) ** 2 for c in closes_3[-20:]) / 20) ** 0.5
            close_3min_20_map[code] = deque(closes_3[-20:], maxlen=20)

        # ✅ 추가 계산: 1분봉 평균 거래량(10봉)
        if len(candle_1min_map[code]) >= 10:
            avg_1min_vol = sum(c["volume"] for c in list(candle_1min_map[code])[-10:]) / 10

        # ✅ 추가 계산: 최근 5분 고가
        if len(candle_1min_map[code]) >= 5:
            recent_high = max(c["high"] for c in list(candle_1min_map[code])[-5:])

        if candle_1min_map[code]:
            snapshot = snapshot_row_for_strategy11(code)
            snapshot.update(candle_1min_map[code][-1])
            last_finalized_1min_map[code] = snapshot
            cur_volume_map[code] = candle_1min_map[code][-1]["volume"]
            last_price_map[code] = candle_1min_map[code][-1]["close"]

    except Exception as e:
        print(f"[초기로드 실패] {code}: {e}")

    # ✅ 이 부분은 try 바깥에 있어야 한다
    while len(candle_1min_map[code]) < 20:
        print(f"[보강] {code}: 1분봉 부족({len(candle_1min_map[code])}개) → 0.2초 대기 후 재확인")
        time.sleep(0.2)
    
    print(f"[DEBUG] {code} 캔들 확보 완료 → {len(candle_1min_map[code])}개 수신됨")
# ----------------------------------
# [WebSocket 시작]
# ----------------------------------
def start_websocket():
    """
    WebSocket 세션 시작
      • approval_key 발급
      • 관심종목 선로딩
      • on_open()에서 캐시만 초기화
        (실제 구독은 subscribe_worker 가 큐를 순차 처리)
    """
    global ws_instance, approval_key

    # ① 승인키
    approval_key = get_approval_key()

    # ② 관심종목 등록 + 1분봉 선로딩
    load_interest_stocks_from_hts()
    for c in interest_stocks:
        fetch_today_1min(c)

    # ③ WebSocket 연결
    def on_open(ws):
        print("[on_open] WebSocket 연결 성공")
        subscribed_codes.clear()           # 서버가 기억하는 구독 초기화에 맞춰 리셋
        # 큐는 비우지 않는다 ― 이미 담긴 종목을 워커가 순차 처리

    ws = websocket.WebSocketApp(
        WS_URL,
        on_open=on_open,
        on_message=on_message,
        on_error=on_error,
        on_close=on_close,
    )
    ws_instance = ws
    ws.run_forever()                       # PINGPONG echo 로 keep-alive

    def _keep_alive():
        while True:
            try:
                if ws_instance and ws_instance.sock and ws_instance.sock.connected:
                    ws_safe_send("PING")
            except Exception:
                pass
            time.sleep(30)
    Thread(target=_keep_alive, daemon=True).start()
    
def graceful_shutdown():
    save_positions()
    print("[종료 처리] 프로그램 종료 중...")
    try:
        if ws_instance:
            ws_instance.close()
            print("[종료 처리] WebSocket 닫힘")
    except:
        pass

    with state_lock:
        position_map.clear()
        interest_stocks.clear()
        strategy_queue.clear()
        print("[종료 처리] 메모리 초기화 완료")

atexit.register(graceful_shutdown)

def handle_signal(sig, frame):
    print(f"[종료 처리] signal {sig} 수신됨 → 종료 중")
    sys.exit(0)

signal.signal(signal.SIGINT, handle_signal)
signal.signal(signal.SIGTERM, handle_signal)
    
# ----------------------------------
# [실행]
# ----------------------------------
if __name__ == "__main__":
    last_strategy_check_ts = time.time()  # ✅ 전략체크 시각 초기화

    print(f"[실행시각] {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')} 프로그램 시작")

    restore_position_from_balance()
    schedule_liquidation()

    # ✅ 모든 필수 워커 스레드 실행
    Thread(target=interest_sync_worker, daemon=True).start()
    Thread(target=daily_reset_worker, daemon=True).start()
    Thread(target=start_websocket, daemon=True).start()
    Thread(target=initial_1min_loader, daemon=True).start()
    Thread(target=monitor_strategy_alive, daemon=True).start()
    Thread(target=thread_pool_watchdog, daemon=True).start()

    while True:
        time.sleep(10)
