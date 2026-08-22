import os
import threading
import queue as q
import time
import numpy as np
import sounddevice as sd
import requests
import json
import base64
import hmac
import struct
import websocket
import signal
import sys
import logging
import urllib.parse
from datetime import datetime, timedelta
from time import mktime
from wsgiref.handlers import format_date_time
from flask import Flask, request, jsonify, Response
from flask_socketio import SocketIO, join_room, leave_room
import re
import secrets
import qrcode
import io
import hashlib
import fitz  # PyMuPDF
from collections import Counter, OrderedDict
from concurrent.futures import ThreadPoolExecutor
from collections import deque
import difflib

STUDENTS = {}
ATTENDANCE = {}
ACTIVE_SESSION_CODES = {}
VERIFIED_STUDENTS = {}
CONNECTED_CLIENTS = set()
PHRASE_COUNT = 0
CURRENT_SESSION_CODE = None
CODE_EXPIRES_AT = 0

# НОВЫЕ ПЕРЕМЕННЫЕ
LAST_SEGMENTS = []
LAST_SEGMENT_TIME = time.time()
REPAIR_CACHE = OrderedDict()
PERF_METRICS = {
    'translation_times': [],
    'recognition_times': [],
    'errors': Counter(),
}

# ================= Хранилище полной истории лекции =================
LECTURE_HISTORY = []
LECTURE_INDEX = {}
MAX_HISTORY_SIZE = 10000
USER_SESSIONS = {}

# Logging configuration
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Load environment variables
from dotenv import load_dotenv
# override=True: файл .env всегда имеет приоритет над переменными окружения.
# Иначе если в shell уже экспортирован старый DEEPSEEK_API_KEY, python-dotenv
# его не перезапишет и приложение будет работать с невалидным ключом (401).
load_dotenv(override=True)

# ================= Graceful shutdown =================
def signal_handler(sig, frame):
    global is_running
    logger.info("\n🛑 Received termination signal...")
    
    if 'LECTURE_HISTORY' in globals() and LECTURE_HISTORY:
        try:
            filename = f"lecture_final_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
            with open(filename, "w", encoding="utf-8") as f:
                json.dump({
                    "generated": datetime.now().isoformat(),
                    "total_entries": len(LECTURE_HISTORY),
                    "history": LECTURE_HISTORY
                }, f, indent=2, ensure_ascii=False)
            logger.info(f"💾 Final lecture saved to {filename}")
        except Exception as e:
            logger.error(f"Final save error: {e}")
    
    is_running = False
    time.sleep(1)
    logger.info("✅ Server stopped")
    sys.exit(0)

# ================= Configuration =================
APPID = os.getenv("XF_APPID", "ga88408f")
APIKey = os.getenv("XF_API_KEY", "")
APISecret = os.getenv("XF_API_SECRET", "")
# Endpoint SG-региона iFLYTEK: активирован сервис "Short Form ASR" (ws://iat-api-sg.xf-yun.com/v2/iat)
WS_URL = "ws://iat-api-sg.xf-yun.com/v2/iat"
# Шлюз iFLYTEK-SG живёт в GMT+3; для корректной HMAC-подписи дату нужно сдвигать на +3ч
XF_SG_TIME_OFFSET = 3

# ПАРАМЕТРЫ ОПТИМИЗАЦИИ
ENABLE_REALTIME = True
SHOW_INTERMEDIATE = True
MIN_TEXT_LENGTH = 1
SEND_INTERVAL = 0.3
FINAL_TIMEOUT = 1.5
MIN_WORDS_FOR_FINAL = 2
MAX_INTERMEDIATE_AGE = 3.0

DEEPSEEK_API_KEY = os.getenv("DEEPSEEK_API_KEY")
DEEPSEEK_URL = "https://api.deepseek.com/v1/chat/completions"

# Пул потоков для DeepSeek (увеличен для параллельных переводов нескольким клиентам)
deepseek_executor = ThreadPoolExecutor(max_workers=8)

# Переиспользуемое HTTP-соединение к DeepSeek (keep-alive: быстрее, чем новый TCP+TLS каждый раз)
_deepseek_session = requests.Session()

# ================= НАСТРОЙКИ ТРАНСЛЯЦИИ =================
SCREEN_SHARE_FPS = 15
SCREEN_SHARE_QUALITY = 85
SCREEN_SHARE_MAX_WIDTH = 1280
SCREEN_SHARE_MAX_HEIGHT = 720

# ================= TURN / STUN (WebRTC) =================
# Учётные данные берутся из .env, а не хардкодятся в HTML
TURN_USERNAME = os.getenv("TURN_USERNAME", "50dc17955496d0b5b1c40f74")
TURN_CREDENTIAL = os.getenv("TURN_CREDENTIAL", "RRu50O/yhCb7qtqb")
TURN_URLS = [
    u.strip() for u in os.getenv(
        "TURN_URLS",
        "turn:global.relay.metered.ca:80,"
        "turn:global.relay.metered.ca:80?transport=tcp,"
        "turn:global.relay.metered.ca:443,"
        "turns:global.relay.metered.ca:443?transport=tcp"
    ).split(",") if u.strip()
]
STUN_URLS = [
    'stun:stun.l.google.com:19302',
    'stun:stun1.l.google.com:19302',
    'stun:stun2.l.google.com:19302',
    'stun:stun3.l.google.com:19302',
    'stun:stun4.l.google.com:19302',
    'stun:stun.relay.metered.ca:80',
]

# Собираем JSON-конфигурацию ICE, которую подставляем в HTML-разметку
def build_ice_servers_json():
    ice_servers = [{"urls": u} for u in STUN_URLS]
    if TURN_USERNAME and TURN_CREDENTIAL:
        for url in TURN_URLS:
            ice_servers.append({
                "urls": url,
                "username": TURN_USERNAME,
                "credential": TURN_CREDENTIAL
            })
    return json.dumps(ice_servers)

ICE_SERVERS_JSON = build_ice_servers_json()

# ================= Math Terms Dictionary =================
MATH_TERMS_EN = {
    "plus": "+", "add": "+", "addition": "+",
    "minus": "-", "subtract": "-", "subtraction": "-",
    "times": "×", "multiply": "×", "multiplication": "×",
    "divided by": "÷", "divide": "÷", "division": "÷",
    "equals": "=", "equal": "=",
    "not equal": "≠", "does not equal": "≠",
    "approximately": "≈", "approx": "≈",
    "greater than": ">",
    "less than": "<",
    "greater than or equal": "≥",
    "less than or equal": "≤",
    "squared": "²", "square": "²", "to the power of 2": "²",
    "cubed": "³", "cube": "³", "to the power of 3": "³",
    "to the fourth": "⁴", "to the 4th power": "⁴",
    "to the fifth": "⁵", "to the 5th power": "⁵",
    "to the power": "^", "power": "^",
    "square root": "√", "sqrt": "√",
    "cube root": "∛",
    "fourth root": "∜",
    "absolute value": "|x|", "absolute": "|x|",
    "factorial": "!",
    "sum": "∑", "summation": "∑",
    "product": "∏",
    "element of": "∈", "belongs to": "∈",
    "not element of": "∉",
    "subset of": "⊆",
    "proper subset": "⊂",
    "empty set": "∅",
    "limit": "lim",
    "derivative": "d/dx",
    "partial derivative": "∂",
    "gradient": "∇",
    "laplacian": "Δ",
    "integral": "∫",
    "double integral": "∬",
    "triple integral": "∭",
    "line integral": "∮",
    "infinity": "∞",
    "sine": "sin", "sin": "sin",
    "cosine": "cos", "cos": "cos",
    "tangent": "tan", "tan": "tan",
    "cotangent": "cot",
    "secant": "sec",
    "cosecant": "csc",
    "arcsine": "arcsin",
    "arccosine": "arccos",
    "arctangent": "arctan",
    "logarithm": "log", "log": "log",
    "natural log": "ln",
    "common log": "lg",
    "base": "log_",
    "angle": "∠",
    "right angle": "⊥",
    "parallel": "∥",
    "not parallel": "∦",
    "similar": "∼",
    "congruent": "≅",
    "triangle": "△",
    "circle": "⊙",
    "arc": "⌒",
    "degrees": "°",
    "minutes": "'",
    "seconds": '"',
    "pi": "π",
    "lowercase pi": "π",
    "e": "e",
    "intersection": "∩",
    "union": "∪",
    "complement": "∁",
    "real numbers": "ℝ",
    "rational numbers": "ℚ",
    "integers": "ℤ",
    "natural numbers": "ℕ",
    "complex numbers": "ℂ",
    "and": "∧",
    "or": "∨",
    "not": "¬",
    "implies": "→",
    "if and only if": "↔", "iff": "↔",
    "for all": "∀",
    "there exists": "∃",
    "does not exist": "∄",
    "vector": "→",
    "cross product": "×",
    "dot product": "·",
    "transpose": "ᵀ",
    "conjugate": "̄",
    "hermitian": "†",
    "gamma": "Γ",
    "beta": "Β",
    "delta": "Δ",
    "theta": "Θ",
    "lambda": "Λ",
    "xi": "Ξ",
    "uppercase pi": "Π",
    "sigma": "Σ",
    "phi": "Φ",
    "psi": "Ψ",
    "omega": "Ω",
    "subscript": "_",
    "superscript": "^",
    "zero power": "⁰",
    "first power": "¹",
    "second power": "²",
    "third power": "³",
    "fourth power": "⁴",
    "fifth power": "⁵",
    "sixth power": "⁶",
    "seventh power": "⁷",
    "eighth power": "⁸",
    "ninth power": "⁹",
    "over": "/", "fraction": "/",
    "parentheses": "()",
    "brackets": "[]",
    "braces": "{}",
    "approaches": "→",
    "tends to": "→",
    "goes to": "→",
    "from to": "-",
}

# ================= Функция добавления в историю =================
def add_to_lecture_history(text, text_type='recognition', language='zh', 
                          translation=None, speaker='teacher', metadata=None):
    global LECTURE_HISTORY, LECTURE_INDEX
    
    if not hasattr(add_to_lecture_history, "counter"):
        add_to_lecture_history.counter = 0
    
    entry = {
        'id': add_to_lecture_history.counter,
        'text': text,
        'timestamp': time.time(),
        'datetime': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
        'speaker': speaker,
        'type': text_type,
        'language': language,
        'translation': translation,
        'metadata': metadata or {}
    }
    
    LECTURE_HISTORY.append(entry)
    LECTURE_INDEX[entry['id']] = entry
    add_to_lecture_history.counter += 1
    
    if len(LECTURE_HISTORY) > MAX_HISTORY_SIZE:
        # Пакетная очистка вместо O(n) pop(0) на каждую запись:
        # срезаем сразу всё превышение (обычно 1 запись, при скачках — больше),
        # чтобы амортизировать стоимость и держать список в пределах лимита.
        overflow = len(LECTURE_HISTORY) - MAX_HISTORY_SIZE
        removed = LECTURE_HISTORY[:overflow]
        del LECTURE_HISTORY[:overflow]
        for old_entry in removed:
            if old_entry['id'] in LECTURE_INDEX:
                del LECTURE_INDEX[old_entry['id']]
    
    return entry['id']

# ================= Helper functions =================
TEXTBOOKS = {}
ACTIVE_TEXTBOOKS = set()

def load_textbook_terms(pdf_path, textbook_id=None):
    if textbook_id is None:
        textbook_id = os.path.basename(pdf_path)

    logger.info(f"📘 Loading textbook: {pdf_path}")

    doc = fitz.open(pdf_path)
    text = ""

    for page in doc:
        text += page.get_text()

    candidates = re.findall(
        r'[A-Za-z]{1,10}\([^)]+\)|'
        r'[A-Za-z]{2,10}|'
        r'[\u4e00-\u9fff]{2,6}|'
        r'[0-9]+[a-zA-Z]+|'
        r'[a-zA-Z]+\^[0-9]+|'
        r'√[a-zA-Z0-9]+|'
        r'∫|∑|∏|lim|sin|cos|tan|log|ln',
        text
    )

    freq = Counter(candidates)

    terms = {
        term for term, count in freq.items()
        if count >= 3 and len(term) <= 15
    }
    
    terms.update(MATH_TERMS_EN.values())

    TEXTBOOKS[textbook_id] = {
        "name": os.path.basename(pdf_path),
        "terms": terms,
        "loaded_at": time.time()
    }

    ACTIVE_TEXTBOOKS.add(textbook_id)

    logger.info(f"📗 {textbook_id}: Terms count {len(terms)} (including formulas)")

def float32_to_pcm16(audio):
    if len(audio) == 0:
        return b''
    return (audio * 32767).astype(np.int16).tobytes()

def generate_session_code():
    global CURRENT_SESSION_CODE, CODE_EXPIRES_AT

    timestamp = int(time.time() / 45)
    secret = os.getenv("SESSION_SECRET", "lecture_secret_2024")

    CURRENT_SESSION_CODE = hashlib.sha256(
        f"{secret}_{timestamp}".encode()
    ).hexdigest()[:6].upper()

    CODE_EXPIRES_AT = time.time() + 45

    ACTIVE_SESSION_CODES.clear()
    ACTIVE_SESSION_CODES[CURRENT_SESSION_CODE] = {
        "expires": CODE_EXPIRES_AT,
        "used_by": []
    }

    return CURRENT_SESSION_CODE

def verify_student_code(student_id, code):
    code = code.upper().strip()
    
    if code not in ACTIVE_SESSION_CODES:
        return False, "Code expired or invalid"
    
    code_data = ACTIVE_SESSION_CODES[code]
    
    if time.time() > code_data["expires"]:
        del ACTIVE_SESSION_CODES[code]
        return False, "Code expired"
    
    if student_id in code_data["used_by"]:
        if student_id in VERIFIED_STUDENTS and VERIFIED_STUDENTS[student_id].get("verified"):
            return True, "Already verified"
        else:
            return True, "Already verified"
    
    code_data["used_by"].append(student_id)
    
    VERIFIED_STUDENTS[student_id] = {
        "verified": True,
        "verified_at": time.time(),
        "session_code": code,
        "expires_at": code_data["expires"] + 3600
    }
    
    return True, "Verification successful"

def build_auth_url():
    host = "iat-api-sg.xf-yun.com"
    path = "/v2/iat"
    
    # ВАЖНО: шлюз iFLYTEK-SG (kong) живёт в GMT+3 и отклоняет подписи с датой
    # по UTC (403 "HMAC signature cannot be verified"). Сдвиг +3ч компенсирует
    # расхождение часов шлюза (проверено: +0h -> 403, +3h -> подпись принята).
    now = datetime.now() + timedelta(hours=XF_SG_TIME_OFFSET)
    date = format_date_time(mktime(now.timetuple()))
    
    signature_origin = f"host: {host}\ndate: {date}\nGET {path} HTTP/1.1"
    
    signature_hmac = hmac.new(
        APISecret.encode('utf-8'),
        signature_origin.encode('utf-8'),
        hashlib.sha256
    ).digest()
    
    signature_sha = base64.b64encode(signature_hmac).decode('utf-8')
    
    authorization_origin = f'api_key="{APIKey}", algorithm="hmac-sha256", headers="host date request-line", signature="{signature_sha}"'
    authorization = base64.b64encode(authorization_origin.encode('utf-8')).decode('utf-8')
    
    url_params = {
        "host": host,
        "date": date,
        "authorization": authorization
    }
    
    query_string = urllib.parse.urlencode(url_params)
    url = f"ws://{host}{path}?{query_string}"
    
    return url

# ================= Flask + SocketIO =================
app = Flask(__name__)
socketio = SocketIO(app, 
                    cors_allowed_origins="*",
                    async_mode='threading',
                    logger=True,
                    engineio_logger=False)

# ================= Global variables =================
audio_queue = q.Queue(maxsize=100)
clients_lang = {}
FULL_LECTURE_TEXT = []
translation_cache = OrderedDict()
MAX_CACHE = 1000
ws_connection = None
is_running = True
# Активна ли текущая сессия распознавания iFLYTEK. Сервер Short Form ASR сам
# финализирует сессию по VAD (тишина ~10-11с), присылая status:2 (часто с пустым
# текстом). После этого слать в сокет нельзя — сервер отвечает "invalid handle" и
# закрывает соединение с "server read msg timeout". Флаг сбрасывается в on_open
# при каждом новом подключении и ставится False в on_message при завершении сессии.
xf_session_active = True

# ================= Переменные для трансляции экрана =================
current_teacher_sid = None
TEACHER_ROOM = "teacher_room"
STUDENTS_ROOM = "students_room"

# ================= Статистика трансляции =================
screen_share_stats = {
    'total_frames_sent': 0,
    'total_frames_dropped': 0,
    'active_viewers': set(),
    'frame_times': deque(maxlen=100)
}

# ================= ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ =================
def log_performance(metric_name, value):
    if metric_name in PERF_METRICS:
        PERF_METRICS[metric_name].append(value)
        if len(PERF_METRICS[metric_name]) > 100:
            PERF_METRICS[metric_name].pop(0)

def normalize_numbers(text):
    # Склейка цифр, разорванных распознаванием: "1 2 3" -> "123".
    # Lookahead (?=\d) не поглощает вторую цифру, поэтому цепочки >2 цифр
    # склеиваются целиком, а не по парам ("12 3" вместо "123").
    text = re.sub(r'(\d)\s+(?=\d)', r'\1', text)
    # Десятичные точки: распознавание часто вставляет пробел: "3. 14" -> "3.14",
    # "3 .14" -> "3.14". После запятой-разделителя тоже.
    text = re.sub(r'(\d)\s*\.\s*(?=\d)', r'\1.', text)
    text = re.sub(r'(\d)\.\s*(?=\d)', r'\1.', text)
    return text

def post_process_translation(text):
    duplicates = [
        ('等于于', '等于'),
        ('的的', '的'),
        ('了了', '了'),
        ('，，', ','),
        ('。。', '.'),
        ('  ', ' '),
    ]
    
    for wrong, correct in duplicates:
        text = text.replace(wrong, correct)
    
    math_fixes = [
        ('e(', 'f('),
        ('两档Y', '→'),
        ('伊普西龙', 'ε'),
        ('德尔塔', 'δ'),
    ]
    
    for wrong, correct in math_fixes:
        text = text.replace(wrong, correct)
    
    # Контекстная замена "V" -> "=": только когда рядом есть математический контекст
    # (признаки формулы), чтобы не портить обычные буквы V в тексте.
    math_context = re.compile(
        r'([0-9a-zA-Zεδπ∞]\s*V\s*[0-9a-zA-Zεδπ∞])'
        r'|(V\s*[+\-×÷=<>≤≥])\s*|([+\-×÷=<>≤≥]\s*V)',
        re.IGNORECASE
    )
    text = math_context.sub(lambda m: m.group(0).replace('V', '=').replace('v', '='), text)
    
    return text

# ================= ИСПРАВЛЕННАЯ ФУНКЦИЯ WebSocket handler =================
def on_message(ws, message):
    global PHRASE_COUNT, LAST_SEGMENT_TIME, LAST_SEGMENTS, xf_session_active
    try:
        data = json.loads(message)
        
        if data.get('code') == 0:
            result_data = data.get('data', {})
            result = result_data.get('result', {})
            
            if result and 'ws' in result:
                text_parts = []
                for ws_item in result['ws']:
                    for cw in ws_item.get('cw', []):
                        text_parts.append(cw.get('w', ''))
                
                text = ''.join(text_parts)
                status = result_data.get('status')
                
                # iFLYTEK Short Form ASR сам завершает сессию по VAD (тишина):
                # status:2 — конец сессии, дальше слать аудио нельзя (иначе
                # сервер отвечает "invalid handle" и закрывает сокет). Перестаём
                # слать и переподключаемся для следующей фразы.
                if status == 2:
                    xf_session_active = False
                    logger.info("🔁 iFLYTEK session finalized (status:2), will reconnect")
                
                is_official_final = (status == 2)
                current_time = time.time()
                
                if text and len(text.strip()) > 0:
                    add_to_lecture_history(
                        text=text,
                        text_type='recognition_interim' if not is_official_final else 'recognition_final',
                        language='zh',
                        speaker='teacher',
                        metadata={'status': status, 'is_final': is_official_final}
                    )
                
                if text and SHOW_INTERMEDIATE and len(text.strip()) > 0:
                    if LAST_SEGMENTS and text.startswith(LAST_SEGMENTS[-1]):
                        text = text
                    
                    LAST_SEGMENTS.append(text)
                    if len(LAST_SEGMENTS) > 5:
                        LAST_SEGMENTS.pop(0)
                    
                    time_since_last = current_time - LAST_SEGMENT_TIME
                    is_final_by_pause = time_since_last > FINAL_TIMEOUT and len(LAST_SEGMENTS) > 2
                    
                    is_final = is_official_final or (
                        is_final_by_pause and 
                        len(text.split()) >= MIN_WORDS_FOR_FINAL
                    )
                    
                    LAST_SEGMENT_TIME = current_time
                    
                    if text and clients_lang:
                        def translate_and_send(text, sid, lang, is_final):
                            try:
                                cache_key = f"{lang}:{text}"
                                if cache_key in translation_cache:
                                    translated = translation_cache[cache_key]
                                else:
                                    start_time = time.time()
                                    translated = deepseek_translate(text, lang, is_final=is_final)
                                    log_performance('translation_times', time.time() - start_time)
                                    
                                    translation_cache[cache_key] = translated
                                    translation_cache.move_to_end(cache_key)
                                    
                                    if len(translation_cache) > MAX_CACHE:
                                        translation_cache.popitem(last=False)
                                
                                add_to_lecture_history(
                                    text=text,
                                    text_type='translation',
                                    language=lang,
                                    translation=translated,
                                    speaker='system',
                                    metadata={
                                        'original_lang': 'zh',
                                        'target_lang': lang,
                                        'is_interim': not is_final
                                    }
                                )
                                
                                socketio.emit("new_translation", {
                                    "original": text,
                                    "translation": translated,
                                    "is_final": is_final
                                }, to=sid)
                            except Exception as e:
                                logger.error(f"Translation error for {sid}: {e}")
                                socketio.emit("new_translation", {
                                    "original": text,
                                    "translation": f"[{text}]",
                                    "is_final": is_final
                                }, to=sid)
                        
                        # ОПТИМИЗАЦИЯ СКОРОСТИ:
                        # - Интерм-фрагменты (is_final=False) отправляем МГНОВЕННО без вызова DeepSeek.
                        #   Раньше каждый интерм (~каждые 0.5с речи) звал API с задержкой ~4с и
                        #   забивал пул воркеров — финальные переводы вставали в очередь.
                        # - LLM-перевод вызываем только для финальных фраз.
                        if not is_final:
                            for sid, lang in list(clients_lang.items()):
                                socketio.emit("new_translation", {
                                    "original": text,
                                    "translation": "",  # пусто — клиент показывает оригинал до финала
                                    "is_final": False
                                }, to=sid)
                        else:
                            futures = []
                            for sid, lang in list(clients_lang.items()):
                                futures.append(
                                    deepseek_executor.submit(
                                        translate_and_send,
                                        text, sid, lang, is_final
                                    )
                                )
                            
                            for fut in futures:
                                try:
                                    fut.result(timeout=2.0)
                                except Exception:
                                    pass
                    
                    if is_final:
                        logger.info(f"📝 FINAL: '{text}'")
                        FULL_LECTURE_TEXT.append(text)
                        PHRASE_COUNT += 1
                        emit_stats()
                        
                        if len(FULL_LECTURE_TEXT) % 10 == 0:
                            threading.Thread(target=auto_save_lecture, daemon=True).start()
        
        elif data.get('code') != 0:
            logger.error(f"Server error: {data.get('message')}")
            PERF_METRICS['errors']['server_error'] += 1
            # Ошибка сервера = конец сессии, перестаём слать и переподключаемся
            xf_session_active = False
            
    except Exception as e:
        logger.error(f"Message handling error: {e}")
        PERF_METRICS['errors']['message_error'] += 1

def on_error(ws, error):
    logger.error(f"WebSocket error: {error}")
    PERF_METRICS['errors']['websocket_error'] += 1

def on_close(ws, close_status_code, close_msg):
    logger.info(f"WebSocket closed: {close_msg}")

def on_open(ws):
    global ws_connection, xf_session_active
    logger.info("✅ WebSocket connected")
    ws_connection = ws
    # Новая сессия: разрешаем отправку аудио
    xf_session_active = True
    
    init_params = {
        "common": {"app_id": APPID},
        "business": {
            "language": "zh_cn",
            "domain": "iat",
            "accent": "mandarin"
        },
        "data": {
            "status": 0,
            "format": "audio/L16;rate=16000",
            "encoding": "raw",
            # ВАЖНО: сервис Short Form ASR (iat, SG) не отвечает на пустой
            # первый фрейм (audio: "") — соединение закрывается по "server read
            # msg timeout". Первый фрейм должен содержать аудио: отправляем 1с
            # PCM16-тишины (проверено: сервер мгновенно отвечает code:0).
            "audio": base64.b64encode(struct.pack("<h", 0) * 16000).decode("utf-8")
        }
    }
    
    ws.send(json.dumps(init_params))
    logger.info("Initialization parameters sent (with 1s silence)")

# ================= Audio capture thread =================
_audio_cb_count = [0]
_audio_cb_last_log = [0.0]

def audio_callback(indata, frames, time_info, status):
    if status:
        logger.warning(f"Audio status: {status}")
    
    if is_running:
        try:
            audio_mono = indata.copy().flatten()
            if len(audio_mono) > 0:
                audio_queue.put(audio_mono, timeout=0.1)
                # Диагностика: раз в 10 секунд логируем, что микрофон отдаёт данные
                _audio_cb_count[0] += 1
                now_t = time.time()
                if now_t - _audio_cb_last_log[0] > 10.0:
                    _audio_cb_last_log[0] = now_t
                    logger.info(f"🎙️ audio_callback: {_audio_cb_count[0]} frames in last 10s, queue={audio_queue.qsize()}")
                    _audio_cb_count[0] = 0
        except q.Full:
            pass
        except Exception as e:
            logger.error(f"audio_callback error: {e}")

def audio_thread():
    logger.info("🎤 Starting optimized audio capture...")
    
    # Явно выбираем реальный микрофон (не BlackHole/WeMeet/агрегатное),
    # иначе device=None в фоновом процессе может захватить виртуальное
    # устройство, которое почти не отдаёт фреймов (проверено: 2 фрейма/20с).
    mic_device = None
    try:
        devices = sd.query_devices()
        for idx, dev in enumerate(devices):
            name = str(dev.get("name", ""))
            ch_in = dev.get("max_input_channels", 0)
            if ch_in > 0 and ("Microphone" in name or "麦克风" in name or "микрофон" in name.lower()):
                if "BlackHole" not in name:
                    mic_device = idx
                    break
        if mic_device is None:
            # запасной вариант: первое устройство с входными каналами
            for idx, dev in enumerate(devices):
                if dev.get("max_input_channels", 0) > 0:
                    mic_device = idx
                    break
        logger.info(f"🎙️ Selected audio input device: {mic_device} ({devices[mic_device]['name'] if mic_device is not None and mic_device < len(devices) else 'default'})")
    except Exception as e:
        logger.warning(f"Device selection fallback: {e}")
    
    try:
        with sd.InputStream(
            samplerate=16000,
            channels=1,
            dtype="float32",
            blocksize=2048,
            latency='low',
            callback=audio_callback,
            device=mic_device
        ):
            logger.info("✅ Microphone ready (low latency mode)")
            while is_running:
                time.sleep(0.1)
                
    except Exception as e:
        logger.error(f"❌ Audio capture error: {e}")

# ================= WebSocket thread =================
def ws_thread():
    global ws_connection, is_running, xf_session_active

    logger.info("🌐 Connecting to WebSocket...")
    last_audio_time = time.time()
    audio_buffer = []

    while is_running:
        try:
            ws = websocket.WebSocketApp(
                build_auth_url(),
                on_open=on_open,
                on_message=on_message,
                on_error=on_error,
                on_close=on_close
            )

            wst = threading.Thread(
                target=ws.run_forever,
                kwargs={"ping_interval": 20, "ping_timeout": 10}
            )
            wst.daemon = True
            wst.start()

            # ЖДЁМ фактического соединения: ws.sock появляется только после
            # успешного хендшейка в потоке run_forever. Если начать слать аудио
            # до этого (или выйти из цикла), соединение повиснет и iFLYTEK
            # закроет его по "server read msg timeout".
            sock_wait = 0
            while sock_wait < 5.0 and (ws.sock is None or not getattr(ws.sock, 'connected', False)):
                time.sleep(0.1)
                sock_wait += 0.1
            if ws.sock is None or not getattr(ws.sock, 'connected', False):
                logger.warning(f"⚠️ WS socket not ready after {sock_wait:.1f}s, reconnecting...")
                try:
                    ws.close()
                except Exception:
                    pass
                time.sleep(1)
                continue
            logger.info(f"🔌 WS socket ready in {sock_wait:.1f}s")

            while is_running:
                try:
                    if not xf_session_active:
                        logger.info("🔁 iFLYTEK session ended, reconnecting...")
                        break

                    if not ws.sock or not ws.sock.connected:
                        break

                    chunk = audio_queue.get(timeout=0.1)
                    last_audio_time = time.time()

                    if len(chunk) > 0:
                        audio_buffer.append(chunk)
                        
                        if (time.time() - last_audio_time > SEND_INTERVAL or
                            len(audio_buffer) > 3):
                            
                            combined = np.concatenate(audio_buffer) if audio_buffer else chunk
                            chunk_pcm16 = float32_to_pcm16(combined)
                            
                            ws.send(json.dumps({
                                "data": {
                                    "status": 1,
                                    "format": "audio/L16;rate=16000",
                                    "encoding": "raw",
                                    "audio": base64.b64encode(chunk_pcm16).decode("utf-8")
                                }
                            }))
                            
                            audio_buffer = []

                except q.Empty:
                    if not xf_session_active:
                        break
                    idle_for = time.time() - last_audio_time
                    if idle_for > 0.8:
                        if audio_buffer:
                            # Есть накопленное аудио — отправляем как status:1
                            # (не финализируем! premature status:2 закрывает сессию)
                            combined = np.concatenate(audio_buffer)
                            chunk_pcm16 = float32_to_pcm16(combined)
                            ws.send(json.dumps({
                                "data": {
                                    "status": 1,
                                    "format": "audio/L16;rate=16000",
                                    "encoding": "raw",
                                    "audio": base64.b64encode(chunk_pcm16).decode("utf-8")
                                }
                            }))
                            audio_buffer = []
                        else:
                            # ВАЖНО: сервис iFLYTEK (iat) закрывает соединение по
                            # "server read msg timeout", если после init не приходят
                            # данные. При простое микрофона шлём 0.5с тишины (status:1),
                            # чтобы держать сессию живой. status:2 здесь НЕ отправляем —
                            # это мгновенно завершило бы распознавание.
                            silence = np.zeros(8000, dtype=np.float32)  # 0.5с @ 16kHz
                            chunk_pcm16 = float32_to_pcm16(silence)
                            ws.send(json.dumps({
                                "data": {
                                    "status": 1,
                                    "format": "audio/L16;rate=16000",
                                    "encoding": "raw",
                                    "audio": base64.b64encode(chunk_pcm16).decode("utf-8")
                                }
                            }))
                        continue

                except Exception as e:
                    logger.error(f"Audio sending error: {e}")
                    break

            if is_running:
                # Сессия завершена сервером (VAD) или сокет закрылся — закрываем
                # и переподключаемся для следующей фразы
                try:
                    ws.close()
                except Exception:
                    pass
                time.sleep(0.5)

        except Exception as e:
            logger.error(f"❌ WebSocket error: {e}")
            if is_running:
                time.sleep(1)

def process_math_formulas(text):
    text = normalize_numbers(text)
    
    # Китайские цифры контекстуально: заменяем ТОЛЬКО одиночный иероглиф-цифру,
    # который НЕ является частью слова (не окружён другими иероглифами).
    # Это защищает слова типа "三角" (треугольник) → не "3角",
    # "第三" (третий) → не "第3". '一' исключён полностью — он слишком частотен
    # в словах ("一定", "第一") и трактуется как "минус", что опасно.
    chinese_math = {
        '二': '2',
        '三': '3',
        '四': '4',
        '五': '5',
        '六': '6',
        '七': '7',
        '八': '8',
        '九': '9',
        '零': '0',
    }
    # Границы: не слева и не справа от иероглифа (U+4E00–U+9FFF).
    # Внутри формулы "x二y" заменится, в слове "第二" — нет.
    cjk = r'[\u4e00-\u9fff]'
    
    if any(x in text for x in ['x', 'y', 'f(', '=', '+', '-']):
        for ch, num in chinese_math.items():
            pattern = re.compile(
                rf'(?<!{cjk}){re.escape(ch)}(?!{cjk})'
            )
            text = pattern.sub(num, text)
    
    # Сначала специфичные regex-паттерны с контекстом переменной — они требуют
    # НЕТРОНУТЫЙ исходный текст ("x squared" -> "x²", "square root of x" -> "√(x)").
    # Если сначала применить словарь MATH_TERMS_EN, ключи "squared"/"square"/
    # "cube root" и т.п. поглотятся раньше и паттерны не сработают
    # (получим "x ²" и "² root of x").
    patterns = [
        (r'([a-zA-Z0-9πe])\s+squared', r'\1²'),
        (r'([a-zA-Z0-9πe])\s+cubed', r'\1³'),
        (r'([a-zA-Z0-9πe])\s+to the power of\s+([0-9]+)', r'\1^\2'),
        (r'([a-zA-Z0-9πe])\s+to the\s+([0-9]+)(?:st|nd|rd|th)\s+power', r'\1^\2'),
        (r'square root of\s+([a-zA-Z0-9πe]+)', r'√(\1)'),
        (r'sqrt\s+([a-zA-Z0-9πe]+)', r'√(\1)'),
        (r'cube root of\s+([a-zA-Z0-9πe]+)', r'∛(\1)'),
        (r'([a-zA-Z0-9πe]+)\s+over\s+([a-zA-Z0-9πe]+)', r'\1/\2'),
        (r'limit as\s+([a-zA-Z0-9]+)\s+approaches\s+([0-9∞]+)', r'lim_{\1→\2}'),
        (r'as\s+([a-zA-Z0-9]+)\s+approaches\s+([0-9∞]+)', r'_{\1→\2}'),
        (r'integral from\s+([0-9a-zA-Z]+)\s+to\s+([0-9a-zA-Z]+)', r'∫_{\1}^{\2}'),
    ]
    
    for pattern, replacement in patterns:
        text = re.sub(pattern, replacement, text, flags=re.IGNORECASE)
    
    # Потом общая словарная замена для оставшихся ключей (pi, epsilon, over, ...)
    phrases = sorted(MATH_TERMS_EN.keys(), key=len, reverse=True)
    for phrase in phrases:
        if phrase in text:
            text = text.replace(phrase, MATH_TERMS_EN[phrase])
    
    return text

def semantic_repair(text, use_llm=True):
    global REPAIR_CACHE
    
    if text in REPAIR_CACHE:
        return REPAIR_CACHE[text]
    
    math_indicators = ['x', 'y', 'plus', 'minus', 'times', 'divided', 'equals',
                       'squared', 'cubed', 'root', 'sin', 'cos', 'tan', 'log']
    
    if not any(ind in text.lower() for ind in math_indicators):
        REPAIR_CACHE[text] = text
        return text
    
    if len(text) < 30:
        result = process_math_formulas(text)
        REPAIR_CACHE[text] = result
        return result
    
    # LLM-репейр выполняется только для финальных фраз (use_llm=True).
    # Для промежуточных (interim) — только локальные regex: не блокируем
    # воркер пула 5-секундным сетевым вызовом на каждые ~0.5с речи.
    if use_llm:
        prompt = f"Fix math in: {text}\nFixed:"
        
        try:
            if DEEPSEEK_API_KEY:
                resp = requests.post(
                    DEEPSEEK_URL,
                    headers={"Authorization": f"Bearer {DEEPSEEK_API_KEY}"},
                    json={
                        "model": "deepseek-chat",
                        "messages": [{"role": "user", "content": prompt}],
                        "temperature": 0.1,
                        "max_tokens": 200
                    },
                    timeout=5
                )
                resp.raise_for_status()
                result = resp.json()["choices"][0]["message"]["content"].strip()
                REPAIR_CACHE[text] = result
                if len(REPAIR_CACHE) > 1000:
                    REPAIR_CACHE.popitem(last=False)
                return result
        except:
            pass
    
    result = process_math_formulas(text)
    REPAIR_CACHE[text] = result
    if len(REPAIR_CACHE) > 1000:
        REPAIR_CACHE.popitem(last=False)
    return result

def textbook_repair(text):
    text = process_math_formulas(text)
    
    # Термины делим на две группы по типу символов, чтобы нечёткий поиск
    # НЕ подменял латинский термин китайским фрагментом и наоборот:
    #   - CJK-термины (иероглифы) ищем только в CJK-фрагментах
    #   - латинские/математические (π, √, sin, x^2) — только в не-CJK фрагментах
    cjk_re = re.compile(r'[\u4e00-\u9fff]')
    
    def has_cjk(s):
        return bool(cjk_re.search(s))
    
    for tid in ACTIVE_TEXTBOOKS:
        terms = TEXTBOOKS.get(tid, {}).get("terms", set())
        math_terms = set(MATH_TERMS_EN.values())
        all_terms = terms.union(math_terms)
        
        cjk_terms = sorted((t for t in all_terms if has_cjk(t)), key=len, reverse=True)
        latin_terms = sorted((t for t in all_terms if not has_cjk(t)), key=len, reverse=True)
        
        # Нечёткое исправление: ищем термин из учебника, похожий на фрагмент текста
        # (SequenceMatcher >= 0.8), и заменяем ошибочный фрагмент на корректный термин.
        # Точные совпадения не трогаем (они уже корректны).
        for term in cjk_terms + latin_terms:
            if len(term) < 2:
                continue
            term_is_cjk = has_cjk(term)
            for i in range(len(text) - len(term) + 1):
                substr = text[i:i + len(term)]
                if substr == term:
                    continue
                # Однотипность обязательна: иероглиф ↔ иероглиф, латиница ↔ латиница
                if term_is_cjk != has_cjk(substr):
                    continue
                if difflib.SequenceMatcher(None, substr.lower(), term.lower()).ratio() >= 0.8:
                    text = text[:i] + term + text[i + len(term):]
                    break
            else:
                continue
            break
    
    return text

def deepseek_translate(text, target_lang, is_final=False):
    try:
        if any(indicator in text.lower() for indicator in ['x', 'y', 'plus', 'minus', 'times', 'divided', 'equals', 'squared', 'cubed', 'root', 'sin', 'cos', 'tan', 'log']):
            repaired = semantic_repair(text, use_llm=is_final)
            if repaired and repaired != text:
                logger.info(f"📐 Math repair applied: '{text}' -> '{repaired}'")
                text = repaired
    except Exception as e:
        logger.warning(f"Semantic repair skipped: {e}")
    
    try:
        text = textbook_repair(text)
    except Exception as e:
        logger.warning(f"Textbook repair skipped: {e}")

    if not text.strip():
        return ""
    
    if not DEEPSEEK_API_KEY or DEEPSEEK_API_KEY == "your_deepseek_api_key_here":
        logger.warning("⚠️ DEEPSEEK_API_KEY not set or default value")
        return f"[Translation: {text}]"
    
    lang_names = {
        "en": "English", "de": "German", "kk": "Kazakh",
        "ru": "Russian", "ja": "Japanese", "ko": "Korean",
        "vi": "Vietnamese", "th": "Thai", "ms": "Malay",
        "id": "Indonesian", "mn": "Mongolian", "hy": "Armenian",
        "it": "Italian", "fr": "French", "es": "Spanish"
    }
    
    target_lang_name = lang_names.get(target_lang, target_lang)
    
    context = ""
    recent_entries = LECTURE_HISTORY[-5:]
    if recent_entries:
        context_texts = []
        for entry in recent_entries:
            if entry['type'] in ['recognition_final', 'translation']:
                context_texts.append(entry.get('translation', entry['text']))
        if context_texts:
            context = "Previous context:\n" + "\n".join(context_texts[-2:]) + "\n\n"
    
    # Контекст активных учебников: передаём модели имена и ключевые термины,
    # чтобы она корректно держала терминологию курса при переводе.
    textbook_context = ""
    if ACTIVE_TEXTBOOKS:
        textbook_parts = []
        for tid in ACTIVE_TEXTBOOKS:
            tb = TEXTBOOKS.get(tid, {})
            tb_name = tb.get("name", tid)
            tb_terms = tb.get("terms", set())
            # Термины, отличные от универсальных математических символов
            specialized = [t for t in tb_terms if t not in set(MATH_TERMS_EN.values())]
            if specialized:
                textbook_parts.append(
                    f"Course textbook '{tb_name}'. Key terms: {', '.join(sorted(specialized)[:40])}"
                )
        if textbook_parts:
            textbook_context = "ACTIVE COURSE TEXTBOOK(S):\n" + "\n".join(textbook_parts) + "\n\n"
    
    prompt = f"""
{context}
Translate this mathematical lecture from Chinese to {target_lang_name}.

{textbook_context}MATHEMATICAL RULES:
- f(x) remains as f(x), not e(x)
- Use standard math notation: → for arrow, ε for epsilon
- Numbers and variables stay as is
- Keep all mathematical expressions intact
- Do not add any explanations, only the translation

Text to translate:
{text}

Translation (mathematically accurate, in {target_lang_name} only):
"""
    
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {DEEPSEEK_API_KEY}"
    }
    
    body = {
        "model": "deepseek-chat",
        "messages": [
            {"role": "system", "content": f"You are a professional translator. Translate to {target_lang_name}. Preserve all mathematical expressions exactly."},
            {"role": "user", "content": prompt}
        ],
        # Меньше токенов = быстрее ответ; для коротких фраз 512 более чем достаточно
        "max_tokens": 512,
        "temperature": 0.3,
        "stream": False
    }
    
    try:
        logger.info(f"🌐 Translating to {target_lang}...")
        start_time = time.time()
        # Session с keep-alive: переиспользуем TCP/TLS вместо нового соединения на каждый вызов
        resp = _deepseek_session.post(DEEPSEEK_URL, json=body, headers=headers, timeout=15)
        resp.raise_for_status()
        result = resp.json()["choices"][0]["message"]["content"].strip()
        log_performance('translation_times', time.time() - start_time)
        
        result = post_process_translation(result)
        
        logger.info(f"✅ Translated ({len(result)} characters)")
        return result
    except Exception as e:
        logger.error(f"❌ Translation error: {e}")
        PERF_METRICS['errors']['translation_error'] += 1
        return text

def quick_translate(text, target_lang):
    return deepseek_translate(text, target_lang)

def auto_save_lecture():
    try:
        filename = f"lecture_{datetime.now().strftime('%Y%m%d_%H%M')}.txt"
        with open(filename, "w", encoding="utf-8") as f:
            for entry in LECTURE_HISTORY[-500:]:
                f.write(f"[{entry['datetime']}] {entry['type'].upper()}\n")
                f.write(f"{entry['text']}\n")
                if entry.get('translation'):
                    f.write(f"→ {entry['translation']}\n")
                f.write("-" * 30 + "\n")
        logger.info(f"💾 Auto-saved to {filename}")
    except Exception as e:
        logger.error(f"Auto-save error: {e}")

# ================= Languages =================
LANGUAGES = {
    "en": "🇺🇸 English",
    "de": "🇩🇪 German",
    "kk": "🇰🇿 Kazakh",
    "ru": "🇷🇺 Russian",
    "ja": "🇯🇵 Japanese",
    "ko": "🇰🇷 Korean",
    "vi": "🇻🇳 Vietnamese",
    "th": "🇹🇭 Thai",
    "ms": "🇲🇾 Malay",
    "id": "🇮🇩 Indonesian",
    "mn": "🇲🇳 Mongolian",
    "hy": "🇦🇲 Armenian",
    "it": "🇮🇹 Italian",
    "fr": "🇫🇷 French",
    "es": "🇪🇸 Spanish",
}

def emit_stats():
    socketio.emit("stats", {
        "connected": len(CONNECTED_CLIENTS),
        "phrases": PHRASE_COUNT
    })

@socketio.on("heartbeat")
def handle_heartbeat(data):
    sid = request.sid
    now = time.time()

    if sid not in ATTENDANCE:
        ATTENDANCE[sid] = {
            "join_time": now,
            "active": 0,
            "inactive": 0,
            "last_seen": now,
            "verified": False,
            "student_id": None
        }
    else:
        if "active" not in ATTENDANCE[sid]:
            ATTENDANCE[sid]["active"] = 0
        if "inactive" not in ATTENDANCE[sid]:
            ATTENDANCE[sid]["inactive"] = 0
        if "last_seen" not in ATTENDANCE[sid]:
            ATTENDANCE[sid]["last_seen"] = now
        if "verified" not in ATTENDANCE[sid]:
            ATTENDANCE[sid]["verified"] = False

    a = ATTENDANCE[sid]
    
    student_id = data.get("student_id") or a.get("student_id")
    
    if student_id and student_id in VERIFIED_STUDENTS:
        if VERIFIED_STUDENTS[student_id].get("verified", False):
            a["verified"] = True
            a["student_id"] = student_id
        else:
            a["verified"] = False
    else:
        a["verified"] = False

    a["last_seen"] = now
    
    if a.get("verified", False):
        a["active"] += 5
    else:
        if data.get("visibility") == "visible" and data.get("focused"):
            a["active"] += 5
        else:
            a["inactive"] += 5
    
    logger.debug(f"ATTENDANCE state: {len(ATTENDANCE)} clients")

# ================= Socket.IO обработчики для истории =================
@socketio.on("get_full_lecture_history")
def handle_get_full_history(data):
    sid = request.sid
    student_id = data.get("student_id")
    
    if not student_id or student_id not in VERIFIED_STUDENTS:
        socketio.emit("history_error", {"error": "Not verified"}, to=sid)
        return
    
    history_formatted = []
    for entry in LECTURE_HISTORY[-500:]:
        history_formatted.append({
            'time': entry['datetime'],
            'text': entry['text'],
            'translation': entry.get('translation', ''),
            'type': entry['type'],
            'speaker': entry['speaker']
        })
    
    socketio.emit("full_lecture_history", {
        "history": history_formatted,
        "total": len(LECTURE_HISTORY)
    }, to=sid)
    logger.info(f"📚 Sent lecture history to student {student_id}")

@socketio.on("get_lecture_summary")
def handle_get_summary(data):
    sid = request.sid
    student_id = data.get("student_id")
    time_range = data.get("range", "all")
    
    if not student_id or student_id not in VERIFIED_STUDENTS:
        socketio.emit("summary_error", {"error": "Not verified"}, to=sid)
        return
    
    # Язык студента (выбранный в панели), по умолчанию английский
    target_lang = clients_lang.get(sid, "en")
    target_lang_name = {
        "en": "English", "de": "German", "kk": "Kazakh",
        "ru": "Russian", "ja": "Japanese", "ko": "Korean",
        "vi": "Vietnamese", "th": "Thai", "ms": "Malay",
        "id": "Indonesian", "mn": "Mongolian", "hy": "Armenian",
        "it": "Italian", "fr": "French", "es": "Spanish",
        "zh": "Chinese"
    }.get(target_lang, "English")
    
    now = time.time()
    if time_range == 'last_hour':
        cutoff = now - 3600
    elif time_range == 'last_30min':
        cutoff = now - 1800
    else:
        cutoff = 0
    
    lecture_texts = []
    for entry in LECTURE_HISTORY:
        if entry['timestamp'] >= cutoff and entry['type'] in ['recognition_final', 'translation']:
            text = entry.get('translation', entry['text'])
            lecture_texts.append(f"[{entry['datetime']}] {text}")
    
    if not lecture_texts:
        socketio.emit("lecture_summary", {
            "summary": "No lecture content available for this time period."
        }, to=sid)
        return
    
    full_text = "\n".join(lecture_texts)
    
    prompt = f"""
You are an AI assistant helping a student review a lecture. Please provide a concise summary of the following lecture content:

{full_text}

Please structure your summary:
1. Main topics covered
2. Key formulas or concepts
3. Important conclusions
4. Questions that were discussed (if any)

Respond in {target_lang_name} (the student's language).
Keep it clear and educational.
"""
    
    try:
        if DEEPSEEK_API_KEY:
            resp = requests.post(
                DEEPSEEK_URL,
                headers={"Authorization": f"Bearer {DEEPSEEK_API_KEY}"},
                json={
                    "model": "deepseek-chat",
                    "messages": [{"role": "user", "content": prompt}],
                    "temperature": 0.3,
                    "max_tokens": 1000
                },
                timeout=30
            )
            resp.raise_for_status()
            summary = resp.json()["choices"][0]["message"]["content"].strip()
            
            add_to_lecture_history(
                text=summary,
                text_type='summary',
                language=target_lang,
                speaker='assistant',
                metadata={'time_range': time_range, 'student_id': student_id}
            )
            
            socketio.emit("lecture_summary", {"summary": summary}, to=sid)
            logger.info(f"📋 Generated {target_lang} summary for student {student_id}")
        else:
            socketio.emit("lecture_summary", {
                "summary": "Summary generation requires DeepSeek API key."
            }, to=sid)
    except Exception as e:
        logger.error(f"Summary generation error: {e}")
        socketio.emit("summary_error", {"error": str(e)}, to=sid)

@socketio.on("search_lecture")
def handle_search_lecture(data):
    sid = request.sid
    student_id = data.get("student_id")
    query = data.get("query", "").strip().lower()
    
    if not student_id or student_id not in VERIFIED_STUDENTS:
        socketio.emit("search_error", {"error": "Not verified"}, to=sid)
        return
    
    if len(query) < 3:
        socketio.emit("search_error", {"error": "Query too short"}, to=sid)
        return
    
    results = []
    for entry in LECTURE_HISTORY[-1000:]:
        if query in entry['text'].lower() or query in entry.get('translation', '').lower():
            results.append({
                'time': entry['datetime'],
                'text': entry['text'],
                'translation': entry.get('translation', ''),
                'type': entry['type']
            })
    
    socketio.emit("search_results", {
        "query": query,
        "results": results[:50],
        "count": len(results)
    }, to=sid)
    logger.info(f"🔍 Search '{query}' returned {len(results)} results for student {student_id}")

@socketio.on("export_lecture")
def handle_export_lecture(data):
    sid = request.sid
    student_id = data.get("student_id")
    format_type = data.get("format", "txt")
    
    if not student_id or student_id not in VERIFIED_STUDENTS:
        socketio.emit("export_error", {"error": "Not verified"}, to=sid)
        return
    
    if format_type == "json":
        export_data = {
            "lecture_id": datetime.now().strftime('%Y%m%d_%H%M%S'),
            "generated": datetime.now().isoformat(),
            "total_entries": len(LECTURE_HISTORY),
            "entries": LECTURE_HISTORY[-1000:]
        }
        result = json.dumps(export_data, indent=2, ensure_ascii=False)
        filename = f"lecture_export_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        
    elif format_type == "md":
        lines = ["# Lecture Export\n"]
        lines.append(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        lines.append(f"Total entries: {len(LECTURE_HISTORY)}\n\n")
        
        for entry in LECTURE_HISTORY[-500:]:
            lines.append(f"## {entry['datetime']} - {entry['type']}\n")
            lines.append(f"**Original:** {entry['text']}\n")
            if entry.get('translation'):
                lines.append(f"**Translation:** {entry['translation']}\n")
            if entry.get('speaker'):
                lines.append(f"*Speaker: {entry['speaker']}*\n")
            lines.append("\n---\n")
        
        result = "\n".join(lines)
        filename = f"lecture_export_{datetime.now().strftime('%Y%m%d_%H%M%S')}.md"
        
    else:
        lines = [f"LECTURE EXPORT - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"]
        lines.append("=" * 50)
        lines.append("")
        
        for entry in LECTURE_HISTORY[-500:]:
            lines.append(f"[{entry['datetime']}] {entry['type'].upper()}")
            lines.append(f"Original: {entry['text']}")
            if entry.get('translation'):
                lines.append(f"Translation: {entry['translation']}")
            lines.append("-" * 30)
        
        result = "\n".join(lines)
        filename = f"lecture_export_{datetime.now().strftime('%Y%m%d_%H%M%S')}.txt"
    
    socketio.emit("lecture_export", {
        "filename": filename,
        "content": result,
        "format": format_type
    }, to=sid)
    logger.info(f"📥 Exported lecture as {filename} for student {student_id}")

# ================= ОПТИМИЗИРОВАННЫЕ ОБРАБОТЧИКИ ТРАНСЛЯЦИИ =================
@socketio.on("start_screen_share")
def handle_start_screen_share():
    global current_teacher_sid
    sid = request.sid
    
    if current_teacher_sid is not None and current_teacher_sid != sid:
        socketio.emit("screen_share_error", {"message": "Другой учитель уже транслирует экран"}, to=sid)
        return
    
    current_teacher_sid = sid
    if sid not in ATTENDANCE:
        ATTENDANCE[sid] = {}
    ATTENDANCE[sid]["screen_share_started"] = time.time()
    ATTENDANCE[sid]["is_teacher"] = True
    
    # Учитель присоединяется к комнате учителя
    join_room(TEACHER_ROOM, sid=sid)
    
    logger.info(f"📺 Учитель {sid} начал трансляцию экрана (WebRTC)")
    logger.info(f"📺 Текущий ATTENDANCE: {len(ATTENDANCE)} клиентов")
    logger.info(f"📺 ATTENDANCE DATA: {ATTENDANCE}")
    
    # Уведомляем ВСЕХ студентов, кроме учителя (не фильтруем по verified)
    notified_count = 0
    for student_sid, student_data in ATTENDANCE.items():
        if student_sid != current_teacher_sid:  # Отправляем всем, кроме учителя
            socketio.emit("screen_share_started", to=student_sid)
            notified_count += 1
            logger.info(f"📺 Уведомлён студент {student_sid} (verified: {student_data.get('verified', False)})")
    
    logger.info(f"📺 Уведомлено {notified_count} студентов")

# ===== НОВЫЕ WebRTC ОБРАБОТЧИКИ =====
@socketio.on("webrtc_offer")
def handle_webrtc_offer(data):
    """Учитель отправляет оффер студенту"""
    student_id = data.get("studentId")
    offer = data.get("offer")
    
    logger.info(f"📺 Поиск студента с ID: {student_id}")
    logger.info(f"📺 Текущий ATTENDANCE: {ATTENDANCE}")
    
    # Находим сокет студента по его ID
    target_sid = None
    for sid, att in ATTENDANCE.items():
        if att.get("student_id") == student_id:
            target_sid = sid
            logger.info(f"📺 Найден студент {student_id} с сокетом {sid}")
            break
    
    if target_sid:
        socketio.emit("webrtc_offer", {
            "studentId": student_id,
            "offer": offer
        }, to=target_sid)
        logger.info(f"📺 WebRTC offer отправлен студенту {student_id} (сокет {target_sid})")
    else:
        logger.error(f"❌ Не найден сокет для студента {student_id}")

@socketio.on("webrtc_answer")
def handle_webrtc_answer(data):
    """Студент отвечает учителю"""
    student_id = data.get("studentId")
    answer = data.get("answer")
    
    if current_teacher_sid:
        socketio.emit("webrtc_answer", {
            "studentId": student_id,
            "answer": answer
        }, to=current_teacher_sid)
        logger.info(f"📺 WebRTC answer от студента {student_id} отправлен учителю")

@socketio.on("webrtc_ice_candidate")
def handle_webrtc_ice(data):
    """Обмен ICE кандидатами"""
    student_id = data.get("studentId")
    candidate = data.get("candidate")
    target = data.get("target", "teacher")
    
    if target == "teacher" and current_teacher_sid:
        socketio.emit("webrtc_ice_candidate", {
            "studentId": student_id,
            "candidate": candidate
        }, to=current_teacher_sid)
        logger.debug(f"📺 ICE кандидат от студента {student_id} отправлен учителю")
    else:
        # Находим студента
        for sid, att in ATTENDANCE.items():
            if att.get("student_id") == student_id:
                socketio.emit("webrtc_ice_candidate", {
                    "studentId": student_id,
                    "candidate": candidate
                }, to=sid)
                logger.debug(f"📺 ICE кандидат от учителя отправлен студенту {student_id}")
                break

@socketio.on("student_joined")
def handle_student_joined(data):
    """Студент подключился во время трансляции"""
    if current_teacher_sid:
        socketio.emit("student_joined", data, to=current_teacher_sid)

@socketio.on("request_webrtc_restart")
def handle_webrtc_restart(data):
    """Запрос на перезапуск WebRTC соединения"""
    student_id = data.get("studentId")
    if current_teacher_sid:
        socketio.emit("webrtc_restart", {
            "studentId": student_id
        }, to=current_teacher_sid)
        logger.info(f"📺 Запрос на перезапуск от студента {student_id} отправлен учителю")
# ===== КОНЕЦ WebRTC ОБРАБОТЧИКОВ =====

@socketio.on("stop_screen_share")
def handle_stop_screen_share():
    global current_teacher_sid
    sid = request.sid
    
    if current_teacher_sid == sid:
        current_teacher_sid = None
        # Учитель покидает комнату учителя
        leave_room(TEACHER_ROOM, sid=sid)
        
        logger.info(f"📺 Учитель {sid} остановил трансляцию экрана")
        
        if screen_share_stats['total_frames_sent'] > 0:
            avg_fps = len(screen_share_stats['frame_times']) / (sum(screen_share_stats['frame_times']) or 1)
            logger.info(f"📺 Статистика: {screen_share_stats['total_frames_sent']} кадров, "
                       f"{len(screen_share_stats['active_viewers'])} зрителей, "
                       f"~{avg_fps:.1f} FPS")
        
        # Уведомляем ВСЕХ студентов, кроме учителя
        for student_sid, student_data in ATTENDANCE.items():
            if student_sid != sid:
                socketio.emit("screen_share_stopped", to=student_sid)
        
        screen_share_stats['active_viewers'].clear()

# ================= Остальные Socket.IO обработчики =================
@socketio.on("connect")
def handle_connect():
    sid = request.sid
    CONNECTED_CLIENTS.add(sid)
    
    now = time.time()
    ATTENDANCE[sid] = {
        "join_time": now,
        "active": 0,
        "inactive": 0,
        "last_seen": now,
        "verified": False,
        "student_id": None,
        "is_teacher": False
    }
    
    # По умолчанию все новые подключения добавляем в комнату студентов
    join_room(STUDENTS_ROOM, sid=sid)
    
    logger.info(f"🔗 Клиент подключился: {sid}, добавлен в комнату {STUDENTS_ROOM}")
    logger.info(f"📊 ATTENDANCE теперь содержит {len(ATTENDANCE)} клиентов")
    logger.info(f"📊 ATTENDANCE DATA: {ATTENDANCE}")
    
    # Если трансляция уже идет, уведомляем нового клиента
    if current_teacher_sid is not None:
        logger.info(f"📺 Трансляция уже идет, уведомляем нового клиента {sid}")
        socketio.emit("screen_share_started", to=sid)
    
    emit_stats()

@socketio.on("disconnect")
def handle_disconnect():
    global current_teacher_sid
    sid = request.sid
    
    # Покидаем комнаты
    leave_room(STUDENTS_ROOM, sid=sid)
    leave_room(TEACHER_ROOM, sid=sid)
    
    student_id = ATTENDANCE.get(sid, {}).get("student_id")
    logger.info(f"🔌 Клиент отключился: {sid}, student_id: {student_id}")
    
    clients_lang.pop(sid, None)
    CONNECTED_CLIENTS.discard(sid)
    
    if sid in ATTENDANCE:
        del ATTENDANCE[sid]
        logger.info(f"📊 ATTENDANCE теперь содержит {len(ATTENDANCE)} клиентов")
    
    if current_teacher_sid == sid:
        current_teacher_sid = None
        logger.info(f"📺 Учитель {sid} отключился, трансляция остановлена")
        # Уведомляем всех студентов об остановке трансляции
        for student_sid, student_data in ATTENDANCE.items():
            socketio.emit("screen_share_stopped", to=student_sid)
    
    emit_stats()

@socketio.on("get_attendance")
def send_attendance():
    now = time.time()
    result = []
    for sid, a in ATTENDANCE.items():
        timeout = 30 if a.get("verified", False) else 10
        online = (now - a["last_seen"]) < timeout
        
        if a.get("verified", False):
            status = "✅ (background)" if online else "❌"
        else:
            status = "✅" if online else "❌"
            
        result.append({
            "student_id": a.get("student_id", "??"),
            "name": a.get("name", "Unknown"),
            "active_minutes": a.get("active", 0) // 60,
            "status": status,
            "verified": a.get("verified", False)
        })
    socketio.emit("attendance_update", result)

@socketio.on("student_active")
def handle_student_active(data):
    sid = request.sid
    student_id = data.get("student_id")
    
    if sid in ATTENDANCE:
        if "active" not in ATTENDANCE[sid]:
            ATTENDANCE[sid]["active"] = 0
        if "last_seen" not in ATTENDANCE[sid]:
            ATTENDANCE[sid]["last_seen"] = time.time()
            
        ATTENDANCE[sid]["last_seen"] = time.time()
        ATTENDANCE[sid]["active"] += 5
        
        if student_id:
            old_id = ATTENDANCE[sid].get("student_id")
            ATTENDANCE[sid]["student_id"] = student_id
            if old_id != student_id:
                logger.info(f"📝 Student ID обновлен для сокета {sid}: {old_id} -> {student_id}")

@socketio.on("restore_session")
def handle_restore_session(data):
    sid = request.sid
    student_id = data.get("student_id")
    
    if student_id and student_id in VERIFIED_STUDENTS:
        if sid not in ATTENDANCE:
            ATTENDANCE[sid] = {}
        
        ATTENDANCE[sid]["student_id"] = student_id
        ATTENDANCE[sid]["verified"] = True
        ATTENDANCE[sid]["restored_at"] = time.time()
        ATTENDANCE[sid]["last_seen"] = time.time()
        
        logger.info(f"🔄 Сессия восстановлена для студента {student_id} (сокет {sid})")
        
        socketio.emit("session_restored", {
            "success": True,
            "message": "Session restored"
        }, to=sid)
    else:
        socketio.emit("session_restored", {
            "success": False,
            "message": "Session not found"
        }, to=sid)

@socketio.on("set_language")
def handle_set_language(data):
    lang = data.get("lang", "en")
    sid = request.sid
    clients_lang[sid] = lang
    logger.info(f"🌍 Client {sid[:8]}... selected language: {lang}")
    socketio.emit("language_set", {"lang": lang}, to=sid)

@socketio.on("get_full_text")
def send_full_text():
    sid = request.sid
    text = "\n".join(FULL_LECTURE_TEXT[-50:])
    socketio.emit("full_text", {"text": text}, to=sid)

# ================= Flask routes =================
@app.route("/")
def teacher():
    return """
    <!DOCTYPE html>
    <html>
    <head>
        <meta charset="utf-8">
        <title>Lecture - Teacher</title>
        <style>
            body { 
                font-family: Arial, sans-serif; 
                padding: 40px; 
                text-align: center; 
                background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
                color: white;
                min-height: 100vh;
            }
            .container {
                max-width: 800px;
                margin: 0 auto;
                background: rgba(255, 255, 255, 0.1);
                padding: 40px;
                border-radius: 20px;
                backdrop-filter: blur(10px);
            }
            .status {
                font-size: 24px;
                padding: 15px;
                border-radius: 10px;
                margin: 20px 0;
                background: rgba(255, 255, 255, 0.2);
            }
            .btn {
                display: inline-block;
                padding: 15px 30px;
                margin: 10px;
                background: white;
                color: #667eea;
                text-decoration: none;
                border-radius: 50px;
                font-weight: bold;
                transition: all 0.3s;
                border: none;
                cursor: pointer;
            }
            .btn:hover {
                transform: translateY(-3px);
                box-shadow: 0 10px 20px rgba(0,0,0,0.2);
            }
            .info {
                text-align: left;
                margin: 30px 0;
                padding: 20px;
                background: rgba(255, 255, 255, 0.1);
                border-radius: 10px;
            }
            .screen-share-area {
                margin-top: 30px;
                border-top: 2px solid rgba(255,255,255,0.3);
                padding-top: 20px;
            }
            #localVideo {
                width: 100%;
                max-width: 600px;
                border-radius: 10px;
                background: #000;
                margin-bottom: 15px;
                border: 2px solid #4CAF50;
            }
        </style>
    </head>
    <body>
        <div class="container">
            <h1>👨‍🏫 Teacher Panel</h1>
            
            <div class="status" id="status">
                <span id="status-text">Loading...</span>
            </div>
            
            <div class="info">
                <h3>📊 Statistics:</h3>
                <p>Connected users: <span id="client-count">0</span></p>
                <p>Recognized phrases: <span id="phrase-count">0</span></p>
                <p>History entries: <span id="history-count">0</span></p>
            </div>
            
            <div class="screen-share-area">
                <h3>📺 Демонстрация экрана</h3>
                <div>
                    <video id="localVideo" autoplay playsinline muted style="display: none;"></video>
                </div>
                <div>
                    <button id="startScreenShareBtn" class="btn" style="background: #4CAF50; color: white;">🎥 Начать трансляцию</button>
                    <button id="stopScreenShareBtn" class="btn" style="background: #f44336; color: white; display: none;">⏹ Остановить трансляцию</button>
                </div>
            </div>
            
            <a href='/teacher/qr' class='btn'>📱 QR Code Panel</a>
            <a href='/student' class='btn' target='_blank'>🎓 Student Panel</a>
            <a href='/api/metrics' class='btn' target='_blank'>📊 Metrics</a>

            <div class="info">
                <h3>🎤 Instructions:</h3>
                <p>1. Open QR code panel for attendance check</p>
                <p>2. Students open student panel</p>
                <p>3. Speak clearly and moderately into the microphone</p>
                <p>4. Text will be automatically translated</p>
                <p>5. Full lecture history is automatically saved</p>
            </div>
        </div>
        
        <script src="https://cdnjs.cloudflare.com/ajax/libs/socket.io/4.7.2/socket.io.js"></script>
<script src="https://webrtc.github.io/adapter/adapter-latest.js"></script>
<script>
    const socket = io();
    
    let localStream = null;
    let peerConnections = {};
    let isSharing = false;
    let pendingIceCandidates = {};
    
    // Конфигурация ICE с вашими TURN серверами (из .env)
    const configuration = {
        iceServers: {ICE_SERVERS_JSON},
        iceCandidatePoolSize: 10,
        iceTransportPolicy: 'all'
    };
    
    const localVideo = document.getElementById('localVideo');
    const startBtn = document.getElementById('startScreenShareBtn');
    const stopBtn = document.getElementById('stopScreenShareBtn');
    
    // ========== ФУНКЦИЯ СОЗДАНИЯ PEER CONNECTION ==========
    function createPeerConnection(studentId) {
    console.log(`📺 Создаем PeerConnection для студента ${studentId}`);
    const pc = new RTCPeerConnection(configuration);
    
    // Хранилище для отложенных ICE кандидатов
    if (!pendingIceCandidates[studentId]) {
        pendingIceCandidates[studentId] = [];
    }
    
    // Добавляем видео трек с настройками кодирования
    if (localStream) {
        console.log(`📺 Добавляем видео трек в PeerConnection для ${studentId}`);
        localStream.getVideoTracks().forEach(track => {
            // addTransceiver надёжнее для screen sharing
            const transceiver = pc.addTransceiver(track, { 
                direction: "sendonly",
                streams: [localStream]
            });
            console.log(`📺 Трансивер создан, направление: ${transceiver.direction}`);
            
            // === НАСТРОЙКА ПАРАМЕТРОВ КОДИРОВАНИЯ ===
            const sender = transceiver.sender;
            
            // Даём время на инициализацию sender'а
            setTimeout(async () => {
                try {
                    const params = sender.getParameters();
                    if (!params.encodings) {
                        params.encodings = [{}];
                    }
                    
                    // Определяем тип захвата по разрешению трека
                    const settings = track.getSettings();
                    const isWholeScreen = settings.width > 1900 || settings.height > 1000;
                    
                    if (isWholeScreen) {
                        console.log('📺 Обнаружен захват всего экрана, применяем агрессивные ограничения');
                        // Для всего экрана более агрессивные настройки
                        params.encodings[0].maxBitrate = 800_000;      // 800 kbps
                        params.encodings[0].scaleResolutionDownBy = 2.5; // Уменьшаем больше
                        params.encodings[0].maxFramerate = 10;        // 10 FPS для стабильности
                    } else {
                        console.log('📺 Обнаружен захват окна/вкладки, применяем умеренные ограничения');
                        // Для окна/вкладки умеренные настройки
                        params.encodings[0].maxBitrate = 1_500_000;    // 1.5 Mbps
                        params.encodings[0].scaleResolutionDownBy = 1.5; // Умеренное уменьшение
                        params.encodings[0].maxFramerate = 15;         // 15 FPS
                    }
                    
                    // Дополнительные настройки для стабильности
                    params.encodings[0].priority = "medium";
                    
                    await sender.setParameters(params);
                    console.log(`✅ Параметры кодирования установлены для студента ${studentId}:`, {
                        maxBitrate: params.encodings[0].maxBitrate,
                        scaleResolutionDownBy: params.encodings[0].scaleResolutionDownBy,
                        maxFramerate: params.encodings[0].maxFramerate
                    });
                    
                    // Проверяем, что параметры применились
                    const updatedParams = sender.getParameters();
                    console.log('📊 Текущие параметры кодирования:', updatedParams.encodings[0]);
                    
                } catch (e) {
                    console.warn(`❌ Не удалось установить параметры кодирования для ${studentId}:`, e);
                    
                    // Fallback: пробуем более мягкие настройки
                    try {
                        setTimeout(async () => {
                            const fallbackParams = sender.getParameters();
                            if (!fallbackParams.encodings) {
                                fallbackParams.encodings = [{}];
                            }
                            fallbackParams.encodings[0].maxBitrate = 1_000_000;
                            fallbackParams.encodings[0].maxFramerate = 10;
                            await sender.setParameters(fallbackParams);
                            console.log(`✅ Fallback параметры установлены для ${studentId}`);
                        }, 500);
                    } catch (fallbackError) {
                        console.error('❌ Fallback тоже не сработал:', fallbackError);
                    }
                }
            }, 200); // Увеличил задержку для надежности
        });
    }
    
    // Обработчик ICE кандидатов
    pc.onicecandidate = (event) => {
        if (event.candidate) {
            console.log(`📡 ICE кандидат для ${studentId}:`, {
                type: event.candidate.type,
                protocol: event.candidate.protocol,
                address: event.candidate.address || 'no-address',
                port: event.candidate.port
            });
            
            if (event.candidate.type === 'relay') {
                console.log('✅ TURN сервер РАБОТАЕТ! Релейный кандидат получен');
            }
            
            // Отправляем кандидата, если remote description уже установлен
            if (pc.remoteDescription) {
                socket.emit('webrtc_ice_candidate', {
                    studentId: studentId,
                    candidate: event.candidate,
                    target: 'student'
                });
            } else {
                // Иначе сохраняем для отправки позже
                pendingIceCandidates[studentId].push(event.candidate);
            }
        }
    };
    
    // Обработчик ошибок ICE кандидатов
    pc.onicecandidateerror = (event) => {
        console.error(`❌ Ошибка ICE кандидата для ${studentId}:`, {
            url: event.url,
            errorCode: event.errorCode,
            errorText: event.errorText
        });
        
        // Показываем уведомление только для критических ошибок
        if (event.errorCode >= 700) {
            showNotification(`⚠️ Проблема с подключением к студенту ${studentId}`, 'warning');
        }
    };
    
    // Обработчик изменения ICE состояния
    pc.oniceconnectionstatechange = () => {
        console.log(`📺 ICE состояние для ${studentId}:`, pc.iceConnectionState);
        
        if (pc.iceConnectionState === 'connected' || pc.iceConnectionState === 'completed') {
            console.log(`✅ Студент ${studentId} подключился`);
            showNotification(`✅ Студент ${studentId} подключился`, 'success');
            
            // Очищаем накопленные кандидаты
            if (pendingIceCandidates[studentId]) {
                pendingIceCandidates[studentId] = [];
            }
            
        } else if (pc.iceConnectionState === 'failed') {
            console.error(`❌ ICE failed для ${studentId}`);
            showNotification(`❌ Не удалось подключить студента ${studentId}`, 'error');
            
            // Пробуем переподключиться
            setTimeout(() => {
                if (isSharing) {
                    console.log(`🔄 Пытаемся переподключить студента ${studentId}`);
                    socket.emit('webrtc_restart', { studentId: studentId });
                }
            }, 3000);
            
        } else if (pc.iceConnectionState === 'disconnected') {
            console.log(`⚠️ Студент ${studentId} временно отключился`);
            showNotification(`⚠️ Студент ${studentId} отключился`, 'warning');
        }
    };
    
    // Обработчик изменения состояния сигналинга
    pc.onsignalingstatechange = () => {
        console.log(`📺 Сигналинг состояние для ${studentId}:`, pc.signalingState);
        
        // Когда remote description установлен, отправляем накопленные кандидаты
        if (pc.signalingState === 'stable' && pendingIceCandidates[studentId]?.length > 0) {
            console.log(`📺 Отправка ${pendingIceCandidates[studentId].length} накопленных кандидатов для ${studentId}`);
            pendingIceCandidates[studentId].forEach(candidate => {
                socket.emit('webrtc_ice_candidate', {
                    studentId: studentId,
                    candidate: candidate,
                    target: 'student'
                });
            });
            pendingIceCandidates[studentId] = [];
        }
    };
    
    // Обработчик изменения состояния соединения
    pc.onconnectionstatechange = () => {
        console.log(`📺 Состояние соединения для ${studentId}:`, pc.connectionState);
        
        if (pc.connectionState === 'connected') {
            console.log(`✅ Полное соединение установлено с ${studentId}`);
        } else if (pc.connectionState === 'failed') {
            console.error(`❌ Соединение с ${studentId} полностью провалилось`);
            
            // Очищаем ресурсы
            if (peerConnections[studentId]) {
                delete peerConnections[studentId];
            }
            if (pendingIceCandidates[studentId]) {
                delete pendingIceCandidates[studentId];
            }
        }
    };
    
    // Обработчик получения статистики
    pc.onicecandidate = (event) => {
        if (event.candidate) {
            // Отправляем кандидата
            if (pc.remoteDescription) {
                socket.emit('webrtc_ice_candidate', {
                    studentId: studentId,
                    candidate: event.candidate,
                    target: 'student'
                });
            } else {
                pendingIceCandidates[studentId].push(event.candidate);
            }
        }
    };
    
    // Добавляем метод для очистки
    pc.cleanup = function() {
        console.log(`🧹 Очистка PeerConnection для ${studentId}`);
        if (pendingIceCandidates[studentId]) {
            delete pendingIceCandidates[studentId];
        }
        this.close();
    };
    
    return pc;
}
    
    // ========== ЗАПУСК ТРАНСЛЯЦИИ ==========
async function safeGetDisplayMedia(constraints, retries = 3) {
    const stepResolutions = [
        { width: 1280, height: 720, fps: 15 },   // исходные
        { width: 1024, height: 768, fps: 10 },   // пониженные
        { width: 800, height: 600, fps: 8 }      // очень низкие
    ];
    for (let attempt = 1; attempt <= retries; attempt++) {
        try {
            console.log(`Attempt ${attempt} to get display media with constraints:`, constraints);
            return await navigator.mediaDevices.getDisplayMedia(constraints);
        } catch (err) {
            if (err.name === 'AbortError' && attempt < retries) {
                console.warn(`Attempt ${attempt} failed with AbortError, retrying with lower constraints...`);
                const next = stepResolutions[attempt] || stepResolutions[stepResolutions.length-1];
                constraints.video = {
                    width: { ideal: next.width, max: next.width },
                    height: { ideal: next.height, max: next.height },
                    frameRate: { ideal: next.fps, max: next.fps }
                };
                await new Promise(resolve => setTimeout(resolve, 1500)); // увеличил задержку
                continue;
            }
            throw err;
        }
    }
}

// ========== ЗАПУСК ТРАНСЛЯЦИИ ==========
startBtn.addEventListener('click', async () => {
    try {
        showNotification('📺 Выберите окно или весь экран для трансляции', 'info');
        
        localStream = await safeGetDisplayMedia({
            video: {
                width: { ideal: 1280, max: 1280 },
                height: { ideal: 720, max: 720 },
                frameRate: { ideal: 15, max: 15 }
            },
            audio: false
        }, 3);
        
        console.log('✅ Поток получен:', localStream);
        
        const videoTrack = localStream.getVideoTracks()[0];
        if (videoTrack) {
            console.log('Видео трек настройки:', videoTrack.getSettings());
            
            // ===== ПРОВЕРКА: ЗАПРЕЩАЕМ ВЕСЬ ЭКРАН =====
            const settings = videoTrack.getSettings();
            if (settings.displaySurface === 'monitor') {
                // Весь экран - отменяем трансляцию
                showNotification('❌ Захват всего экрана не поддерживается. Пожалуйста, выберите окно или вкладку.', 'error');
                localStream.getTracks().forEach(track => track.stop());
                localStream = null;
                return; // Выходим из функции, трансляция не запускается
            }
            // ===== КОНЕЦ ПРОВЕРКИ =====
        }
        
        // Показываем локальное видео
        localVideo.srcObject = localStream;
        localVideo.style.display = 'block';
        localVideo.load();
        
        try {
            await localVideo.play();
            console.log('✅ Локальное видео воспроизводится');
        } catch (playError) {
            console.warn('⚠️ Автовоспроизведение заблокировано:', playError);
            showNotification('⚠️ Нажмите на видео, чтобы запустить трансляцию', 'warning');
            localVideo.addEventListener('click', async function onClick() {
                try {
                    await localVideo.play();
                    localVideo.removeEventListener('click', onClick);
                    console.log('✅ Видео запущено по клику');
                    showNotification('✅ Трансляция запущена', 'success');
                } catch (e) {
                    console.error('❌ Не удалось запустить видео даже по клику:', e);
                    showNotification('❌ Ошибка запуска видео', 'error');
                }
            });
        }
        
        // Получаем список студентов
        const studentsResponse = await fetch('/api/verified_students');
        const studentsData = await studentsResponse.json();
        
        console.log('📺 Создаём peer connections для студентов:', studentsData.students);
        
        for (const student of studentsData.students) {
            const studentId = student.id;
            if (!peerConnections[studentId]) {
                const pc = createPeerConnection(studentId);
                peerConnections[studentId] = pc;
                
                try {
                    const offer = await pc.createOffer({
                        offerToReceiveVideo: true,
                        offerToReceiveAudio: false
                    });
                    
                    let sdp = offer.sdp;
                    if (sdp.indexOf('H264') === -1) {
                        sdp = sdp.replace('VP9/90000', 'VP8/90000');
                    }
                    
                    await pc.setLocalDescription({
                        type: offer.type,
                        sdp: sdp
                    });
                    
                    console.log(`📺 Offer создан для ${studentId}`);
                    
                    socket.emit('webrtc_offer', {
                        studentId: studentId,
                        offer: pc.localDescription
                    });
                } catch (err) {
                    console.error(`❌ Ошибка создания offer для ${studentId}:`, err);
                }
            }
        }
        
        // Обновляем UI
        startBtn.style.display = 'none';
        stopBtn.style.display = 'inline-block';
        isSharing = true;
        
        socket.emit('start_screen_share');
        showNotification('✅ Трансляция начата (WebRTC)', 'success');
        
        videoTrack.onended = () => {
            stopScreenShare();
        };
        
    } catch (err) {
        console.error('❌ Ошибка доступа к экрану:', err);
        if (err.name === 'AbortError') {
            showNotification('❌ Не удалось захватить экран. Попробуйте выбрать окно или вкладку, либо проверьте разрешения.', 'error');
        } else {
            showNotification('❌ Ошибка доступа к экрану: ' + err.message, 'error');
        }
    }
});
    
    // ========== ОСТАНОВКА ТРАНСЛЯЦИИ ==========
    function stopScreenShare() {
        // Закрываем все peer connections
        Object.keys(peerConnections).forEach(studentId => {
            const pc = peerConnections[studentId];
            if (pc) {
                pc.close();
            }
        });
        peerConnections = {};
        pendingIceCandidates = {};
        
        // Останавливаем локальный стрим
        if (localStream) {
            localStream.getTracks().forEach(track => track.stop());
            localStream = null;
        }
        
        // Очищаем UI
        localVideo.srcObject = null;
        localVideo.style.display = 'none';
        startBtn.style.display = 'inline-block';
        stopBtn.style.display = 'none';
        isSharing = false;
        
        // Уведомляем сервер
        socket.emit('stop_screen_share');
        showNotification('📺 Трансляция остановлена', 'info');
    }
    
    stopBtn.addEventListener('click', stopScreenShare);
    
    // ========== ОБРАБОТЧИКИ СОБЫТИЙ ==========
    socket.on('webrtc_answer', async (data) => {
        console.log('📺 Получен answer от студента:', data.studentId);
        const pc = peerConnections[data.studentId];
        
        if (pc) {
            try {
                await pc.setRemoteDescription(new RTCSessionDescription(data.answer));
                console.log(`✅ Remote description установлен для ${data.studentId}`);
            } catch (err) {
                console.error(`❌ Ошибка установки remote description для ${data.studentId}:`, err);
            }
        }
    });
    
    socket.on('webrtc_ice_candidate', (data) => {
        const pc = peerConnections[data.studentId];
        if (pc && pc.remoteDescription) {
            pc.addIceCandidate(new RTCIceCandidate(data.candidate))
                .then(() => console.log(`✅ ICE кандидат добавлен для ${data.studentId}`))
                .catch(err => console.error(`❌ Ошибка добавления ICE кандидата для ${data.studentId}:`, err));
        }
    });
    
    socket.on('student_joined', async (data) => {
        console.log('📺 Новый студент присоединился:', data);
        
        if (isSharing && localStream) {
            const studentId = data.studentId;
            
            // Создаём peer connection для нового студента
            if (!peerConnections[studentId]) {
                const pc = createPeerConnection(studentId);
                peerConnections[studentId] = pc;
                
                try {
                    const offer = await pc.createOffer();
                    await pc.setLocalDescription(offer);
                    
                    socket.emit('webrtc_offer', {
                        studentId: studentId,
                        offer: pc.localDescription
                    });
                    console.log(`📺 Offer отправлен новому студенту ${studentId}`);
                } catch (err) {
                    console.error(`❌ Ошибка создания offer для нового студента ${studentId}:`, err);
                }
            }
        }
    });
    
    socket.on('webrtc_restart', (data) => {
        console.log('📺 Запрос на перезапуск от студента:', data.studentId);
        
        if (isSharing && localStream) {
            const studentId = data.studentId;
            
            // Закрываем старое соединение
            if (peerConnections[studentId]) {
                peerConnections[studentId].close();
                delete peerConnections[studentId];
            }
            
            // Создаём новое
            setTimeout(async () => {
                const pc = createPeerConnection(studentId);
                peerConnections[studentId] = pc;
                
                try {
                    const offer = await pc.createOffer();
                    await pc.setLocalDescription(offer);
                    
                    socket.emit('webrtc_offer', {
                        studentId: studentId,
                        offer: pc.localDescription
                    });
                    console.log(`📺 Offer перезапуска отправлен студенту ${studentId}`);
                } catch (err) {
                    console.error(`❌ Ошибка перезапуска для ${studentId}:`, err);
                }
            }, 100);
        }
    });
    
    socket.on('connect', () => {
        document.getElementById('status-text').innerHTML = '✅ Server running';
        document.getElementById('status').style.background = 'rgba(76, 175, 80, 0.3)';
    });
    
    socket.on('disconnect', () => {
        document.getElementById('status-text').innerHTML = '⚠️ Reconnecting...';
        document.getElementById('status').style.background = 'rgba(255, 152, 0, 0.3)';
        if (isSharing) {
            showNotification('⚠️ Соединение потеряно, трансляция приостановлена', 'warning');
        }
    });
    
    socket.on("stats", data => {
        document.getElementById("client-count").innerText = data.connected;
        document.getElementById("phrase-count").innerText = data.phrases;
        document.getElementById("history-count").innerText = data.phrases * 2 || 0;
    });
    
    // ========== ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ ==========
    function showNotification(text, type = 'info') {
        const colors = { error: '#f44336', success: '#4CAF50', warning: '#ff9800', info: '#2196F3' };
        const notification = document.createElement('div');
        notification.style.cssText = `
            position: fixed; top: 20px; right: 20px; 
            background: ${colors[type]}; color: white; padding: 15px 25px; border-radius: 5px; 
            z-index: 1000; animation: slideIn 0.3s;
            font-family: Arial; box-shadow: 0 4px 12px rgba(0,0,0,0.15);
        `;
        notification.innerText = text;
        document.body.appendChild(notification);
        setTimeout(() => {
            notification.style.animation = 'slideOut 0.3s forwards';
            setTimeout(() => notification.remove(), 300);
        }, 3000);
    }
    
    // Добавляем стили для анимаций
    const style = document.createElement('style');
    style.textContent = `
        @keyframes slideIn { from { transform: translateX(100%); opacity: 0; } to { transform: translateX(0); opacity: 1; } }
        @keyframes slideOut { from { transform: translateX(0); opacity: 1; } to { transform: translateX(100%); opacity: 0; } }
    `;
    document.head.appendChild(style);
</script>
    </body>
    </html>
    """.replace("{ICE_SERVERS_JSON}", ICE_SERVERS_JSON)

@app.route("/student")
def student():
    return """
<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>Lecture Translation - Student</title>
<style>
body { 
    font-family: Arial, sans-serif; 
    background: #f0f2f5;
    margin: 0;
    padding: 20px;
}
.container {
    max-width: 1000px;
    margin: 0 auto;
    background: white;
    border-radius: 15px;
    box-shadow: 0 5px 20px rgba(0,0,0,0.1);
    overflow: hidden;
}
.header {
    background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
    color: white;
    padding: 30px;
    text-align: center;
}
.controls {
    padding: 20px;
    background: #f8f9fa;
    border-bottom: 1px solid #eee;
    display: flex;
    gap: 10px;
    flex-wrap: wrap;
    align-items: center;
}
#verificationBox {
    display: block;
    padding: 20px;
    background: #fff3cd;
    border: 2px solid #ffc107;
    border-radius: 10px;
    margin: 20px;
    text-align: center;
}
.code-input {
    font-size: 24px;
    padding: 15px;
    width: 200px;
    text-align: center;
    letter-spacing: 5px;
    border: 3px solid #667eea;
    border-radius: 10px;
    margin: 10px;
}
.status-badge {
    display: inline-block;
    padding: 5px 15px;
    border-radius: 20px;
    font-size: 14px;
    margin-left: 10px;
}
.status-verified {
    background: #d4edda;
    color: #155724;
}
.status-pending {
    background: #fff3cd;
    color: #856404;
}
.translation-box {
    padding: 20px;
    min-height: 200px;
    border: 1px solid #e0e0e0;
    border-radius: 10px;
    margin: 20px;
    background: #f8f9fa;
}
.history-box {
    padding: 20px;
    max-height: 300px;
    overflow-y: auto;
}
#assistantBox {
    animation: slideDown 0.3s ease;
}
.dropdown {
    position: relative;
    display: inline-block;
}
.dropdown-content {
    display: none;
    position: absolute;
    background: white;
    min-width: 200px;
    box-shadow: 0 8px 16px rgba(0,0,0,0.2);
    z-index: 1;
    border-radius: 5px;
}
.dropdown-content button {
    width: 100%;
    text-align: left;
    padding: 12px;
    border: none;
    background: none;
    cursor: pointer;
}
.dropdown-content button:hover {
    background: #f0f0f0;
}
.modal {
    display: none;
    position: fixed;
    top: 0;
    left: 0;
    width: 100%;
    height: 100%;
    background: rgba(0,0,0,0.5);
    z-index: 1000;
}
.modal-content {
    background: white;
    width: 80%;
    max-width: 800px;
    margin: 50px auto;
    border-radius: 10px;
    max-height: 80vh;
    overflow-y: auto;
}
.modal-header {
    padding: 20px;
    border-bottom: 1px solid #eee;
    display: flex;
    justify-content: space-between;
}
.modal-body {
    padding: 20px;
}
@keyframes slideDown {
    from {
        opacity: 0;
        transform: translateY(-20px);
    }
    to {
        opacity: 1;
        transform: translateY(0);
    }
}
#assistantHistory {
    scrollbar-width: thin;
    scrollbar-color: #4CAF50 #f1f8e9;
}
#assistantHistory::-webkit-scrollbar {
    width: 8px;
}
#assistantHistory::-webkit-scrollbar-track {
    background: #f1f8e9;
}
#assistantHistory::-webkit-scrollbar-thumb {
    background-color: #4CAF50;
    border-radius: 4px;
}
#screenShareContainer {
    margin: 20px;
    padding: 20px;
    background: #1a1a1a;
    border-radius: 10px;
    color: white;
}
</style>
</head>
<body>
    <div class="header">
        <h1>🎓 Lecture Translator</h1>
        <div style="display: flex; justify-content: center; align-items: center; gap: 10px; flex-wrap: wrap;">
            <div class="status-badge" id="presenceStatus">❓ Not confirmed</div>
            <div class="status-badge" style="background: #e3f2fd; color: #1976d2;" id="studentIdDisplay"></div>
            <div class="status-badge" style="background: #fff3cd; color: #856404;" id="phraseCountDisplay">📝 0</div>
        </div>
    </div>
    
    <div id="verificationBox">
        <h2>🔐 Confirm Attendance</h2>
        <p>Enter the 6-digit code from the teacher's screen:</p>
        <input type="text" id="lectureCode" class="code-input" 
               maxlength="6" placeholder="XXXXXX" autocomplete="off" autofocus>
        <br>
        <button onclick="verifyCode()" style="padding: 15px 30px; font-size: 18px; margin: 10px;">
            ✅ Confirm
        </button>
        <p id="codeTimer" style="color: red; font-weight: bold; margin-top: 10px;"></p>
        <p style="color: #666; font-size: 14px;">
            Code updates every 45 seconds<br>
            ⚠️ Do not close this window
        </p>
    </div>
    
    <div id="mainInterface" style="display: none;">
        <div class="controls">
            <select id="langSelect">
                <option value="" disabled selected>Select language</option>
                <option value="en">🇺🇸 English</option>
                <option value="de">🇩🇪 German</option>
                <option value="kk">🇰🇿 Kazakh</option>
                <option value="ru">🇷🇺 Russian</option>
                <option value="ja">🇯🇵 Japanese</option>
                <option value="ko">🇰🇷 Korean</option>
                <option value="vi">🇻🇳 Vietnamese</option>
                <option value="th">🇹🇭 Thai</option>
                <option value="ms">🇲🇾 Malay</option>
                <option value="id">🇮🇩 Indonesian</option>
                <option value="mn">🇲🇳 Mongolian</option>
                <option value="hy">🇦🇲 Armenian</option>
                <option value="it">🇮🇹 Italian</option>
                <option value="fr">🇫🇷 French</option>
                <option value="es">🇪🇸 Spanish</option>
                <option value="zh">🇨🇳 Chinese</option>
            </select>
            
            <button onclick="toggleSound()" id="soundBtn">🔊 Sound off</button>
            <button onclick="toggleAssistant()" style="margin-left: 10px; background: #4CAF50; color: white;" id="assistantBtn">🤖 Xiao Shu Assistant</button>
            <button onclick="changeStudentId()" style="margin-left: 10px;">🔄 Change Student ID</button>
            <button onclick="debugWebRTC()" style="background: #f39c12; color: white;">🔍 Debug WebRTC</button>
            <button onclick="forceReconnect()" style="background: #e74c3c; color: white;">🔄 Force Reconnect</button>

            <div class="dropdown">
                <button onclick="toggleHistoryDropdown()" style="background: #6c5ce7; color: white;">
                    📚 Lecture History ▼
                </button>
                <div id="historyDropdown" class="dropdown-content">
                    <button onclick="getFullHistory()">📜 Full History</button>
                    <button onclick="getLectureSummary()">📋 Get Summary</button>
                    <button onclick="searchInLecture()">🔍 Search</button>
                    <button onclick="exportLecture()">📥 Export</button>
                </div>
            </div>
            
            <button onclick="checkScreenShareStatus()" style="background: #9b59b6; color: white;">📺 Check Stream</button>
            <button onclick="requestVerificationAgain()" style="margin-left: auto;">🔄 Change Code</button>
        </div>
        
        <div id="screenShareContainer" style="display: none;">
            <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 15px;">
                <h3 style="margin: 0; color: white;">📺 Teacher's Screen</h3>
                <span id="screenStatus" style="background: #ff9800; color: white; padding: 5px 10px; border-radius: 5px; font-size: 14px;">🟡 Connecting...</span>
            </div>
            <video id="webrtcVideo" autoplay playsinline style="width: 100%; max-width: 800px; border: 3px solid #4CAF50; border-radius: 10px; background: #000;"></video>
        </div>
        
        <div class="translation-box">
            <h3>📝 Current Translation:</h3>
            <div id="currentTranslation">
                <em>Waiting for lecture to start...</em>
            </div>
            <div id="original" style="margin-top: 10px; color: #666; font-size: 14px;"></div>
        </div>

        <div id="assistantBox" style="display: none; margin: 20px; padding: 20px; background: #f1f8e9; border: 2px solid #4CAF50; border-radius: 10px;">
            <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 15px;">
                <h3 style="margin: 0; color: #2e7d32;">🤖 Xiao Shu - Your Math Assistant</h3>
                <button onclick="toggleAssistant()" style="background: none; border: none; font-size: 20px; cursor: pointer;">✖</button>
            </div>
            
            <div id="assistantHistory" style="max-height: 300px; overflow-y: auto; margin-bottom: 15px; padding: 10px; background: white; border-radius: 5px;">
                <div style="color: #666; text-align: center; padding: 20px;" id="assistantPlaceholder">
                    👋 Hello! I'm Xiao Shu, your math assistant.<br>
                    I have access to the full lecture history. Ask me anything!
                </div>
            </div>
            
            <div style="display: flex; gap: 10px;">
                <input type="text" id="assistantQuery" placeholder="Enter your question..." 
                       style="flex: 1; padding: 12px; border: 2px solid #4CAF50; border-radius: 5px; font-size: 16px;"
                       onkeypress="if(event.key==='Enter') sendAssistantQuery()">
                <button onclick="sendAssistantQuery()" style="padding: 12px 20px; background: #4CAF50; color: white; border: none; border-radius: 5px; cursor: pointer; font-size: 16px;">
                    Send
                </button>
            </div>
        </div>
        
        <div class="history-box">
            <h3>📜 Translation History:</h3>
            <div id="historyList">
                <em>History will appear here...</em>
            </div>
        </div>
    </div>

    <div id="historyModal" class="modal">
        <div class="modal-content">
            <div class="modal-header">
                <h2 id="modalTitle">Lecture History</h2>
                <button onclick="closeModal()" style="font-size: 24px; background: none; border: none;">✖</button>
            </div>
            <div id="modalContent" class="modal-body">
                Loading...
            </div>
        </div>
    </div>

    <script src="https://cdnjs.cloudflare.com/ajax/libs/socket.io/4.7.2/socket.io.js"></script>
    <script>
    const socket = io();
    let studentProfile = {
        id: localStorage.getItem("student_id"),
        name: ""
    };

    function requestStudentId() {
        return new Promise((resolve) => {
            let storedId = localStorage.getItem("student_id");
            
            if (storedId && /^\\d{6,}$/.test(storedId)) {
                resolve(storedId);
                return;
            }
            
            const modal = document.createElement('div');
            modal.style.cssText = `
                position: fixed; top: 0; left: 0; width: 100%; height: 100%;
                background: rgba(0,0,0,0.5); z-index: 2000;
                display: flex; justify-content: center; align-items: center;
            `;
            
            modal.innerHTML = `
                <div style="background: white; padding: 30px; border-radius: 15px; max-width: 400px; width: 90%;">
                    <h2 style="margin-top: 0; color: #333;">🎓 Enter Student ID</h2>
                    <p style="color: #666; margin-bottom: 20px;">
                        Please enter your student ID (e.g., 2025080206)
                    </p>
                    <input type="text" id="modalStudentId" 
                           style="width: 100%; padding: 15px; font-size: 18px; 
                                  border: 2px solid #667eea; border-radius: 8px;
                                  margin-bottom: 20px; box-sizing: border-box;"
                           placeholder="Enter at least 6 digits" 
                           autocomplete="off" autofocus>
                    <button onclick="submitModalStudentId()" 
                            style="width: 100%; padding: 15px; background: #667eea; 
                                   color: white; border: none; border-radius: 8px;
                                   font-size: 18px; cursor: pointer;">
                        ✅ Continue
                    </button>
                    <p style="color: #999; font-size: 12px; margin-top: 10px;">
                        Your ID will be saved locally
                    </p>
                </div>
            `;
            
            document.body.appendChild(modal);
            
            window.submitModalStudentId = () => {
                const input = document.getElementById('modalStudentId');
                const id = input.value.trim();
                
                if (/^\\d{6,}$/.test(id)) {
                    localStorage.setItem("student_id", id);
                    document.body.removeChild(modal);
                    resolve(id);
                } else {
                    alert("❌ Please enter at least 6 digits");
                    input.focus();
                }
            };
            
            document.getElementById('modalStudentId').addEventListener('keypress', (e) => {
                if (e.key === 'Enter') submitModalStudentId();
            });
        });
    }

    let assistantVisible = false;
    let assistantHistory = [];
    let lectureContext = [];

    let screenContainer = document.getElementById('screenShareContainer');
    let isReceiving = false;
    let pendingIceCandidates = [];
    let studentPeerConnection = null;

    function checkWebRTCConnection() {
        if (studentPeerConnection) {
            const state = studentPeerConnection.iceConnectionState;
            const connectionState = studentPeerConnection.connectionState;
            const statusElement = document.getElementById('screenStatus');
            
            if (statusElement) {
                if (state === 'connected' && connectionState === 'connected') {
                    statusElement.innerHTML = '🔴 LIVE - Connected';
                    statusElement.style.background = '#4CAF50';
                } else if (state === 'checking') {
                    statusElement.innerHTML = '🟡 Connecting...';
                    statusElement.style.background = '#ff9800';
                } else if (state === 'disconnected' || state === 'failed') {
                    statusElement.innerHTML = '⚫ Disconnected';
                    statusElement.style.background = '#f44336';
                }
            }
        }
    }

    function debugWebRTC() {
        if (studentPeerConnection) {
            console.log('=== WebRTC Debug Info ===');
            console.log('Connection state:', studentPeerConnection.connectionState);
            console.log('ICE connection state:', studentPeerConnection.iceConnectionState);
            console.log('ICE gathering state:', studentPeerConnection.iceGatheringState);
            console.log('Signaling state:', studentPeerConnection.signalingState);
            console.log('Remote description:', studentPeerConnection.remoteDescription ? 'Set' : 'Not set');
            console.log('Local description:', studentPeerConnection.localDescription ? 'Set' : 'Not set');
            console.log('Pending ICE candidates:', pendingIceCandidates.length);
            
            const receivers = studentPeerConnection.getReceivers();
            console.log('Receivers:', receivers.length);
            receivers.forEach((receiver, i) => {
                console.log(`Receiver ${i}:`, receiver.track.kind, receiver.track.id);
            });
            
            const videoElement = document.getElementById('webrtcVideo');
            if (videoElement) {
                console.log('Video element readyState:', videoElement.readyState);
                console.log('Video element srcObject:', videoElement.srcObject ? 'Set' : 'Not set');
            }
        } else {
            console.log('No WebRTC connection');
        }
    }

    function forceReconnect() {
        console.log('📺 Принудительное переподключение...');
        if (studentPeerConnection) {
            studentPeerConnection.close();
            studentPeerConnection = null;
        }
        pendingIceCandidates = [];
        socket.emit('request_webrtc_restart', { studentId: studentProfile.id });
        showNotification('🔄 Запрос на переподключение отправлен', 'info');
    }

    setInterval(checkWebRTCConnection, 2000);

    function toggleHistoryDropdown() {
        const dropdown = document.getElementById('historyDropdown');
        dropdown.style.display = dropdown.style.display === 'none' ? 'block' : 'none';
    }

    function getFullHistory() {
        if (!studentProfile.id) {
            showNotification("❌ Please enter student ID first", "error");
            return;
        }
        showModal('Loading history...');
        socket.emit("get_full_lecture_history", { student_id: studentProfile.id });
    }

    function getLectureSummary() {
        if (!studentProfile.id) {
            showNotification("❌ Please enter student ID first", "error");
            return;
        }
        showModal('Generating summary...');
        socket.emit("get_lecture_summary", {
            student_id: studentProfile.id,
            range: 'all'
        });
    }

    function searchInLecture() {
        const query = prompt("Enter search term:", "");
        if (query && query.length >= 3) {
            showModal(`Searching for "${query}"...`);
            socket.emit("search_lecture", {
                student_id: studentProfile.id,
                query: query
            });
        } else if (query) {
            showNotification("❌ Search term must be at least 3 characters", "warning");
        }
    }

    function exportLecture() {
        if (!studentProfile.id) {
            showNotification("❌ Please enter student ID first", "error");
            return;
        }
        const format = prompt("Enter export format (txt, md, json):", "txt");
        if (format && ['txt', 'md', 'json'].includes(format)) {
            showModal('Preparing export...');
            socket.emit("export_lecture", {
                student_id: studentProfile.id,
                format: format
            });
        }
    }

    function showModal(content) {
        document.getElementById('modalContent').innerHTML = content;
        document.getElementById('historyModal').style.display = 'block';
    }

    function closeModal() {
        document.getElementById('historyModal').style.display = 'none';
    }

    function toggleAssistant() {
        const assistantBox = document.getElementById("assistantBox");
        if (!assistantVisible) {
            assistantBox.style.display = "block";
            assistantVisible = true;
            document.getElementById("assistantQuery").focus();
        } else {
            assistantBox.style.display = "none";
            assistantVisible = false;
        }
    }

    function sendAssistantQuery() {
        const queryInput = document.getElementById("assistantQuery");
        const query = queryInput.value.trim();
        
        if (!query) return;
        if (!studentProfile.id) {
            showNotification("❌ Please enter student ID first", "error");
            return;
        }
        
        addAssistantMessage("user", query);
        queryInput.value = "";
        addAssistantMessage("assistant", "⏳ Xiao Shu is thinking...", "loading");
        
        fetch('/api/assistant', {
            method: 'POST',
            headers: {'Content-Type': 'application/json'},
            body: JSON.stringify({
                student_id: studentProfile.id,
                query: query,
                context: lectureContext.slice(-20)
            })
        })
        .then(response => response.json())
        .then(data => {
            removeLastAssistantMessage();
            if (data.status === 'success') {
                addAssistantMessage("assistant", data.answer);
            } else {
                addAssistantMessage("assistant", "❌ " + data.answer);
            }
        })
        .catch(error => {
            removeLastAssistantMessage();
            addAssistantMessage("assistant", "❌ Connection error");
            console.error('Error:', error);
        });
    }

    function verifyCode() {
        const code = document.getElementById("lectureCode").value.trim().toUpperCase();
        if (code.length === 6) {
            socket.emit("verify_code", {
                code: code,
                student_id: studentProfile.id
            });
            showNotification("⏳ Verifying code...", "info");
        } else {
            showNotification("⚠️ Please enter 6-digit code", "warning");
            document.getElementById("lectureCode").focus();
        }
    }

    function addAssistantMessage(role, text, type = "normal") {
        const historyDiv = document.getElementById("assistantHistory");
        const placeholder = document.getElementById("assistantPlaceholder");
        
        if (placeholder) placeholder.style.display = "none";
        
        const messageDiv = document.createElement("div");
        messageDiv.style.marginBottom = "15px";
        messageDiv.style.padding = "10px";
        messageDiv.style.borderRadius = "5px";
        messageDiv.style.maxWidth = "80%";
        
        if (role === "user") {
            messageDiv.style.backgroundColor = "#e3f2fd";
            messageDiv.style.marginLeft = "20%";
            messageDiv.style.textAlign = "right";
            messageDiv.innerHTML = `<strong>👤 You:</strong><br>${text}`;
        } else {
            messageDiv.style.backgroundColor = "#f1f8e9";
            messageDiv.style.marginRight = "20%";
            
            if (type === "loading") {
                messageDiv.innerHTML = `<strong>🤖 Xiao Shu:</strong><br>${text}`;
                messageDiv.id = "loadingMessage";
            } else {
                messageDiv.innerHTML = `<strong>🤖 Xiao Shu:</strong><br>${text}`;
            }
        }
        
        historyDiv.appendChild(messageDiv);
        historyDiv.scrollTop = historyDiv.scrollHeight;
        assistantHistory.push({role, text, timestamp: new Date()});
    }

    function removeLastAssistantMessage() {
        const loadingMsg = document.getElementById("loadingMessage");
        if (loadingMsg) loadingMsg.remove();
    }

    let selectedLang = "en";
    let soundEnabled = false;
    let history = [];
    let verificationTimer;

    function getUrlParameter(name) {
        name = name.replace(/[\\[]/, '\\\\[').replace(/[\\]]/, '\\\\]');
        var regex = new RegExp('[\\\\?&]' + name + '=([^&#]*)');
        var results = regex.exec(location.search);
        return results === null ? '' : decodeURIComponent(results[1].replace(/\\+/g, ' '));
    }

    function changeStudentId() {
        const newId = prompt("Enter new student ID:", "");
        if (newId && /^\\d{6,}$/.test(newId)) {
            studentProfile.id = newId;
            localStorage.setItem("student_id", newId);
            updateStudentIdDisplay();
            showNotification(`✅ Student ID updated: ${newId}`, "success");
            
            if (document.getElementById("mainInterface").style.display === "block") {
                document.getElementById("mainInterface").style.display = "none";
                document.getElementById("verificationBox").style.display = "block";
                socket.emit("request_verification");
            }
        } else {
            alert("❌ Invalid student ID format!");
        }
    }

    function checkScreenShareStatus() {
        fetch('/api/screen_share_status')
            .then(r => r.json())
            .then(data => {
                if (data.active) {
                    showNotification(`📺 Stream active (since ${data.since || 'unknown'})`, 'success');
                } else {
                    showNotification('📺 Stream not active', 'warning');
                }
            })
            .catch(err => {
                showNotification('❌ Error checking stream status', 'error');
            });
    }

    function updateStudentIdDisplay() {
        const idDisplay = document.getElementById("studentIdDisplay");
        if (idDisplay) {
            idDisplay.innerHTML = `🆔 ${studentProfile.id}`;
        }
    }

    setInterval(() => {
        if (socket.connected && studentProfile.id) {
            socket.emit("student_active", {
                student_id: studentProfile.id,
                timestamp: Date.now()
            });
        }
    }, 10000);

    socket.on("disconnect", () => {
        showNotification("⚠️ Connection lost, reconnecting...", "warning");
        if (isReceiving) {
            showNotification('⚠️ Server connection lost', 'warning');
            const videoElement = document.getElementById('webrtcVideo');
            if (videoElement) videoElement.style.opacity = '0.3';
        }
    });

    socket.on("reconnect", () => {
        showNotification("✅ Reconnected successfully", "success");
        if (studentProfile.id && document.getElementById("mainInterface").style.display === "block") {
            socket.emit("restore_session", { student_id: studentProfile.id });
        }
        fetch('/api/screen_share_status')
            .then(r => r.json())
            .then(data => {
                if (data.active) {
                    showNotification('📺 Stream resumed', 'success');
                    const videoElement = document.getElementById('webrtcVideo');
                    if (videoElement) videoElement.style.opacity = '1';
                }
            });
    });

    socket.on("session_restored", (data) => {
        if (data.success) {
            showNotification("✅ Session restored", "success");
        }
    });

    updateStudentIdDisplay();

    const urlCode = getUrlParameter('code');
    if (urlCode) {
        setTimeout(() => showNotification("📲 QR code detected! Auto-verification...", "info"), 100);
    }

    function unlockAudio() {
        const u = new SpeechSynthesisUtterance(" ");
        u.volume = 0;
        speechSynthesis.speak(u);
    }

    function toggleSound() {
        soundEnabled = !soundEnabled;
        const btn = document.getElementById("soundBtn");
        if (soundEnabled) {
            unlockAudio();
            btn.innerText = "🔊 Sound on";
            speakLast();
        } else {
            btn.innerText = "🔇 Sound off";
            speechSynthesis.cancel();
        }
    }

    function speakLast() {
        if (!history.length) return;
        speak(history[0].translation);
    }

    let soundQueue = [];
    let isSpeaking = false;

    function speak(text) {
        if (!soundEnabled || !text) return;
        soundQueue.push(text);
        if (!isSpeaking) processSoundQueue();
    }

    function processSoundQueue() {
        if (!soundQueue.length) {
            isSpeaking = false;
            return;
        }
        isSpeaking = true;
        const text = soundQueue.shift();
        const utterance = new SpeechSynthesisUtterance(text);
        const langMap = {
            en: "en-US", ru: "ru-RU", kk: "kk-KZ",
            de: "de-DE", ja: "ja-JP", ko: "ko-KR", zh: "zh-CN"
        };
        utterance.lang = langMap[selectedLang] || "en-US";
        utterance.rate = 1.0;
        utterance.pitch = 1.0;
        utterance.onend = () => processSoundQueue();
        speechSynthesis.speak(utterance);
    }
    
    socket.on("connect", () => {
        updateStatus("🔗 Connected to server", "pending");
        socket.emit("request_verification");
        setInterval(() => {
            socket.emit("heartbeat", {
                visibility: document.visibilityState,
                focused: document.hasFocus()
            });
        }, 5000);
    });
    
    socket.on("verification_required", (data) => {
        document.getElementById("verificationBox").style.display = "block";
        document.getElementById("mainInterface").style.display = "none";
        updateStatus("⏳ Verification needed", "pending");
        startCodeTimer();
        
        const codeInput = document.getElementById("lectureCode");
        codeInput.focus();
        
        if (urlCode) {
            codeInput.value = urlCode;
            setTimeout(() => verifyCode(), 500);
        }
    });
    
    socket.on("verification_result", (data) => {
        if (data.requires_id) {
            requestStudentId().then(id => {
                studentProfile.id = id;
                updateStudentIdDisplay();
                
                const code = document.getElementById("lectureCode").value.trim().toUpperCase();
                socket.emit("verify_code", {
                    code: code,
                    student_id: id
                });
            });
        } else if (data.success) {
            document.getElementById("verificationBox").style.display = "none";
            document.getElementById("mainInterface").style.display = "block";
            updateStatus("✅ Attendance confirmed", "verified");
            clearInterval(verificationTimer);
            
            document.getElementById("langSelect").value = "en";
            socket.emit("set_language", {lang: "en"});
            showNotification(`✅ Attendance confirmed!`, "success");
        } else {
            showNotification(`❌ ${data.message}`, "error");
            document.getElementById("lectureCode").value = "";
            document.getElementById("lectureCode").focus();
            setTimeout(() => socket.emit("request_verification"), 2000);
        }
    });

    socket.on("stats", (data) => {
        const countDisplay = document.getElementById("phraseCountDisplay");
        if (countDisplay) countDisplay.innerHTML = `📝 ${data.phrases}`;
    });
    
    socket.on("new_translation", (data) => {
        if (data.is_final && soundEnabled) speak(data.translation);
        
        if (data.translation && data.translation.trim() !== "") {
            document.getElementById("currentTranslation").innerHTML = 
                `<strong style="color: #2c3e50;">${data.translation}</strong>`;
            
            if (data.original && data.original.trim() !== "") {
                document.getElementById("original").innerHTML = 
                    `<i>Original: "${data.original}"</i>`;
            }
            
            addToHistory(data);
            
            if (data.is_final) {
                lectureContext.push({
                    original: data.original,
                    translation: data.translation,
                    timestamp: new Date().toLocaleTimeString()
                });
                if (lectureContext.length > 50) lectureContext.shift();
            }
        }
    });

    socket.on('screen_share_started', () => {
        console.log('📺 Получено событие: screen_share_started');
        showNotification('📺 Teacher started screen sharing', 'success');
        isReceiving = true;
        screenContainer.style.display = 'block';
        setTimeout(() => {
            socket.emit('request_webrtc_restart', { studentId: studentProfile.id });
        }, 1000);
    });

    socket.on('webrtc_offer', async (data) => {
        console.log('📺 Получен WebRTC offer');
        
        // ⚡ ОБНОВЛЕННАЯ КОНФИГУРАЦИЯ с вашими TURN серверами от Metered.ca
        const configuration = {
        iceServers: {ICE_SERVERS_JSON},
        iceCandidatePoolSize: 10,
        iceTransportPolicy: 'all'
    };
        
        if (studentPeerConnection) {
            studentPeerConnection.close();
        }
        
        studentPeerConnection = new RTCPeerConnection(configuration);
        
        const videoElement = document.getElementById('webrtcVideo');
        const pendingCandidates = [];
        
        studentPeerConnection.ontrack = (event) => {
            console.log('✅ Получен видеотрек');
            if (videoElement.srcObject !== event.streams[0]) {
                videoElement.srcObject = event.streams[0];
                videoElement.play().catch(e => console.log('Play error:', e));
                showNotification('✅ Video stream started', 'success');
            }
        };
        
        studentPeerConnection.onicecandidate = (event) => {
            if (event.candidate) {
                console.log(`📡 ICE кандидат студента (${event.candidate.type}):`, {
                    type: event.candidate.type,
                    protocol: event.candidate.protocol,
                    address: event.candidate.address || 'no-address',
                    port: event.candidate.port
                });
                
                if (event.candidate.type === 'relay') {
                    console.log('✅ TURN сервер РАБОТАЕТ! Релейный кандидат получен');
                }
                
                if (studentPeerConnection.remoteDescription) {
                    socket.emit('webrtc_ice_candidate', {
                        studentId: studentProfile.id,
                        candidate: event.candidate,
                        target: 'teacher'
                    });
                } else {
                    pendingCandidates.push(event.candidate);
                }
            }
        };
        
        studentPeerConnection.onicecandidateerror = (event) => {
            console.error('❌ Ошибка ICE кандидата (студент):', {
                url: event.url,
                errorCode: event.errorCode,
                errorText: event.errorText
            });
        };
        
        studentPeerConnection.onicegatheringstatechange = () => {
            console.log('📺 Сбор ICE кандидатов (студент):', studentPeerConnection.iceGatheringState);
        };
        
        studentPeerConnection.oniceconnectionstatechange = () => {
            console.log('📺 ICE состояние (студент):', studentPeerConnection.iceConnectionState);
            const statusElement = document.getElementById('screenStatus');
            if (studentPeerConnection.iceConnectionState === 'connected') {
                showNotification('✅ Connected to stream', 'success');
                if (statusElement) {
                    statusElement.innerHTML = '🔴 LIVE - Connected';
                    statusElement.style.background = '#4CAF50';
                }
            } else if (studentPeerConnection.iceConnectionState === 'disconnected') {
                showNotification('⚠️ Stream connection lost', 'warning');
                if (statusElement) {
                    statusElement.innerHTML = '⚫ Disconnected';
                    statusElement.style.background = '#f44336';
                }
            } else if (studentPeerConnection.iceConnectionState === 'failed') {
                console.error('❌ ICE failed (студент)');
                showNotification('❌ Failed to connect to stream', 'error');
                if (statusElement) {
                    statusElement.innerHTML = '❌ Failed';
                    statusElement.style.background = '#f44336';
                }
            }
        };
        
        studentPeerConnection.onconnectionstatechange = () => {
            console.log('📺 Общее состояние (студент):', studentPeerConnection.connectionState);
        };
        
        studentPeerConnection.flushPendingCandidates = function() {
            console.log(`📺 Отправка ${pendingCandidates.length} накопленных кандидатов студента`);
            pendingCandidates.forEach(candidate => {
                socket.emit('webrtc_ice_candidate', {
                    studentId: studentProfile.id,
                    candidate: candidate,
                    target: 'teacher'
                });
            });
            pendingCandidates.length = 0;
        };
        
        await studentPeerConnection.setRemoteDescription(new RTCSessionDescription(data.offer));
        
        const answer = await studentPeerConnection.createAnswer();
        await studentPeerConnection.setLocalDescription(answer);
        
        if (studentPeerConnection.flushPendingCandidates) {
            studentPeerConnection.flushPendingCandidates();
        }
        
        socket.emit('webrtc_answer', {
            studentId: studentProfile.id,
            answer: studentPeerConnection.localDescription
        });
        
        showNotification('📺 Connecting to stream...', 'info');
    });

    socket.on('webrtc_ice_candidate', (data) => {
        if (!studentPeerConnection) {
            pendingIceCandidates.push(data.candidate);
            return;
        }
        
        if (studentPeerConnection.remoteDescription) {
            studentPeerConnection.addIceCandidate(new RTCIceCandidate(data.candidate))
                .then(() => console.log('✅ ICE кандидат добавлен'))
                .catch(e => console.error('❌ Ошибка добавления ICE кандидата:', e));
        } else {
            pendingIceCandidates.push(data.candidate);
        }
    });

    socket.on('webrtc_restart', () => {
        console.log('📺 Перезапуск WebRTC соединения');
        if (studentPeerConnection) {
            studentPeerConnection.close();
            studentPeerConnection = null;
        }
        pendingIceCandidates = [];
        socket.emit('request_webrtc_restart', { studentId: studentProfile.id });
    });

    socket.on('screen_share_stopped', () => {
        console.log('📺 Получено событие: screen_share_stopped');
        if (studentPeerConnection) {
            studentPeerConnection.close();
            studentPeerConnection = null;
        }
        const container = document.getElementById('screenShareContainer');
        if (container) {
            container.style.display = 'none';
        }
        isReceiving = false;
        showNotification('📺 Stream ended', 'info');
    });

    socket.on("full_lecture_history", (data) => {
        let html = `<p>Total entries: ${data.total}</p>`;
        html += '<div style="max-height: 500px; overflow-y: auto;">';
        data.history.forEach(entry => {
            html += `
                <div style="margin-bottom: 15px; padding: 10px; background: #f8f9fa; border-radius: 5px;">
                    <small style="color: #666;">${entry.time}</small>
                    <div><strong>${entry.text}</strong></div>
                    ${entry.translation ? `<div style="color: #28a745;">→ ${entry.translation}</div>` : ''}
                    <small style="color: #999;">Type: ${entry.type}</small>
                </div>
            `;
        });
        html += '</div>';
        document.getElementById('modalTitle').innerHTML = '📜 Lecture History';
        document.getElementById('modalContent').innerHTML = html;
    });

    socket.on("lecture_summary", (data) => {
        const html = `<div style="white-space: pre-wrap; line-height: 1.6;">${data.summary}</div>`;
        document.getElementById('modalTitle').innerHTML = '📋 Lecture Summary';
        document.getElementById('modalContent').innerHTML = html;
    });

    socket.on("search_results", (data) => {
        if (data.results.length === 0) {
            document.getElementById('modalContent').innerHTML = '<p>No results found.</p>';
            return;
        }
        let html = `<p>Found ${data.count} results for "${data.query}":</p>`;
        data.results.forEach(result => {
            html += `
                <div style="margin-bottom: 15px; padding: 10px; background: #f8f9fa; border-radius: 5px;">
                    <small>${result.time}</small>
                    <div><strong>${result.text}</strong></div>
                    ${result.translation ? `<div>→ ${result.translation}</div>` : ''}
                </div>
            `;
        });
        document.getElementById('modalTitle').innerHTML = `🔍 Search: ${data.query}`;
        document.getElementById('modalContent').innerHTML = html;
    });

    socket.on("lecture_export", (data) => {
        const blob = new Blob([data.content], { type: 'text/plain' });
        const url = window.URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = url;
        a.download = data.filename;
        a.click();
        window.URL.revokeObjectURL(url);
        closeModal();
        showNotification(`✅ Exported as ${data.filename}`, "success");
    });

    socket.on("history_error", (data) => {
        showNotification(`❌ ${data.error}`, "error");
        closeModal();
    });

    socket.on("summary_error", (data) => {
        showNotification(`❌ ${data.error}`, "error");
        closeModal();
    });

    socket.on("search_error", (data) => {
        showNotification(`❌ ${data.error}`, "error");
        closeModal();
    });

    socket.on("export_error", (data) => {
        showNotification(`❌ ${data.error}`, "error");
        closeModal();
    });
    
    function requestVerificationAgain() {
        socket.emit("request_verification");
        showNotification("🔄 Requesting new code...", "info");
    }
    
    function startCodeTimer() {
        let secondsLeft = 45;
        clearInterval(verificationTimer);
        verificationTimer = setInterval(() => {
            secondsLeft--;
            if (secondsLeft >= 0) {
                document.getElementById("codeTimer").innerText = 
                    `⏰ Code will update in: ${secondsLeft} seconds`;
                if (secondsLeft <= 5) {
                    document.getElementById("codeTimer").style.color = "#dc3545";
                }
                if (secondsLeft <= 0) {
                    clearInterval(verificationTimer);
                    document.getElementById("codeTimer").innerText = "🔄 Code updated!";
                    document.getElementById("lectureCode").value = "";
                    setTimeout(() => socket.emit("request_verification"), 1000);
                }
            }
        }, 1000);
    }
    
    function updateStatus(text, type) {
        const statusEl = document.getElementById('presenceStatus');
        statusEl.innerHTML = text;
        statusEl.className = type === "verified" ? "status-badge status-verified" : "status-badge status-pending";
    }
    
    document.getElementById("lectureCode").addEventListener("keypress", (e) => {
        if (e.key === "Enter") verifyCode();
    });
    
    document.getElementById("langSelect").onchange = (e) => {
        selectedLang = e.target.value;
        socket.emit("set_language", {lang: selectedLang});
        showNotification(`🌍 Language changed to: ${e.target.options[e.target.selectedIndex].text}`);
    };
    
    function addToHistory(data) {
        const historyItem = {
            timestamp: new Date().toLocaleTimeString(),
            original: data.original || '',
            translation: data.translation || '',
            lang: selectedLang
        };
        history.unshift(historyItem);
        if (history.length > 10) history.pop();
        
        const historyList = document.getElementById('historyList');
        historyList.innerHTML = history.map(item => `
            <div style="margin-bottom: 10px; padding: 10px; background: #f8f9fa; border-radius: 5px;">
                <small style="color:#666">${item.timestamp}</small>
                <div><strong>${item.translation}</strong></div>
                <small style="color:#888">${item.original}</small>
            </div>
        `).join('');
    }
    
    function showNotification(text, type = "info") {
        const colors = { success: "#4CAF50", error: "#f44336", warning: "#ff9800", info: "#2196F3" };
        const notification = document.createElement('div');
        notification.style.cssText = `
            position: fixed; top: 20px; right: 20px; background: ${colors[type]}; color: white;
            padding: 15px 25px; border-radius: 5px; z-index: 1000; animation: slideIn 0.3s;
            font-family: Arial; box-shadow: 0 4px 12px rgba(0,0,0,0.15);
        `;
        notification.innerText = text;
        document.body.appendChild(notification);
        setTimeout(() => {
            notification.style.animation = "slideOut 0.3s forwards";
            setTimeout(() => notification.remove(), 300);
        }, 3000);
    }
    
    const style = document.createElement('style');
    style.textContent = `
        @keyframes slideIn { from { transform: translateX(100%); opacity: 0; } to { transform: translateX(0); opacity: 1; } }
        @keyframes slideOut { from { transform: translateX(0); opacity: 1; } to { transform: translateX(100%); opacity: 0; } }
    `;
    document.head.appendChild(style);
    
    document.getElementById("lectureCode").focus();
</script>
</body>
</html>
""".replace("{ICE_SERVERS_JSON}", ICE_SERVERS_JSON)

# ================= QR code и другие маршруты =================
@socketio.on("request_verification")
def handle_verification_request():
    sid = request.sid
    logger.info(f"📩 Verification request from {sid}")
    socketio.emit("verification_required", {"message": "Attendance confirmation required", "timeout": 45}, to=sid)

@socketio.on("verify_code")
def handle_code_verification(data):
    if not CURRENT_SESSION_CODE or time.time() > CODE_EXPIRES_AT:
        generate_session_code()
    
    sid = request.sid
    code = data.get("code", "").strip().upper()
    student_id = data.get("student_id")

    if not student_id:
        socketio.emit("verification_result", {
            "success": False, 
            "message": "student_id_required",
            "requires_id": True
        }, to=sid)
        return

    if not re.match(r'^\d{6,}$', student_id):
        socketio.emit("verification_result", {
            "success": False, 
            "message": "Invalid student ID format. Please use at least 6 digits.",
            "requires_id": True
        }, to=sid)
        return

    success, message = verify_student_code(student_id, code)

    if success:
        if sid not in ATTENDANCE:
            ATTENDANCE[sid] = {}
        ATTENDANCE[sid]["student_id"] = student_id
        ATTENDANCE[sid]["verified"] = True
        ATTENDANCE[sid]["name"] = f"Student_{student_id[-4:]}"
        
        logger.info(f"✅ Student {student_id} verified with code {code} (socket {sid})")
        
        # Если трансляция уже идет, уведомляем нового студента
        if current_teacher_sid is not None:
            logger.info(f"📺 Трансляция уже идет, уведомляем нового студента {sid}")
            socketio.emit("screen_share_started", to=sid)
    else:
        logger.warning(f"❌ Verification failed for student {student_id}: {message}")

    socketio.emit("verification_result", {
        "success": success, 
        "message": message,
        "requires_id": False
    }, to=sid)

@socketio.on("submit_student_id")
def handle_student_id_submission(data):
    sid = request.sid
    student_id = data.get("student_id", "").strip()
    
    if not re.match(r'^\d{6,}$', student_id):
        socketio.emit("student_id_result", {
            "success": False,
            "message": "Invalid format. Please use at least 6 digits."
        }, to=sid)
        return
    
    if sid not in ATTENDANCE:
        ATTENDANCE[sid] = {}
    ATTENDANCE[sid]["temp_student_id"] = student_id
    
    logger.info(f"📝 Student ID {student_id} submitted for session {sid}")
    
    socketio.emit("student_id_result", {
        "success": True,
        "student_id": student_id,
        "message": "ID accepted. Now enter the verification code."
    }, to=sid)

@app.route("/teacher/qr")
def teacher_qr_dashboard():
    current_code = generate_session_code()
    
    base_url = "https://pretympanic-sprucely-concepcion.ngrok-free.dev"
    qr = qrcode.QRCode(version=1, box_size=15, border=4)
    qr.add_data(f"{base_url}/student?code={current_code}")
    qr.make(fit=True)
    
    img = qr.make_image(fill_color="black", back_color="white")
    
    buffered = io.BytesIO()
    img.save(buffered, format="PNG")
    img_str = base64.b64encode(buffered.getvalue()).decode()
    
    html_template = f"""
    <!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>Lecture QR Code</title>
    <style>
        body {{
            font-family: Arial, sans-serif;
            padding: 40px;
            text-align: center;
            background: #f0f2f5;
        }}
        .container {{
            max-width: 600px;
            margin: 0 auto;
            background: white;
            padding: 30px;
            border-radius: 15px;
            box-shadow: 0 5px 20px rgba(0,0,0,0.1);
        }}
        .qrcode {{
            margin: 20px 0;
            padding: 20px;
            background: white;
            border-radius: 10px;
            border: 2px solid #e0e0e0;
        }}
        .code-display {{
            font-size: 48px;
            font-weight: bold;
            letter-spacing: 10px;
            color: #2c3e50;
            margin: 20px 0;
            padding: 20px;
            background: #ecf0f1;
            border-radius: 10px;
            font-family: monospace;
        }}
        .timer {{
            font-size: 24px;
            color: #e74c3c;
            margin: 20px 0;
        }}
        .stats {{
            margin-top: 30px;
            padding: 20px;
            background: #f8f9fa;
            border-radius: 10px;
            text-align: left;
        }}
        .student-list {{
            max-height: 300px;
            overflow-y: auto;
            margin-top: 10px;
        }}
    </style>
</head>
<body>
    <div class="container">
        <h1>📱 Lecture QR Code</h1>
        <p>Code updates every 45 seconds</p>
        
        <div class="timer">
            ⏰ Time until update: <span id="countdown">45</span> seconds
        </div>
        
        <div class="code-display" id="currentCode">{current_code}</div>
        
        <div class="qrcode">
            <img src="data:image/png;base64,{img_str}" 
                 alt="QR Code" 
                 width="300" 
                 height="300">
        </div>
        
        <div class="stats">
            <h3>✅ Confirmed attendance:</h3>
            <div class="student-list" id="verifiedStudents">
                <em>Waiting for students...</em>
            </div>
            <p>Total: <span id="verifiedCount">0</span> students</p>
        </div>
        
        <div style="margin-top: 30px;">
            <button onclick="refreshQR()" style="padding: 10px 20px;">🔄 Refresh manually</button>
            <button onclick="location.reload()" style="padding: 10px 20px; margin-left: 10px;">📊 Refresh list</button>
        </div>

        <div class="info" style="margin-top: 20px; padding: 15px; background: #e3f2fd; border-radius: 10px; text-align: left;">
            <h4>📱 QR Code Information:</h4>
            <p>When scanned, the student will automatically go to the login page with the pre-filled code.</p>
            <p>They only need to click the "✅ Confirm" button.</p>
        </div>
    </div>
    
    <script src="https://cdnjs.cloudflare.com/ajax/libs/socket.io/4.7.2/socket.io.js"></script>
    <script>
        const socket = io();
        let countdown = 45;
        
        function startTimer() {{
            const timerElement = document.getElementById('countdown');
            const codeElement = document.getElementById('currentCode');
            
            setInterval(() => {{
                countdown--;
                if (countdown <= 0) {{
                    countdown = 45;
                    fetch('/api/current_code')
                        .then(r => r.json())
                        .then(data => {{
                            codeElement.textContent = data.code;
                            timerElement.textContent = '45';
                            countdown = 45;
                        }});
                }}
                timerElement.textContent = countdown;
            }}, 1000);
        }}
        
        function refreshQR() {{
            fetch('/api/current_code')
                .then(r => r.json())
                .then(data => {{
                    document.getElementById('currentCode').textContent = data.code;
                    countdown = 30;
                    document.getElementById('countdown').textContent = '30';
                }});
        }}
        
        function updateStudentList() {{
            fetch('/api/verified_students')
                .then(r => r.json())
                .then(data => {{
                    const listElement = document.getElementById('verifiedStudents');
                    const countElement = document.getElementById('verifiedCount');
                    
                    if (data.students.length > 0) {{
                        listElement.innerHTML = data.students
                            .map(student => `<div>✅ ${{student.name || student.student_name || 'Student'}} (${{student.id}}) - ${{student.time}}</div>`)
                            .join('');
                    }} else {{
                        listElement.innerHTML = '<em>No one confirmed yet</em>';
                    }}
                    
                    countElement.textContent = data.count;
                }});
        }}
        
        startTimer();
        updateStudentList();
        setInterval(updateStudentList, 5000);
    </script>
</body>
</html>
"""
    return html_template

@app.route("/api/current_code")
def api_current_code():
    if not CURRENT_SESSION_CODE or time.time() > CODE_EXPIRES_AT:
        generate_session_code()
    return jsonify({
        "code": CURRENT_SESSION_CODE,
        "expires_in": int(CODE_EXPIRES_AT - time.time())
    })

@app.route("/api/verified_students")
def api_verified_students():
    verified_list = []
    for student_id, student_data in VERIFIED_STUDENTS.items():
        if student_data["verified"]:
            student_name = "Student"
            for a in ATTENDANCE.values():
                if a.get("student_id") == student_id:
                    student_name = a.get("name", "Student")
            verified_time = datetime.fromtimestamp(student_data["verified_at"]).strftime("%H:%M:%S")
            verified_list.append({
                "id": student_id,
                "name": student_name,
                "time": verified_time
            })
    return jsonify({
        "students": verified_list,
        "count": len(verified_list)
    })

@app.route("/api/screen_share_status")
def api_screen_share_status():
    global current_teacher_sid
    if current_teacher_sid:
        start_time = "неизвестно"
        for sid, data in ATTENDANCE.items():
            if sid == current_teacher_sid and "screen_share_started" in data:
                start_time = datetime.fromtimestamp(data["screen_share_started"]).strftime("%H:%M:%S")
                break
        return jsonify({
            "active": True,
            "teacher": current_teacher_sid,
            "since": start_time
        })
    return jsonify({"active": False})

@app.route("/api/assistant", methods=["POST"])
def assistant_query():
    data = request.json
    student_id = data.get("student_id")
    query = data.get("query", "").strip()
    session_id = data.get("session_id")
    
    if not query:
        return jsonify({"error": "Empty query"}), 400
    
    question_id = add_to_lecture_history(
        text=query,
        text_type='question',
        language='en',
        speaker='student',
        metadata={'student_id': student_id, 'session_id': session_id}
    )
    
    lecture_context = []
    for entry in LECTURE_HISTORY[-200:]:
        if entry['type'] in ['recognition_final', 'translation']:
            lecture_context.append({
                'time': entry['datetime'],
                'text': entry.get('translation', entry['text']),
                'original': entry['text']
            })
    
    context_text = "\n".join([f"[{item['time']}] {item['text']}" for item in lecture_context])
    
    student_questions = [
        entry for entry in LECTURE_HISTORY 
        if entry['type'] == 'question' and 
        entry['metadata'].get('student_id') == student_id
    ][-5:]
    
    questions_context = ""
    if student_questions:
        questions_context = "\nPrevious questions from this student:\n" + "\n".join([
            f"Q: {q['text']}" for q in student_questions
        ])
    
    prompt = f"""
You are Xiao Shu, an intelligent math assistant with access to the complete lecture history.

LECTURE CONTEXT (chronological order):
{context_text}

{questions_context}

Student's question: {query}

IMPORTANT RULES:
1. Base your answer on the ACTUAL lecture content provided above
2. If the question is about a specific topic, reference the relevant part of the lecture
3. If you need more context, ask for clarification
4. Keep answers educational and concise (3-4 sentences maximum)
5. Use mathematical notation when appropriate
6. If the question is off-topic, politely redirect to the lecture material

Your response:
"""
    
    try:
        if not DEEPSEEK_API_KEY:
            return jsonify({
                "answer": "Xiao Shu needs an API key to work. Please configure DEEPSEEK_API_KEY.",
                "status": "error"
            })
        
        resp = requests.post(
            DEEPSEEK_URL,
            headers={"Authorization": f"Bearer {DEEPSEEK_API_KEY}"},
            json={
                "model": "deepseek-chat",
                "messages": [
                    {"role": "system", "content": "You are Xiao Shu, a friendly math assistant with full access to lecture history. Answer based on the lecture content."},
                    {"role": "user", "content": prompt}
                ],
                "temperature": 0.5,
                "max_tokens": 500
            },
            timeout=15,
        )
        
        resp.raise_for_status()
        answer = resp.json()["choices"][0]["message"]["content"].strip()
        
        add_to_lecture_history(
            text=answer,
            text_type='answer',
            language='en',
            speaker='assistant',
            metadata={'student_id': student_id, 'question_id': question_id, 'session_id': session_id}
        )
        
        logger.info(f"🤖 Assistant answered student {student_id}")
        
        return jsonify({
            "answer": answer,
            "status": "success",
            "context_used": len(lecture_context)
        })
        
    except Exception as e:
        logger.error(f"❌ Assistant error: {e}")
        PERF_METRICS['errors']['assistant_error'] += 1
        return jsonify({
            "answer": "Xiao Shu is temporarily unavailable. Please try again later.",
            "status": "error"
        })

@app.route("/api/stream")
def stream_translations():
    def generate():
        last_text = ""
        try:
            while True:
                if FULL_LECTURE_TEXT and FULL_LECTURE_TEXT[-1] != last_text:
                    last_text = FULL_LECTURE_TEXT[-1]
                    yield f"data: {json.dumps({'text': last_text})}\n\n"
                time.sleep(0.5)
        except GeneratorExit:
            # Клиент закрыл SSE-соединение — корректно завершаем генератор
            logger.info("SSE /api/stream: client disconnected, generator closed")
            raise
        except Exception as e:
            logger.error(f"SSE /api/stream error: {e}")
            raise
        finally:
            # Очистка: сообщаем о закрытии потока
            logger.info("SSE /api/stream: stream closed")
    return Response(generate(), mimetype="text/event-stream")

@app.route("/api/metrics")
def api_metrics():
    avg_translation = 0
    if PERF_METRICS['translation_times']:
        avg_translation = sum(PERF_METRICS['translation_times']) / len(PERF_METRICS['translation_times'])
    
    screen_stats = {}
    if screen_share_stats['total_frames_sent'] > 0:
        screen_stats = {
            'total_frames': screen_share_stats['total_frames_sent'],
            'dropped_frames': screen_share_stats['total_frames_dropped'],
            'active_viewers': len(screen_share_stats['active_viewers']),
            'avg_frame_time': sum(screen_share_stats['frame_times']) / len(screen_share_stats['frame_times']) if screen_share_stats['frame_times'] else 0
        }
    
    return jsonify({
        'avg_translation_time': round(avg_translation, 2),
        'total_phrases': PHRASE_COUNT,
        'connected_clients': len(CONNECTED_CLIENTS),
        'errors': dict(PERF_METRICS['errors']),
        'cache_size': len(translation_cache),
        'repair_cache_size': len(REPAIR_CACHE),
        'history_size': len(LECTURE_HISTORY),
        'screen_share': screen_stats
    })
    
@app.route("/register", methods=["POST"])
def register_student():
    data = request.json
    student_id = data.get("id")
    name = data.get("name")
    
    if not student_id or not name:
        return jsonify({"error": "ID and name required"}), 400

    if student_id in STUDENTS:
        return jsonify({"error": "Student already registered"}), 400

    token = secrets.token_urlsafe(16)
    STUDENTS[student_id] = {"name": name, "token": token}

    return jsonify({"token": token})

# ================= Startup =================
if __name__ == "__main__":
    if os.path.exists("matan.pdf"):
        load_textbook_terms("matan.pdf")
    if os.path.exists("linalg.pdf"):
        load_textbook_terms("linalg.pdf")
    
    logging.getLogger('socketio').setLevel(logging.WARNING)
    logging.getLogger('engineio').setLevel(logging.WARNING)
    logging.getLogger('websocket').setLevel(logging.WARNING)
    
    if not DEEPSEEK_API_KEY:
        logger.warning("⚠️ DEEPSEEK_API_KEY not configured!")
    
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)
    
    logger.info("🚀 Starting optimized server with full lecture history...")
    
    audio_thread_obj = threading.Thread(target=audio_thread, daemon=True)
    audio_thread_obj.start()
    
    ws_thread_obj = threading.Thread(target=ws_thread, daemon=True)
    ws_thread_obj.start()
    
    time.sleep(1)
    
    logger.info("✅ Optimized server started!")
    logger.info("👨‍🏫 Teacher: http://localhost:8000")
    logger.info("🎓 Student: http://localhost:8000/student")
    logger.info("📊 Metrics: http://localhost:8000/api/metrics")
    logger.info("📺 Screen sharing: WebRTC P2P with Metered.ca TURN")
    
    try:
        socketio.run(app, 
                    host="0.0.0.0", 
                    port=8000,
                    debug=False,
                    allow_unsafe_werkzeug=True,
                    use_reloader=False)
    except KeyboardInterrupt:
        signal_handler(None, None)