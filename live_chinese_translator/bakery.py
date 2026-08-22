import asyncio
import json
import base64
import hashlib
import hmac
import logging
import os
import urllib.parse
import re
from datetime import datetime
from time import mktime
from wsgiref.handlers import format_date_time
import difflib

import numpy as np
import requests
import websockets
from aiohttp import web
from dotenv import load_dotenv
from pypinyin import lazy_pinyin, Style

load_dotenv()

# ================= Конфигурация =================
APPID = os.getenv("XF_APPID", "ga88408f")
APIKey = os.getenv("XF_API_KEY", "")
APISecret = os.getenv("XF_API_SECRET", "")
DEEPSEEK_API_KEY = os.getenv("DEEPSEEK_API_KEY")
DEEPSEEK_URL = "https://api.deepseek.com/v1/chat/completions"

SAMPLE_RATE = 16000
DEBOUNCE_SEC = 0.4

audio_queue = asyncio.Queue()
is_running = True
is_guest_mode = False

pending_text = ""
pending_task = None

lecture_transcript = []

chat_connections = set()
admin_connections = set()

# ================= Словарь терминов =================
GLOSSARY_ZH_EN = {
    "鲁邦种": "levain",
    "乳酸菌": "lactic acid bacteria",
    "酵母菌": "yeast",
    "面筋": "gluten",
    "麸质": "gluten",
    "含水量": "water content",
    "醒发": "proofing",
    "折叠": "folding",
    "水解": "autolyse",
    "搅拌": "mixing",
    "发酵": "fermentation",
    "割口": "scoring",
    "烘烤": "baking",
    "蒸汽": "steam",
    "铸铁锅": "cast iron pot",
    "面团": "dough",
    "辅料": "inclusions",
    "冷藏": "refrigeration",
    "更新激活": "refresh",
    "喂养": "feeding",
    "比例": "ratio",
    "面糊": "batter",
    "欧包": "artisan bread",
    "机械力": "mechanical force",
    "强化": "strengthen",
    "平衡": "balance",
    "弹性": "elasticity",
    "分割": "dividing",
    "揉圆": "rounding",
    "松弛": "resting",
    "整型": "shaping",
    "发酵篮": "proofing basket",
    "发酵布": "proofing cloth",
    "支撑力": "support",
    "饱满": "full",
    "手印": "fingerprint",
    "羽绒服": "down jacket",
    "耳朵": "ear",
    "上色": "browning"
}

GLOSSARY_EN_ZH = {v: k for k, v in GLOSSARY_ZH_EN.items()}

FUZZY_CORRECTIONS = {
    "路帮种": "鲁邦种",
    "鲁棒种": "鲁邦种",
    "乳酸军": "乳酸菌",
    "孝母菌": "酵母菌",
    "面金": "面筋",
    "含水两": "含水量",
    "醒花": "醒发",
    "水姐": "水解",
    "搅半": "搅拌",
    "发笑": "发酵",
    "哥口": "割口",
    "哄烤": "烘烤",
    "征气": "蒸汽",
    "住铁锅": "铸铁锅",
    "面谈": "面团",
    "腐烂": "辅料",
    "冷长": "冷藏",
    "更心激活": "更新激活",
    "胃养": "喂养",
    "鼻例": "比例",
    "面狐": "面糊",
    "藕包": "欧包",
    "肌卸力": "机械力",
    "枪化": "强化",
    "屏横": "平衡",
    "担性": "弹性",
    "分歌": "分割",
    "柔圆": "揉圆",
    "松持": "松弛",
    "整形": "整型",
    "发笑蓝": "发酵篮",
    "发笑布": "发酵布",
    "只撑力": "支撑力",
    "宝满": "饱满",
    "手淫": "手印",
    "羽容服": "羽绒服",
    "耳多": "耳朵",
    "上射": "上色"
}

def detect_language(text: str) -> str:
    if re.search(r'[\u0600-\u06FF\u0750-\u077F\u08A0-\u08FF\uFB50-\uFDFF\uFE70-\uFEFF]', text):
        return 'ar'
    if re.search(r'[\u0400-\u04FF]', text):
        return 'ru'
    if re.search(r'[\u4e00-\u9fff]', text):
        return 'zh'
    return 'en'

def correct_glossary(text: str) -> str:
    corrected = text
    for wrong, right in FUZZY_CORRECTIONS.items():
        if wrong in corrected:
            corrected = corrected.replace(wrong, right)
    words = list(GLOSSARY_ZH_EN.keys())
    for term in words:
        if term in corrected:
            continue
        for i in range(len(corrected) - len(term) + 1):
            substr = corrected[i:i+len(term)]
            if difflib.SequenceMatcher(None, substr, term).ratio() >= 0.8:
                corrected = corrected[:i] + term + corrected[i+len(term):]
                break
    return corrected

def translate_with_glossary(text: str, source_lang: str, target_lang: str) -> str:
    if not text:
        return text
    if source_lang == 'zh' and target_lang == 'en':
        text = correct_glossary(text)
        if text in GLOSSARY_ZH_EN:
            return GLOSSARY_ZH_EN[text]
    if source_lang == 'en' and target_lang == 'zh':
        if text.lower() in GLOSSARY_EN_ZH:
            return GLOSSARY_EN_ZH[text.lower()]
    lang_pair = f"{source_lang}|{target_lang}"
    url = f"https://api.mymemory.translated.net/get?q={urllib.parse.quote(text)}&langpair={lang_pair}"
    try:
        resp = requests.get(url, timeout=5)
        if resp.status_code == 200:
            data = resp.json()
            translated = data.get("responseData", {}).get("translatedText", text)
            if translated.startswith("@@") or translated == text:
                if source_lang != 'en' and target_lang != 'en':
                    temp = translate_with_glossary(text, source_lang, 'en')
                    if temp and temp != text:
                        return translate_with_glossary(temp, 'en', target_lang)
            if source_lang == 'zh' and target_lang == 'en':
                for zh_term, en_term in GLOSSARY_ZH_EN.items():
                    if zh_term in text and en_term.lower() not in translated.lower():
                        translated = translated + f" ({en_term})"
            elif source_lang == 'en' and target_lang == 'zh':
                for en_term, zh_term in GLOSSARY_EN_ZH.items():
                    if en_term.lower() in text.lower() and zh_term not in translated:
                        translated = translated + f"({zh_term})"
            return translated
    except Exception as e:
        logging.error(f"Translation error: {e}")
    return text

def get_pinyin(chinese_text: str) -> str:
    if not chinese_text:
        return ""
    pinyin_list = lazy_pinyin(chinese_text, style=Style.NORMAL)
    return ' '.join(pinyin_list)

# ================= DeepSeek AI Assistant =================
async def deepseek_answer(question: str, lang: str, lecture_context: str = "") -> str:
    if not DEEPSEEK_API_KEY:
        return "[Error: DeepSeek API key missing]"
    
    system_prompt = """
You are an expert assistant for T DESSERT International Pastry Academy and a sourdough baking class.
You have knowledge about:
- The school: founded in 2013 in Beijing and Xiamen, international staff, published in "so good..." magazine.
- Instructor Carbon Zhao: degree in Bioengineering specializing in marine yeast, worked in high-end Beijing restaurants.
- Sourdough and Ciabatta recipes (detailed ingredients and methods).
- Levain (starter) preparation: using flour, water, ratio 1:1:1, fermentation at 25-30°C, lactic acid bacteria, etc.
Answer questions clearly, accurately, and in the same language as the question. If the question is in English, answer in English. If in Chinese, answer in Chinese. If in Arabic, answer in Arabic. If in Russian, answer in Russian.
If the user provides a context from the current lecture, use it to give more precise answers.
"""
    user_content = question
    if lecture_context:
        user_content = f"Context from the current lecture (what the teacher has said so far, in English):\n{lecture_context}\n\nNow answer the following question, using this context if relevant:\n{question}"
    
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {DEEPSEEK_API_KEY}"
    }
    payload = {
        "model": "deepseek-chat",
        "messages": [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_content}
        ],
        "max_tokens": 1024,
        "temperature": 0.7
    }
    try:
        resp = requests.post(DEEPSEEK_URL, json=payload, headers=headers, timeout=15)
        resp.raise_for_status()
        return resp.json()["choices"][0]["message"]["content"].strip()
    except Exception as e:
        logging.error(f"DeepSeek error: {e}")
        return f"Sorry, an error occurred: {str(e)}"

# ================= WebSocket для Xunfei =================
connected_clients = set()

async def broadcast_to_clients(message):
    if connected_clients:
        for client in list(connected_clients):
            try:
                await client.send_str(message)
            except:
                connected_clients.discard(client)

async def delayed_translate(text, source, target):
    if text.strip() == "":
        return
    translated = translate_with_glossary(text, source, target)
    lecture_transcript.append(translated)
    await broadcast_to_clients(json.dumps({
        'type': 'teacher_translation',
        'translation': translated,
        'original': text
    }))

async def xunfei_client():
    global is_running, pending_text, pending_task, is_guest_mode
    while is_running:
        try:
            now = datetime.now()
            date = format_date_time(mktime(now.timetuple()))
            host = "ist-api-sg.xf-yun.com"
            path = "/v2/ist"
            signature_origin = f"host: {host}\ndate: {date}\nGET {path} HTTP/1.1"
            signature_hmac = hmac.new(
                APISecret.encode('utf-8'),
                signature_origin.encode('utf-8'),
                hashlib.sha256
            ).digest()
            signature_sha = base64.b64encode(signature_hmac).decode('utf-8')
            authorization_origin = f'api_key="{APIKey}", algorithm="hmac-sha256", headers="host date request-line", signature="{signature_sha}"'
            authorization = base64.b64encode(authorization_origin.encode('utf-8')).decode('utf-8')
            url_params = {"host": host, "date": date, "authorization": authorization}
            query_string = urllib.parse.urlencode(url_params)
            ws_url = f"ws://{host}{path}?{query_string}"

            async with websockets.connect(ws_url) as ws:
                init_msg = {
                    "common": {"app_id": APPID},
                    "business": {"language": "zh_cn", "domain": "ist_ed", "accent": "mandarin", "punc": 1, "nunum": 1},
                    "data": {"status": 0, "format": "audio/L16;rate=16000", "encoding": "raw", "audio": ""}
                }
                await ws.send(json.dumps(init_msg))
                logging.info("Xunfei WS connected (streaming mode)")

                async def recv_task():
                    global pending_text, pending_task
                    async for message in ws:
                        data = json.loads(message)
                        if data.get('code') == 0:
                            res = data.get('data', {}).get('result', {})
                            if res and 'ws' in res:
                                raw_text = ''.join(cw.get('w', '') for ws_item in res['ws'] for cw in ws_item.get('cw', []))
                                if raw_text:
                                    corrected = correct_glossary(raw_text)
                                    await broadcast_to_clients(json.dumps({'type': 'teacher_speech', 'text': corrected, 'is_final': False}))
                                    if pending_task:
                                        pending_task.cancel()
                                    pending_text = corrected
                                    pending_task = asyncio.create_task(asyncio.sleep(DEBOUNCE_SEC))
                                    asyncio.create_task(wait_and_translate(pending_task, pending_text, 'zh', 'en'))
                        elif data.get('code') != 0:
                            logging.error(f"Xunfei error: {data}")

                async def wait_and_translate(task, text, src, tgt):
                    try:
                        await task
                        await delayed_translate(text, src, tgt)
                    except asyncio.CancelledError:
                        pass

                recv = asyncio.create_task(recv_task())

                while is_running:
                    try:
                        chunk = await asyncio.wait_for(audio_queue.get(), timeout=0.05)
                        pcm = (chunk * 32767).astype(np.int16).tobytes()
                        audio_msg = {
                            "data": {
                                "status": 1,
                                "format": "audio/L16;rate=16000",
                                "encoding": "raw",
                                "audio": base64.b64encode(pcm).decode()
                            }
                        }
                        await ws.send(json.dumps(audio_msg))
                    except asyncio.TimeoutError:
                        continue
                    except Exception as e:
                        logging.error(f"Audio send error: {e}")
                        break

                recv.cancel()
                await ws.close()

        except Exception as e:
            logging.error(f"Xunfei connection error: {e}")
            await asyncio.sleep(2)

# ================= WebSocket для перевода (аудио) =================
async def websocket_handler(request):
    ws = web.WebSocketResponse()
    await ws.prepare(request)
    connected_clients.add(ws)
    logging.info(f"Client connected. Total: {len(connected_clients)}")
    try:
        async for msg in ws:
            if msg.type == web.WSMsgType.TEXT:
                data = json.loads(msg.data)
                if data.get('type') == 'audio_chunk':
                    int16_data = np.array(data['data'], dtype=np.int16)
                    float32_data = int16_data.astype(np.float32) / 32768.0
                    await audio_queue.put(float32_data)
                elif data.get('type') == 'guest_question':
                    english_text = data.get('text', '')
                    if english_text:
                        chinese = translate_with_glossary(english_text, 'en', 'zh')
                        pinyin = get_pinyin(chinese)
                        await ws.send_json({
                            'type': 'guest_translation',
                            'chinese': chinese,
                            'pinyin': pinyin,
                            'original': english_text
                        })
                elif data.get('type') == 'set_guest_mode':
                    global is_guest_mode
                    is_guest_mode = data.get('active', False)
                    logging.info(f"Guest mode set to {is_guest_mode}")
    except Exception as e:
        logging.error(f"WebSocket error: {e}")
    finally:
        connected_clients.discard(ws)
        logging.info(f"Client disconnected. Total: {len(connected_clients)}")
    return ws

# ================= WebSocket для чата =================
def get_lecture_context(max_chars=3000):
    if not lecture_transcript:
        return ""
    full_text = " ".join(lecture_transcript)
    if len(full_text) <= max_chars:
        return full_text
    return full_text[-max_chars:]

async def chat_websocket_handler(request):
    ws = web.WebSocketResponse()
    await ws.prepare(request)
    is_admin = request.query.get('admin', '').lower() == 'true'
    if is_admin:
        admin_connections.add(ws)
        logging.info(f"Admin connected. Total admins: {len(admin_connections)}")
    else:
        chat_connections.add(ws)
        logging.info(f"Chat user connected. Total users: {len(chat_connections)}")
    try:
        async for msg in ws:
            if msg.type == web.WSMsgType.TEXT:
                data = json.loads(msg.data)
                if data.get('type') == 'chat_question':
                    question = data.get('text', '')
                    lang = data.get('lang', 'en')
                    if question:
                        ctx = get_lecture_context(3000)
                        answer = await deepseek_answer(question, lang, ctx)
                        await ws.send_json({
                            'type': 'chat_answer',
                            'question': question,
                            'answer': answer,
                            'lang': lang
                        })
                        if not is_admin:
                            src_lang_q = detect_language(question)
                            src_lang_a = detect_language(answer)
                            if src_lang_q == 'zh':
                                chinese_q = question
                            else:
                                chinese_q = translate_with_glossary(question, src_lang_q, 'zh')
                            if src_lang_a == 'zh':
                                chinese_a = answer
                            else:
                                chinese_a = translate_with_glossary(answer, src_lang_a, 'zh')
                            pinyin_q = get_pinyin(chinese_q)
                            pinyin_a = get_pinyin(chinese_a)
                            admin_msg = {
                                'type': 'admin_chat_message',
                                'original_question': question,
                                'original_answer': answer,
                                'chinese_question': chinese_q,
                                'chinese_answer': chinese_a,
                                'pinyin_question': pinyin_q,
                                'pinyin_answer': pinyin_a,
                                'timestamp': datetime.now().strftime("%H:%M:%S")
                            }
                            for admin in admin_connections:
                                try:
                                    await admin.send_json(admin_msg)
                                except:
                                    admin_connections.discard(admin)
    except Exception as e:
        logging.error(f"Chat WebSocket error: {e}")
    finally:
        if is_admin:
            admin_connections.discard(ws)
        else:
            chat_connections.discard(ws)
    return ws

# ================= HTTP маршруты =================

async def handle_index(request):
    html = '''<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0, user-scalable=yes">
    <title>T DESSERT Live Translation + AI Chat</title>
    <style>
        * { box-sizing: border-box; margin: 0; padding: 0; }
        body {
            font-family: system-ui, -apple-system, 'Segoe UI', Roboto, Helvetica, Arial, sans-serif;
            background: #f7f7f7;
            padding: 1rem;
        }
        .container {
            max-width: 700px;
            margin: 0 auto;
            background: white;
            border-radius: 32px;
            box-shadow: 0 10px 35px rgba(0,0,0,0.05), 0 2px 5px rgba(0,0,0,0.02);
            overflow: hidden;
            padding: 1.5rem;
        }
        h1 {
            font-size: 1.8rem;
            font-weight: 600;
            letter-spacing: -0.01em;
            text-align: center;
            margin-bottom: 1.2rem;
            color: #1a1a1a;
        }
        .status {
            background: #f0f0f0;
            border-radius: 60px;
            padding: 0.65rem 1rem;
            text-align: center;
            font-weight: 500;
            font-size: 0.9rem;
            margin-bottom: 1.5rem;
            color: #2c2c2c;
        }
        .card {
            background: #fafafa;
            border-radius: 24px;
            padding: 1.2rem;
            margin-bottom: 1.5rem;
            border: 1px solid #eee;
        }
        .card h3 {
            font-size: 1.2rem;
            font-weight: 600;
            margin-bottom: 0.75rem;
            display: flex;
            align-items: center;
            gap: 0.5rem;
        }
        .teacher-phrase p, .translation p {
            background: white;
            padding: 0.8rem;
            border-radius: 20px;
            margin-top: 0.5rem;
            word-break: break-word;
            border: 1px solid #eaeaea;
        }
        .guest-area button, .download-btn {
            background: #000;
            color: white;
            border: none;
            padding: 0.8rem;
            width: 100%;
            border-radius: 60px;
            font-weight: 600;
            font-size: 1rem;
            cursor: pointer;
            transition: 0.2s;
            margin-top: 0.5rem;
        }
        .guest-area button:active, .download-btn:active { transform: scale(0.97); }
        .chat-container {
            margin-top: 0.5rem;
        }
        .chat-messages {
            max-height: 280px;
            overflow-y: auto;
            background: #f5f5f5;
            border-radius: 24px;
            padding: 0.8rem;
            margin-bottom: 0.8rem;
        }
        .chat-message {
            background: white;
            border-radius: 20px;
            padding: 0.8rem;
            margin-bottom: 0.8rem;
            border-left: 5px solid #000;
        }
        .chat-question { font-weight: 700; color: #000; margin-bottom: 0.3rem; }
        .chat-answer { color: #3a3a3a; }
        .chat-input {
            display: flex;
            gap: 0.5rem;
            flex-wrap: wrap;
        }
        .chat-input input {
            flex: 1;
            min-width: 150px;
            padding: 0.8rem;
            border-radius: 60px;
            border: 1px solid #ccc;
            font-size: 0.95rem;
        }
        .chat-input button {
            background: #000;
            color: white;
            border: none;
            padding: 0.8rem 1.2rem;
            border-radius: 60px;
            font-weight: 600;
            cursor: pointer;
            white-space: nowrap;
        }
        .history-list {
            max-height: 320px;
            overflow-y: auto;
            background: #f5f5f5;
            border-radius: 20px;
            padding: 0.8rem;
        }
        .history-item {
            background: white;
            padding: 0.8rem;
            border-radius: 16px;
            margin-bottom: 0.6rem;
            border-left: 3px solid #aaa;
        }
        .note {
            font-size: 0.75rem;
            text-align: center;
            color: #6c6c6c;
            margin-top: 1.5rem;
        }
        a.school-link {
            display: inline-block;
            text-align: center;
            margin-top: 1rem;
            color: #2c2c2c;
            font-weight: 500;
        }
        @media (max-width: 550px) {
            body { padding: 0.8rem; }
            .container { padding: 1rem; }
            h1 { font-size: 1.5rem; }
            .chat-input button { padding: 0.8rem 1rem; }
        }
    </style>
</head>
<body>
<div class="container">
    <h1>🎧 T DESSERT <span style="font-weight:400;">Live Translation</span></h1>
    <div class="status" id="status">🔌 Connecting...</div>
    <div class="card">
        <h3>👨‍🍳 Teacher (Chinese)</h3>
        <p id="teacherText">—</p>
    </div>
    <div class="card">
        <h3>🎤 Translation (English)</h3>
        <p id="translationText">—</p>
        <small style="color:#666;">🔊 Plays in earphone → repeat to guests</small>
    </div>
    <div class="card guest-area">
        <h3>🗣 Guest Question (English → Chinese)</h3>
        <button id="guestBtn">🎤 Translate guest question</button>
        <div id="guestResult" style="display:none; background:white; margin-top:0.8rem; padding:0.8rem; border-radius:20px;">
            <div><strong>English:</strong> <span id="guestEn"></span></div>
            <div><strong>Chinese:</strong> <span id="guestZh"></span></div>
            <div><strong>Pinyin:</strong> <span id="guestPy"></span></div>
        </div>
    </div>
    <div class="chat-container">
        <h3 style="font-size:1.2rem; margin-bottom:0.5rem;">💬 AI Assistant (DeepSeek)</h3>
        <div class="chat-messages" id="chatMessages"></div>
        <div class="chat-input">
            <input type="text" id="chatInput" placeholder="Ask in any language...">
            <button id="chatSend">Send</button>
        </div>
        <small style="display:block; margin-top:0.3rem;">Knows school, recipes, levain + current lecture context</small>
    </div>
    <div>
        <h3 style="font-size:1.2rem;">📜 Lecture history</h3>
        <button id="downloadBtn" class="download-btn" style="background:#2c2c2c;">⬇ Download lecture (English)</button>
        <div class="history-list" id="historyList"></div>
    </div>
    <div class="note">
        📌 Phone near teacher. 🎧 Headphones for translation. <br>
        ✨ <a href="/school" class="school-link" style="color:#000;">About T DESSERT Academy →</a>
    </div>
</div>
<script>
    let ws = null, chatWs = null, audioContext = null, mediaStream = null, processorNode = null;
    let guestModeActive = false;
    let historyItems = [];

    const statusDiv = document.getElementById('status');
    const teacherTextSpan = document.getElementById('teacherText');
    const translationSpan = document.getElementById('translationText');
    const guestBtn = document.getElementById('guestBtn');
    const guestResultDiv = document.getElementById('guestResult');
    const guestEnSpan = document.getElementById('guestEn');
    const guestZhSpan = document.getElementById('guestZh');
    const guestPySpan = document.getElementById('guestPy');
    const historyListDiv = document.getElementById('historyList');
    const chatMessagesDiv = document.getElementById('chatMessages');
    const chatInput = document.getElementById('chatInput');
    const chatSend = document.getElementById('chatSend');
    const downloadBtn = document.getElementById('downloadBtn');

    // Определяем протокол WebSocket: wss для HTTPS, ws для HTTP
    const wsProtocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';

    function addToHistory(direction, source, target) {
        historyItems.unshift({ timestamp: new Date().toLocaleTimeString(), direction, source, target });
        let html = '';
        for (let i=0; i<historyItems.length; i++) {
            const h = historyItems[i];
            html += `<div class="history-item"><div>[${h.timestamp}] ${h.direction}</div><div>📝 ${h.source}</div><div>✅ ${h.target}</div></div>`;
        }
        historyListDiv.innerHTML = html;
        historyListDiv.scrollTop = 0;
    }
    function addChatMessage(question, answer) {
        const div = document.createElement('div');
        div.className = 'chat-message';
        div.innerHTML = `<div class="chat-question">❓ ${question}</div><div class="chat-answer">🤖 ${answer}</div>`;
        chatMessagesDiv.appendChild(div);
        chatMessagesDiv.scrollTop = chatMessagesDiv.scrollHeight;
    }
    function initChatWebSocket() {
        chatWs = new WebSocket(`${wsProtocol}//${window.location.host}/ws_chat`);
        chatWs.onmessage = (e) => {
            const data = JSON.parse(e.data);
            if (data.type === 'chat_answer') addChatMessage(data.question, data.answer);
        };
        chatWs.onclose = () => setTimeout(initChatWebSocket, 3000);
    }
    chatSend.onclick = () => {
        const text = chatInput.value.trim();
        if (!text || !chatWs || chatWs.readyState !== WebSocket.OPEN) return;
        const containsChinese = /[\\u4e00-\\u9fff]/.test(text);
        chatWs.send(JSON.stringify({ type: 'chat_question', text, lang: containsChinese ? 'zh' : 'en' }));
        chatInput.value = '';
    };
    chatInput.onkeypress = (e) => { if (e.key === 'Enter') chatSend.click(); };
    downloadBtn.onclick = () => window.location.href = '/download_lecture';

    function connectWebSocket() {
        ws = new WebSocket(`${wsProtocol}//${window.location.host}/ws`);
        ws.onopen = () => { statusDiv.innerText = '✅ Connected. Starting mic...'; startMicrophone(); };
        ws.onmessage = (e) => {
            const data = JSON.parse(e.data);
            if (data.type === 'teacher_speech') teacherTextSpan.innerText = data.text;
            else if (data.type === 'teacher_translation') {
                translationSpan.innerText = data.translation;
                const utterance = new SpeechSynthesisUtterance(data.translation);
                utterance.lang = 'en-US';
                window.speechSynthesis.cancel();
                window.speechSynthesis.speak(utterance);
                addToHistory('👨‍🍳 Chinese → English', data.original, data.translation);
            } else if (data.type === 'guest_translation') {
                guestZhSpan.innerText = data.chinese;
                guestPySpan.innerText = data.pinyin;
                guestResultDiv.style.display = 'block';
                setTimeout(() => guestResultDiv.style.display = 'none', 5000);
            }
        };
        ws.onclose = () => statusDiv.innerText = '❌ Disconnected. Reload.';
    }
    async function startMicrophone() {
        try {
            const stream = await navigator.mediaDevices.getUserMedia({ audio: true });
            mediaStream = stream;
            audioContext = new AudioContext({ sampleRate: 16000 });
            const source = audioContext.createMediaStreamSource(stream);
            processorNode = audioContext.createScriptProcessor(2048, 1, 1);
            source.connect(processorNode);
            processorNode.connect(audioContext.destination);
            processorNode.onaudioprocess = (event) => {
                if (guestModeActive) return;
                if (ws && ws.readyState === WebSocket.OPEN) {
                    const inputData = event.inputBuffer.getChannelData(0);
                    const pcm16 = new Int16Array(inputData.length);
                    for (let i=0; i<inputData.length; i++) {
                        let s = Math.max(-1, Math.min(1, inputData[i]));
                        pcm16[i] = s < 0 ? s * 0x8000 : s * 0x7FFF;
                    }
                    ws.send(JSON.stringify({ type: 'audio_chunk', data: Array.from(pcm16) }));
                }
            };
            await audioContext.resume();
            statusDiv.innerText = '🎙️ Listening to teacher...';
        } catch(err) { statusDiv.innerText = '❌ Microphone access denied'; }
    }
    guestBtn.onclick = () => {
        if (!('webkitSpeechRecognition' in window)) { alert('Speech recognition not supported'); return; }
        guestModeActive = true;
        const recognition = new (window.SpeechRecognition || window.webkitSpeechRecognition)();
        recognition.lang = 'en-US';
        guestBtn.disabled = true;
        guestBtn.innerText = '🎙️ Listening to guest...';
        statusDiv.innerText = '🎤 Recording guest question...';
        recognition.start();
        recognition.onresult = (event) => {
            const text = event.results[0][0].transcript;
            guestEnSpan.innerText = text;
            guestResultDiv.style.display = 'block';
            if (ws && ws.readyState === WebSocket.OPEN) {
                ws.send(JSON.stringify({ type: 'guest_question', text }));
            }
        };
        recognition.onerror = (e) => {
            statusDiv.innerText = '⚠️ Recognition error';
            guestModeActive = false;
            guestBtn.disabled = false;
            guestBtn.innerText = '🎤 Translate guest question';
            statusDiv.innerText = '🎙️ Listening to teacher...';
        };
        recognition.onend = () => {
            guestModeActive = false;
            guestBtn.disabled = false;
            guestBtn.innerText = '🎤 Translate guest question';
            statusDiv.innerText = '🎙️ Listening to teacher...';
            if (guestEnSpan.innerText === '') setTimeout(() => guestResultDiv.style.display = 'none', 1000);
        };
    };
    window.onbeforeunload = () => {
        if (mediaStream) mediaStream.getTracks().forEach(t=>t.stop());
        if (audioContext) audioContext.close();
        if (ws) ws.close();
        if (chatWs) chatWs.close();
    };
    connectWebSocket();
    initChatWebSocket();
</script>
</body>
</html>'''
    return web.Response(text=html, content_type='text/html')

async def handle_admin(request):
    html = '''<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0, user-scalable=yes">
    <title>Admin Panel - T DESSERT Chat</title>
    <style>
        * { margin:0; padding:0; box-sizing: border-box; }
        body {
            background: #0a0a0a;
            font-family: 'SF Mono', 'Menlo', monospace;
            padding: 1.2rem;
        }
        .container {
            max-width: 1100px;
            margin: 0 auto;
        }
        h1 {
            color: #f5a623;
            font-size: 1.8rem;
            margin-bottom: 1rem;
            border-left: 4px solid #f5a623;
            padding-left: 1rem;
        }
        .admin-question {
            display: flex;
            gap: 0.8rem;
            margin-bottom: 2rem;
            flex-wrap: wrap;
        }
        .admin-question input {
            flex: 1;
            padding: 0.8rem;
            background: #1e1e1e;
            border: 1px solid #3a3a3a;
            border-radius: 40px;
            color: #eee;
            font-family: inherit;
            font-size: 0.9rem;
        }
        .admin-question button {
            background: #f5a623;
            border: none;
            padding: 0 1.4rem;
            border-radius: 40px;
            font-weight: bold;
            font-family: inherit;
            cursor: pointer;
        }
        .message {
            background: #1a1a1a;
            border-left: 4px solid #f5a623;
            margin-bottom: 1rem;
            padding: 1rem;
            border-radius: 16px;
        }
        .timestamp {
            color: #888;
            font-size: 0.7rem;
            margin-bottom: 0.5rem;
        }
        .original { color: #b5ffb5; }
        .chinese { color: #ffd8a8; }
        .pinyin { color: #a0c0ff; }
        hr { border-color: #2a2a2a; margin: 0.5rem 0; }
        @media (max-width: 650px) {
            body { padding: 0.8rem; }
            .admin-question input { min-width: 160px; }
        }
    </style>
</head>
<body>
<div class="container">
    <h1>🔐 Admin Panel – All messages + Chinese translation & Pinyin</h1>
    <div class="admin-question">
        <input type="text" id="adminQuestion" placeholder="Ask as admin (any language)...">
        <button id="adminSend">Send →</button>
    </div>
    <div id="messages"></div>
</div>
<script>
    const wsProtocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
    const ws = new WebSocket(`${wsProtocol}//${window.location.host}/ws_chat?admin=true`);
    const messagesDiv = document.getElementById('messages');
    const adminQuestion = document.getElementById('adminQuestion');
    const adminSend = document.getElementById('adminSend');

    function escapeHtml(str) {
        if (!str) return '';
        return str.replace(/[&<>]/g, function(m) {
            if (m === '&') return '&amp;';
            if (m === '<') return '&lt;';
            if (m === '>') return '&gt;';
            return m;
        });
    }
    ws.onmessage = (event) => {
        const data = JSON.parse(event.data);
        if (data.type === 'admin_chat_message') {
            const div = document.createElement('div');
            div.className = 'message';
            div.innerHTML = `
                <div class="timestamp">${data.timestamp}</div>
                <div><strong>❓ Original:</strong> <span class="original">${escapeHtml(data.original_question)}</span></div>
                <div><strong>🤖 Original answer:</strong> <span class="original">${escapeHtml(data.original_answer)}</span></div>
                <div><strong>🇨🇳 Chinese Q:</strong> <span class="chinese">${escapeHtml(data.chinese_question)}</span></div>
                <div><strong>🔊 Pinyin Q:</strong> <span class="pinyin">${escapeHtml(data.pinyin_question)}</span></div>
                <div><strong>🇨🇳 Chinese A:</strong> <span class="chinese">${escapeHtml(data.chinese_answer)}</span></div>
                <div><strong>🔊 Pinyin A:</strong> <span class="pinyin">${escapeHtml(data.pinyin_answer)}</span></div>
                <hr>
            `;
            messagesDiv.prepend(div);
        }
    };
    adminSend.addEventListener('click', () => {
        const text = adminQuestion.value.trim();
        if (!text || ws.readyState !== WebSocket.OPEN) return;
        const containsChinese = /[\\u4e00-\\u9fff]/.test(text);
        const lang = containsChinese ? 'zh' : 'en';
        ws.send(JSON.stringify({ type: 'chat_question', text: text, lang: lang }));
        adminQuestion.value = '';
    });
    ws.onclose = () => setTimeout(() => location.reload(), 3000);
</script>
</body>
</html>'''
    return web.Response(text=html, content_type='text/html')

# ================= Чёрно-белая страница школы =================
async def handle_school(request):
    html = '''<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0, user-scalable=yes">
    <title>T DESSERT Academy | Black & White</title>
    <style>
        * { margin:0; padding:0; box-sizing: border-box; }
        body {
            background: #ffffff;
            font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Helvetica, sans-serif;
            line-height: 1.5;
            color: #111;
        }
        .container {
            max-width: 1000px;
            margin: 0 auto;
            padding: 2rem 1.5rem;
        }
        h1, h2, h3 {
            font-weight: 500;
            letter-spacing: -0.02em;
        }
        h1 {
            font-size: 3rem;
            font-weight: 600;
            margin-bottom: 0.25rem;
            letter-spacing: -0.03em;
        }
        .subhead {
            font-size: 1.1rem;
            color: #3a3a3a;
            border-bottom: 1px solid #ccc;
            padding-bottom: 1rem;
            margin-bottom: 2rem;
        }
        h2 {
            font-size: 1.8rem;
            margin-top: 2rem;
            margin-bottom: 1rem;
            border-left: 4px solid #000;
            padding-left: 1rem;
        }
        h3 {
            font-size: 1.3rem;
            margin: 1.2rem 0 0.6rem;
            font-weight: 500;
        }
        .badge {
            display: inline-block;
            background: #111;
            color: white;
            font-size: 0.7rem;
            padding: 0.2rem 0.6rem;
            border-radius: 30px;
            letter-spacing: 0.5px;
            margin-right: 0.5rem;
        }
        .grid-2 {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 2rem;
            margin: 1.5rem 0;
        }
        .card {
            background: #fafafa;
            padding: 1.2rem;
            border-radius: 24px;
            border: 1px solid #eaeaea;
        }
        .recipe-table {
            width: 100%;
            border-collapse: collapse;
            font-size: 0.85rem;
            margin: 1rem 0;
        }
        .recipe-table td, .recipe-table th {
            border-bottom: 1px solid #ddd;
            padding: 0.5rem;
            text-align: left;
        }
        .recipe-table th {
            font-weight: 600;
        }
        ul, .rule-list {
            list-style: none;
            padding-left: 0;
        }
        li {
            margin-bottom: 0.5rem;
            padding-left: 1.2rem;
            position: relative;
        }
        li::before {
            content: "—";
            position: absolute;
            left: 0;
            color: #888;
        }
        hr {
            margin: 2rem 0;
            border: none;
            border-top: 1px solid #ddd;
        }
        .footer-links {
            margin-top: 3rem;
            text-align: center;
            font-size: 0.9rem;
            border-top: 1px solid #eee;
            padding-top: 1.5rem;
        }
        .footer-links a {
            color: #000;
            text-decoration: none;
            margin: 0 1rem;
            font-weight: 500;
        }
        .footer-links a:hover {
            text-decoration: underline;
        }
        @media (max-width: 700px) {
            .container { padding: 1.2rem; }
            h1 { font-size: 2.2rem; }
            h2 { font-size: 1.5rem; }
            .grid-2 { grid-template-columns: 1fr; gap: 1rem; }
        }
        @media (prefers-color-scheme: dark) {
            body { background: #000; color: #eee; }
            .card { background: #111; border-color: #2a2a2a; }
            .subhead { border-bottom-color: #2a2a2a; color: #aaa; }
            .recipe-table td, .recipe-table th { border-bottom-color: #2a2a2a; }
            hr { border-top-color: #2a2a2a; }
            .footer-links a { color: #ddd; }
        }
    </style>
</head>
<body>
<div class="container">
    <h1>T DESSERT</h1>
    <div class="subhead">International Pastry Academy · since 2013 · Beijing & Xiamen</div>
    
    <p><strong>China's first international baking institution</strong> integrating professional baking with aesthetic art, staffed entirely by foreign professional chefs. Published in <em>so good...</em> magazine — the first Chinese school ever featured.</p>
    
    <h2>📍 Courses & Instructors</h2>
    <div class="card">
        <h3>#024 × T DESSERT — Sourdough & Ciabatta Baking Class</h3>
        <p><span class="badge">Instructor</span> <strong>Carbon Zhao</strong> — Bread Lecturer, TIPA</p>
        <ul>
            <li>Degree in Bioengineering, specialization in marine yeast</li>
            <li>Previously worked at multiple high-end Beijing restaurants</li>
            <li>Specializes in Japanese-style bread, bagels, brioche, rustic sourdough</li>
            <li>“Bread as a refined microbial experiment”</li>
        </ul>
    </div>

    <h2>📖 Key Recipes</h2>
    <div class="grid-2">
        <div class="card">
            <h3>🍞 Ciabatta</h3>
            <table class="recipe-table">
                <tr><th>Ingredient</th><th>Amount</th></tr>
                <tr><td>T65 flour</td><td>450g</td></tr>
                <tr><td>Bread Flour</td><td>150g</td></tr>
                <tr><td>Levain</td><td>300g</td></tr>
                <tr><td>Malt extract</td><td>8g</td></tr>
                <tr><td>Water 1</td><td>300g</td></tr>
                <tr><td>Water roux</td><td>150g</td></tr>
                <tr><td>Poolish</td><td>1800g</td></tr>
                <tr><td>Salt</td><td>28g</td></tr>
                <tr><td>Water 2</td><td>120g</td></tr>
                <tr><td>Olive oil</td><td>100g</td></tr>
            </table>
            <p><em>Method: mix, hydrolyze 30min, add levain & salt, mix until smooth, add oil. Dough temp 23–24°C. Bake 250/240°C, 23min.</em></p>
        </div>
        <div class="card">
            <h3>🍞 Sourdough Bread</h3>
            <table class="recipe-table">
                <tr><th>Ingredient</th><th>Amount</th></tr>
                <tr><td>T65 flour</td><td>800g</td></tr>
                <tr><td>T170 flour</td><td>200g</td></tr>
                <tr><td>Water 1</td><td>680g</td></tr>
                <tr><td>Maltodextrin</td><td>6g</td></tr>
                <tr><td>Fresh yeast</td><td>5g</td></tr>
                <tr><td>Levain</td><td>300g</td></tr>
                <tr><td>Salt</td><td>18g</td></tr>
                <tr><td>Water 2</td><td>40g</td></tr>
                <tr><td>Walnut</td><td>180g</td></tr>
                <tr><td>Marinated cherries</td><td>300g</td></tr>
                <tr><td>Chocolate chips</td><td>180g</td></tr>
            </table>
            <p><em>Hydrolysis 50min, mix with levain & yeast, add salt, slow water, ferment 90min + cold overnight. Bake 260/230°C with steam.</em></p>
        </div>
    </div>

    <h2>⚙️ Classroom Rules (short)</h2>
    <div class="card">
        <ul>
            <li>Arrive 10 min early, strict hygiene (hand washing, hair tied)</li>
            <li>No slippers, non-slip shoes required</li>
            <li>Work surfaces cleaned after use, silent mobile phones</li>
            <li>No children or non‑class personnel allowed</li>
        </ul>
    </div>

    <h2>🏆 Honors & Partners</h2>
    <div class="grid-2">
        <div class="card">
            <h3>Accolades</h3>
            <ul>
                <li>First Chinese school in <em>so good...</em> magazine (2017, featured 3 years)</li>
                <li>Member of ITCL International Pastry Chefs Alliance</li>
                <li>Official academy for world-top pastry masters in China</li>
            </ul>
        </div>
        <div class="card">
            <h3>Brand partners</h3>
            <ul>
                <li>Valrhona · UNOX · Tbest · Sosa · Rémy Cointreau · AKOKO</li>
                <li>Collaboration with <strong>#024 Sanlitun</strong> — “24‑hour living” concept</li>
            </ul>
        </div>
    </div>

    <div class="footer-links">
        <a href="/">← Back to Live Translation</a> | <a href="/admin">Admin Panel</a>
    </div>
</div>
</body>
</html>'''
    return web.Response(text=html, content_type='text/html')

async def download_lecture(request):
    content = "\n\n".join(lecture_transcript) if lecture_transcript else "Lecture not started yet."
    return web.Response(text=content, headers={
        'Content-Disposition': 'attachment; filename="lecture_english.txt"',
        'Content-Type': 'text/plain; charset=utf-8'
    })

async def start_http_server():
    app = web.Application()
    app.router.add_get('/', handle_index)
    app.router.add_get('/admin', handle_admin)
    app.router.add_get('/school', handle_school)
    app.router.add_get('/download_lecture', download_lecture)
    app.router.add_get('/ws', websocket_handler)
    app.router.add_get('/ws_chat', chat_websocket_handler)
    runner = web.AppRunner(app)
    await runner.setup()
    # Render устанавливает переменную окружения PORT, используем её
    port = int(os.environ.get("PORT", 8000))
    site = web.TCPSite(runner, '0.0.0.0', port)
    await site.start()
    logging.info(f"HTTP + WebSocket server running on port {port}")
    logging.info(f"Admin panel: http://localhost:{port}/admin")
    logging.info(f"School page: http://localhost:{port}/school")

async def main():
    asyncio.create_task(xunfei_client())
    await start_http_server()
    await asyncio.Future()

if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    if not APPID or not APIKey or not APISecret:
        logging.warning("Xunfei credentials missing. Get them from console.xfyun.cn")
    if not DEEPSEEK_API_KEY:
        logging.warning("DEEPSEEK_API_KEY not set! AI assistant will not work.")
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        logging.info("Shutdown")