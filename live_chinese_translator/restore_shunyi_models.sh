#!/bin/bash
# ============================================================
# Восстановление моделей проекта shunyi (~/Downloads/shunyi)
# Скачивает vosk/piper/punctuation/nllb модели заново.
# Источники: alphacephei.com (vosk), Hugging Face (nllb), GitHub (piper)
#
# v2: докачка (resume), проверка целостности zip, повторы при обрыве
# ============================================================
set -u

DEST="$HOME/Downloads/shunyi/models"
mkdir -p "$DEST"
cd "$DEST"

echo "=== Восстановление моделей в: $DEST ==="

# ---------- VOSK модели (основные) ----------
# (имя_папки|url|ожидаемый_zip_name)
VOSK_MODELS=(
  "vosk-ru|https://alphacephei.com/vosk/models/vosk-model-ru-0.42.zip|vosk-model-ru-0.42.zip"
  "vosk-zh|https://alphacephei.com/vosk/models/vosk-model-cn-0.22.zip|vosk-model-cn-0.22.zip"
  "vosk-ar|https://alphacephei.com/vosk/models/vosk-model-ar-0.22-linto-1.1.0.zip|vosk-model-ar-0.22-linto-1.1.0.zip"
  "vosk-uk|https://alphacephei.com/vosk/models/vosk-model-uk-v3.zip|vosk-model-uk-v3.zip"
  "vosk-ko|https://alphacephei.com/vosk/models/vosk-model-small-ko-0.22.zip|vosk-model-small-ko-0.22.zip"
  "vosk-fa|https://alphacephei.com/vosk/models/vosk-model-fa-0.5.zip|vosk-model-fa-0.5.zip"
  "vosk-pl|https://alphacephei.com/vosk/models/vosk-model-small-pl-0.22.zip|vosk-model-small-pl-0.22.zip"
  "vosk-de|https://alphacephei.com/vosk/models/vosk-model-de-0.21.zip|vosk-model-de-0.21.zip"
  "vosk-hi|https://alphacephei.com/vosk/models/vosk-model-hi-0.22.zip|vosk-model-hi-0.22.zip"
)

# скачивание с докачкой и повторами; без жёсткого таймаута
# (alfaphacephei отдаёт Content-Length, curl -C - докачивает с места обрыва)
fetch_resume() {
  local url="$1" out="$2" attempts="${3:-5}" retries=0
  while [ "$retries" -lt "$attempts" ]; do
    if curl -sL -C - --retry 3 --retry-delay 2 -o "$out" "$url"; then
      # curl успешен: проверяем, что файл не пуст
      [ -s "$out" ] && return 0 || { echo "    (пустой файл, повтор $((retries+1))/$attempts)"; rm -f "$out"; }
    else
      echo "    (обрыв, повтор $((retries+1))/$attempts)"
    fi
    retries=$((retries+1))
    sleep 3
  done
  return 1
}

download_vosk() {
  local name="$1" url="$2" zname="$3" tmp="/tmp/${zname}"
  if [ -d "$DEST/$name" ] && [ -s "$DEST/$name/am/final.mdl" ]; then
    echo "  [skip] $name уже есть"
    return
  fi
  if [ -d "$DEST/$name" ] && [ ! -s "$DEST/$name/am/final.mdl" ]; then
    echo "  [warn] $name есть, но битый — перекачаю"
    rm -rf "$DEST/$name"
  fi
  echo "  [down] $name"
  if fetch_resume "$url" "$tmp"; then
    # проверка целостности zip
    if unzip -tq "$tmp" >/dev/null 2>&1; then
      mkdir -p "$DEST/$name"
      unzip -q -o "$tmp" -d "$DEST/$name" 2>/dev/null
      # vosk-модели распаковываются во вложенную папку vosk-model-*; поднимаем содержимое на уровень выше
      local inner
      inner=$(find "$DEST/$name" -mindepth 1 -maxdepth 1 -type d | head -1)
      if [ -n "$inner" ] && [ "$(dirname "$inner")" = "$DEST/$name" ]; then
        mv "$inner"/* "$DEST/$name"/ 2>/dev/null
        rm -rf "$inner"
      fi
      rm -f "$tmp"
      echo "  [OK]   $name ($(du -sh "$DEST/$name" | cut -f1))"
    else
      echo "  [FAIL] $name — битый zip (не хватает данных)"
      rm -f "$tmp"
    fi
  else
    echo "  [FAIL] $name — не удалось скачать"
    rm -f "$tmp"
  fi
}

echo
echo "--- VOSK ---"
for entry in "${VOSK_MODELS[@]}"; do
  name="${entry%%|*}"
  rest="${entry#*|}"
  url="${rest%%|*}"
  zname="${rest#*|}"
  download_vosk "$name" "$url" "$zname"
done

# ---------- piper (TTS голоса) ----------
echo
echo "--- Piper TTS ---"
PIPER_FILES=(
  "https://huggingface.co/rhasspy/piper-voices/resolve/main/ru/ru_RU/irina/medium/ru_RU-irina-medium.onnx"
  "https://huggingface.co/rhasspy/piper-voices/resolve/main/ru/ru_RU/irina/medium/ru_RU-irina-medium.onnx.json"
  "https://huggingface.co/rhasspy/piper-voices/resolve/main/zh/zh_CN/huayan/medium/zh_CN-huayan-medium.onnx"
  "https://huggingface.co/rhasspy/piper-voices/resolve/main/zh/zh_CN/huayan/medium/zh_CN-huayan-medium.onnx.json"
)
mkdir -p "$DEST/piper"
for url in "${PIPER_FILES[@]}"; do
  fname=$(basename "$url")
  if [ ! -s "$DEST/piper/$fname" ]; then
    echo "  [down] piper/$fname"
    fetch_resume "$url" "$DEST/piper/$fname" && echo "  [OK]" || echo "  [FAIL] piper/$fname"
  else
    echo "  [skip] piper/$fname"
  fi
done

# ---------- punctuation ----------
echo
echo "--- Punctuation ---"
mkdir -p "$DEST/punctuation"
PUNCT_URLS=(
  "https://huggingface.co/rhasspy/piper-voices/resolve/main/en/en_US/lessac/medium/en_US-lessac-medium.onnx"
)
for u in "${PUNCT_URLS[@]}"; do
  fname=$(basename "$u")
  if [ ! -s "$DEST/punctuation/$fname" ]; then
    echo "  [down] punctuation/$fname"
    fetch_resume "$u" "$DEST/punctuation/$fname" && echo "  [OK]" || echo "  [FAIL] punctuation/$fname"
  else
    echo "  [skip] punctuation/$fname"
  fi
done

# ---------- NLLB-200 (перевод) ----------
echo
echo "--- NLLB-200 distilled 600M ---"
mkdir -p "$DEST/nllb-200-distilled-600M-int8"
NLLB_URLS=(
  "config.json|https://huggingface.co/facebook/nllb-200-distilled-600M/resolve/main/config.json"
  "sentencepiece.bpe.model|https://huggingface.co/facebook/nllb-200-distilled-600M/resolve/main/sentencepiece.bpe.model"
  "pytorch_model.bin|https://huggingface.co/facebook/nllb-200-distilled-600M/resolve/main/pytorch_model.bin"
  "tokenizer.json|https://huggingface.co/facebook/nllb-200-distilled-600M/resolve/main/tokenizer.json"
  "generation_config.json|https://huggingface.co/facebook/nllb-200-distilled-600M/resolve/main/generation_config.json"
)
for entry in "${NLLB_URLS[@]}"; do
  fname="${entry%%|*}"
  url="${entry#*|}"
  if [ ! -s "$DEST/nllb-200-distilled-600M-int8/$fname" ]; then
    echo "  [down] nllb/$fname"
    fetch_resume "$url" "$DEST/nllb-200-distilled-600M-int8/$fname" && echo "  [OK]" || echo "  [FAIL] nllb/$fname"
  else
    echo "  [skip] nllb/$fname"
  fi
done

echo
echo "=== ГОТОВО ==="
du -sh "$DEST"
echo "Расположение: $DEST"
