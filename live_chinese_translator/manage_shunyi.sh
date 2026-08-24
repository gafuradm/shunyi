#!/bin/bash
# Управление сервисами Shunyi (автозапуск через launchd)
# Использование: ./manage_shunyi.sh {start|stop|restart|status}
PLIST_DIR="$HOME/Library/LaunchAgents"
SERVICES=(server ngrok caffeinate)
GUI="gui/$(id -u)"

cmd="${1:-status}"

case "$cmd" in
  start)
    for s in "${SERVICES[@]}"; do
      launchctl bootstrap "$GUI" "$PLIST_DIR/com.shunyi.$s.plist" 2>/dev/null || true
      launchctl kickstart -k "$GUI/com.shunyi.$s" 2>/dev/null || true
    done
    echo "Сервисы запущены."
    "$0" status
    ;;
  stop)
    for s in "${SERVICES[@]}"; do
      launchctl bootout "$GUI" "$PLIST_DIR/com.shunyi.$s.plist" 2>/dev/null || true
    done
    echo "Сервисы остановлены (сайт недоступен до следующего start или перезагрузки)."
    ;;
  restart)
    "$0" stop
    sleep 2
    "$0" start
    ;;
  status)
    echo "--- Сервер (порт 8000) ---"
    pid=$(lsof -ti :8000)
    if [ -n "$pid" ]; then echo "работает (pid $pid)"; else echo "СЕРВЕР НЕ РАБОТАЕТ"; fi
    echo "--- ngrok ---"
    pgrep -fl "ngrok http" || echo "ngrok не запущен"
    echo "--- caffeinate ---"
    pgrep -fl "caffeinate -dims" || echo "caffeinate не запущен"
    echo "--- Публичный адрес ---"
    echo "https://lucas-uncadenced-dustin.ngrok-free.dev"
    ;;
  *)
    echo "Использование: $0 {start|stop|restart|status}"
    ;;
esac
