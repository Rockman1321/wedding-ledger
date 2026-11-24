#!/usr/bin/env bash
# Deploy the committed `main` branch (or the ref given as $1) to a server
# set up as in the README: files in /opt/wedding-hub owned by `weddinghub`,
# run by the `wedding-hub` systemd service. It asks for your sudo password
# on the server.
#
# Set the server in DEPLOY_HOST, or put it in a gitignored .deploy.local
# next to this script, e.g.:
#   DEPLOY_HOST=my-server        # an ssh host or ssh-config alias
# Optional overrides (defaults match the README and the example service):
#   DEPLOY_APP_DIR=/opt/wedding-hub  DEPLOY_USER=weddinghub
#   DEPLOY_SERVICE=wedding-hub       DEPLOY_PORT=8422
set -euo pipefail

cd "$(dirname "$0")"
[ -f .deploy.local ] && . ./.deploy.local

HOST="${DEPLOY_HOST:-}"
[ -n "$HOST" ] || { echo "Set DEPLOY_HOST (or put DEPLOY_HOST=... in .deploy.local)." >&2; exit 1; }
REF="${1:-main}"
APP_DIR="${DEPLOY_APP_DIR:-/opt/wedding-hub}"
APP_USER="${DEPLOY_USER:-weddinghub}"
SERVICE="${DEPLOY_SERVICE:-wedding-hub}"
PORT="${DEPLOY_PORT:-8422}"
FILES=(main.py static/index.html requirements.txt)

git rev-parse --verify --quiet "$REF" >/dev/null || { echo "No such ref: $REF" >&2; exit 1; }
REV=$(git rev-parse --short "$REF")
STAMP=$(date +%Y%m%d-%H%M%S)
STAGE="/tmp/wedding-ledger-deploy-$STAMP"

echo "==> Deploying $REF ($REV) to $HOST:$APP_DIR"

# Ship exactly what's committed (not the working tree).
git archive --format=tar "$REF" "${FILES[@]}" \
  | ssh "$HOST" "mkdir -p '$STAGE/new' && tar -xf - -C '$STAGE/new'"

ssh "$HOST" "cat > '$STAGE/remote.sh'" <<EOF
set -euo pipefail
cd '$STAGE'

echo '==> Backing up current files to $STAGE/old'
mkdir -p old/static
cp '$APP_DIR/main.py' '$APP_DIR/requirements.txt' old/
cp '$APP_DIR/static/index.html' old/static/

REQS_CHANGED=0
cmp -s old/requirements.txt new/requirements.txt || REQS_CHANGED=1

echo '==> Installing (sudo)'
sudo install -o $APP_USER -g $APP_USER -m 644 new/main.py new/requirements.txt '$APP_DIR/'
sudo install -o $APP_USER -g $APP_USER -m 644 new/static/index.html '$APP_DIR/static/'

if [ "\$REQS_CHANGED" = 1 ]; then
  echo '==> requirements.txt changed, updating venv'
  sudo -u $APP_USER '$APP_DIR/venv/bin/pip' install -q --no-cache-dir -r '$APP_DIR/requirements.txt'
fi

echo '==> Restarting $SERVICE'
sudo systemctl restart $SERVICE

for i in \$(seq 1 20); do
  if curl -fs -o /dev/null http://127.0.0.1:$PORT/; then
    echo "==> Up and answering on :$PORT (deployed $REV)"
    echo "    Roll back with: sudo install -o $APP_USER -g $APP_USER -m 644 $STAGE/old/main.py $STAGE/old/requirements.txt $APP_DIR/ && sudo install -o $APP_USER -g $APP_USER -m 644 $STAGE/old/static/index.html $APP_DIR/static/ && sudo systemctl restart $SERVICE"
    exit 0
  fi
  sleep 1
done

echo '!!  Service did not answer within 20s. Recent log:' >&2
sudo journalctl -u $SERVICE -n 40 --no-pager >&2
echo "    Old files are in $STAGE/old to roll back." >&2
exit 1
EOF

# Run with a real terminal so sudo can ask for the password.
ssh -t "$HOST" "bash '$STAGE/remote.sh'"
