# The Wedding Ledger

A self-hosted wedding planning app I built for my own wedding. It covers
venues, vendors, guests, seating, a timeline checklist, appointments,
and a budget with a payment ledger. It's one FastAPI process, one SQLite
file and one HTML page with no build step, so it runs fine on a small
VM.

The full walkthrough, including which features need extra hardware, is on
my wiki: **[Wedding Planning Tools — Do It Yourself](https://wiki.rockbed.xyz/services/wedding-planning/setup/)**.

## What works with what

| Feature | Needs |
|---|---|
| Dashboard, Timeline, Schedule (`.ics` downloads), Venues, Vendors, contact log, tour notes, Guests, Wedding Party, Seating, Budget and payment ledger, document storage | Just the app |
| Drive time from home to each venue | A free [OpenRouteService](https://openrouteservice.org/) API key |
| Auto-fill from a link, reading contracts and receipts, contract deadlines as tasks, vendor site review | A local [Ollama](https://ollama.com/) server. `qwen3.5:4b` works on CPU only |
| Email sync | A Microsoft 365 mailbox and an Entra app registration |
| RSVP sync and invites | A separate wedding website with an RSVP admin API (not included) |

Features that aren't set up are hidden in the app.

## Before you run it

**The app has no logins.** It only answers requests that arrive on the
machine's loopback address, so you need a reverse proxy on the same
machine (Caddy with `basicauth` is the easy one), and something like
Cloudflare Access in front if it's reachable from the internet. Anyone
who can reach the page can change everything in it.

## Quick start

```bash
sudo useradd -r -s /usr/sbin/nologin weddinghub
sudo mkdir -p /opt/wedding-hub && sudo cp -r main.py static requirements.txt /opt/wedding-hub/
sudo chown -R weddinghub:weddinghub /opt/wedding-hub
cd /opt/wedding-hub
sudo -u weddinghub python3 -m venv venv
sudo -u weddinghub ./venv/bin/pip install -r requirements.txt
```

Copy `wedding-hub.service.example` to `/etc/systemd/system/wedding-hub.service`,
fill in your names and hostname, then:

```bash
sudo systemctl daemon-reload
sudo systemctl enable --now wedding-hub
```

The database and starting checklist get created on first run.

To update the server later from a checkout on another machine, put
`DEPLOY_HOST=<your ssh host>` in a `.deploy.local` file next to the repo
(it's gitignored) and run `./deploy.sh`. It copies the committed `main`
branch, backs up the live files, restarts the service and checks that it
comes back up. Database changes apply themselves on startup.

## Settings

All settings are environment variables in the systemd unit. The main ones:

| Setting | What it's for |
|---|---|
| `HUB_PARTNER_1`, `HUB_PARTNER_2` | Your names. They're saved as text on guests and tasks, so pick them before adding people |
| `HUB_ORIGIN_HOSTS` | Every hostname you open the app at, comma separated. Saves from anywhere else are refused |
| `APP_PUBLIC_URL` | The app's public address, for links in the CSV export |
| `APP_TIMEZONE` | For overdue / due soon (default `America/Chicago`) |
| `OLLAMA_URL`, `OLLAMA_MODEL` | Your Ollama server (default `http://localhost:11434`, `qwen3.5:4b`) |
| `HUB_DB_PATH`, `HUB_DOCUMENTS_PATH` | Where the database and uploads live (default: next to `main.py`) |

`wedding-hub.service.example` lists the rest, including the optional
email and RSVP settings. Put API keys and secrets in a root-only
`EnvironmentFile`, never in `Environment=` lines, which any local user
can read through `systemctl show`.

## License

MIT, see `LICENSE`.
