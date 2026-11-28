#!/usr/bin/env bash
# List or inspect published Goldbach statements without contacting a task server.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
case "${1:-list}" in
  list|show)
    python3 - "$root/research/gaps.json" "${1:-list}" "${2:-}" <<'PY'
import json
import sys
from pathlib import Path

path, action, gap = sys.argv[1:]
entries = json.loads(Path(path).read_text(encoding="utf-8"))["gaps"]
if action == "list":
    for entry in entries:
        print(entry["id"], entry["plain_statement"]["en"])
else:
    entry = next((entry for entry in entries if entry["id"] == gap), None)
    if entry is None:
        sys.exit(f"Unknown Goldbach gap: {gap}")
    print(json.dumps(entry, ensure_ascii=False, indent=2))
PY
    ;;
  *)
    echo 'Usage: tools/catalogue.sh [list | show GAP]' >&2
    echo 'Submit one proof file via GitHub, as described in CONTRIBUTING.md.' >&2
    exit 2
    ;;
esac
