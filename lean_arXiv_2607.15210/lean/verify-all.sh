#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

# Normal usage installs the pinned dependencies. --no-setup reuses them.
setup=1
jobs=2
while [[ $# -gt 0 ]]; do
  case "$1" in
    --no-setup) setup=0; shift ;;
    --require-complete|--require-unconditional) shift ;;
    --jobs)
      if [[ $# -lt 2 || ! "$2" =~ ^[1-9][0-9]*$ ]]; then
        echo '--jobs requires a positive integer.' >&2; exit 2
      fi
      jobs="$2"; shift 2 ;;
    *) echo "Usage: $0 [--no-setup] [--jobs N] [--require-unconditional]" >&2; exit 2 ;;
  esac
done
command -v lake >/dev/null || { echo 'Install elan and add lake to PATH; see ../readme.md.' >&2; exit 1; }
command -v python3 >/dev/null
if [[ "$setup" == 1 ]]; then
  # Lake reads the committed manifest; do not resolve newer dependencies.
  lake exe cache get
  python3 -m venv ../python/.venv
  ../python/.venv/bin/python -m pip install -r ../python/requirements.txt
fi
python=python3
if [[ -x ../python/.venv/bin/python ]]; then python=../python/.venv/bin/python; fi
mkdir -p verification
printf 'running\n' > verification/exit_code.txt
trap 'code=$?; printf "%s\n" "$code" > verification/exit_code.txt' EXIT
"$python" scripts/verify_lean.py --jobs "$jobs"
"$python" ../python/verify.py
"$python" scripts/result_index.py --check
"$python" scripts/check_coverage.py --require-unconditional
echo 'All indexed paper results passed Lean verification; all Python checks passed.'
