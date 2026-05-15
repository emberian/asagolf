#!/bin/sh
# Fetch set.mm (the Metamath set-theory database, public domain) into data/.
# Required only for `modelsplice` and `calibrate`, which measure the ZFC
# grounding of the F1 substrate against set.mm's constructed ℝ.
set -eu

dest="$(CDPATH= cd "$(dirname "$0")/.." && pwd)/data/set.mm"
url="https://raw.githubusercontent.com/metamath/set.mm/develop/set.mm"

if [ -f "$dest" ]; then
  echo "set.mm already present at $dest"
  exit 0
fi

echo "fetching set.mm -> $dest"
mkdir -p "$(dirname "$dest")"
if command -v curl >/dev/null 2>&1; then
  curl -fL "$url" -o "$dest"
else
  wget -O "$dest" "$url"
fi
echo "done ($(wc -c < "$dest") bytes)"
