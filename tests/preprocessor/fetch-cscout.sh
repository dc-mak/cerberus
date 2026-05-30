#!/usr/bin/env bash
# Import the cscout C-preprocessor test suite for use as the internal-cpp oracle.
#
# Inputs : https://github.com/dspinellis/cscout/tree/master/src/test/cpp  (cppNN-*.c)
# Goldens: https://github.com/dspinellis/cscout/tree/master/src/test/out  (cppNN-*.c.out)
#
# cscout goldens begin with a fixed two-line harness preamble:
#     int main();
#     static void _cscout_dummy1(void) { _cscout_dummy1(); }
# which is NOT preprocessor output, so we strip it on import. The remaining lines
# are the expected preprocessed text (with cscout-specific whitespace).
#
# Result layout (diff-prog's "<input>.<name>" convention, name="out"):
#     tests/preprocessor/cpp/cppNN-*.c        (input)
#     tests/preprocessor/cpp/cppNN-*.c.out    (golden, preamble stripped)
#
# Re-run to refresh. Requires curl.
set -euo pipefail

base="https://raw.githubusercontent.com/dspinellis/cscout/master/src/test"
here="$(cd "$(dirname "$0")" && pwd)"
dst="$here/cpp"
mkdir -p "$dst"

# The cscout cpp suite is cpp01..cpp77 (a couple of numbers may be absent).
names=$(curl -sS "https://api.github.com/repos/dspinellis/cscout/contents/src/test/cpp" \
        | grep '"name"' | sed -E 's/.*"name": *"([^"]+)".*/\1/' | grep -E '^cpp[0-9]+.*\.c$' || true)

if [ -z "$names" ]; then
  echo "Could not list src/test/cpp via the GitHub API." >&2
  exit 1
fi

preamble1='int main();'
preamble2='static void _cscout_dummy1(void) { _cscout_dummy1(); }'

count=0
for c in $names; do
  curl -sS -f "$base/cpp/$c" -o "$dst/$c" || { echo "skip input $c" >&2; continue; }
  if curl -sS -f "$base/out/$c.out" -o "$dst/$c.out.raw"; then
    # Strip the two-line cscout preamble if present, else keep verbatim.
    # (Some goldens have trailing spaces on the preamble lines, so trim them.)
    l1=$(sed -n '1p' "$dst/$c.out.raw" | sed 's/[[:space:]]*$//')
    l2=$(sed -n '2p' "$dst/$c.out.raw" | sed 's/[[:space:]]*$//')
    if [ "$l1" = "$preamble1" ] && [ "$l2" = "$preamble2" ]; then
      tail -n +3 "$dst/$c.out.raw" > "$dst/$c.out"
    else
      echo "WARN: unexpected preamble in $c.out (kept verbatim)" >&2
      cp "$dst/$c.out.raw" "$dst/$c.out"
    fi
    rm -f "$dst/$c.out.raw"
  else
    echo "no golden for $c" >&2
  fi
  count=$((count + 1))
done
echo "imported $count cscout cpp tests into $dst"
