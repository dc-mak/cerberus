#!/bin/bash
# run-mem2reg.sh — two-phase mem2reg validation
#   Phase 1: --sw mem2reg must not change output of existing tests (0001–0340)
#   Phase 2: --sw mem2reg must eliminate promotable vars from Core (0341–0350)

TESTSDIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)
cd "$TESTSDIR"

source ./tests.sh   # citests, skip
source ./common.sh  # set_cerberus_exec

mkdir -p tmp

pass=0
fail=0

function doSkip {
  for f in "${skip[@]}"; do [[ $f == $1 ]] && return 0; done
  return 1
}

# report <display-name> <file-for-type-check> <ret>
#   display-name: what to print
#   file-for-type-check: bare filename used for *.error.c / *.undef.c detection
#   ret: raw exit / comparison result (0 = success before inversion)
function report {
  local label=$1
  local file=$2
  local ret=$3
  local res=$ret

  if [[ $file == *.error.c || $file == *.undef.c ]]; then
    res=$((1 - ret))
  fi

  if [[ $file == *.unsup.c ]]; then
    cat tmp/result tmp/stderr | grep -q "feature not yet supported"
    res=$?
  fi

  if [[ "$((res))" -eq "0" ]]; then
    res="\033[1m\033[32mPASSED!\033[0m"
    pass=$((pass+1))
  else
    res="\033[1m\033[31mFAILED!\033[0m"
    fail=$((fail+1))
    cat tmp/result tmp/stderr
  fi

  echo -e "Test $label: $res"
}

if [[ $# == 1 ]]; then
  citests=("$(basename "$1")")
fi

set_cerberus_exec "cerberus"

# ---------------------------------------------------------------------------
echo "=== Phase 1: regression (--sw mem2reg must not change output of tests 0001–0340) ==="

for file in "${citests[@]}"; do
  # skip the mem2reg-specific tests — handled in phase 2
  [[ $file == *mem2reg* ]] && continue

  if [[ ! -f ./ci/$file ]]; then
    echo -e "Test $file: \033[1m\033[33mNOT FOUND\033[0m"
    fail=$((fail+1))
    continue
  fi

  if doSkip "$file"; then
    echo -e "Test $file: \033[1m\033[33mSKIPPING\033[0m"
    continue
  fi

  if [[ $file == *.syntax-only.c ]]; then
    $CERB --nolibc --typecheck-core --sw mem2reg ci/$file > tmp/result 2> tmp/stderr
  else
    $CERB --nolibc --typecheck-core --exec --batch --sw mem2reg ci/$file > tmp/result 2> tmp/stderr
  fi
  ret=$?

  if [[ -f ./ci/expected/$file.expected ]]; then
    if [[ $file == *.error.c || $file == *.syntax-only.c ]]; then
      if [ "$(uname)" == "Linux" ]; then
        sed -i '$ d' tmp/stderr
      else
        sed -i '' -e '$ d' tmp/stderr
      fi
      if ! cmp --silent tmp/stderr ci/expected/$file.expected; then
        ret=0
      fi
    else
      if ! cmp --silent tmp/result ci/expected/$file.expected; then
        if [[ $file == *.undef.c ]]; then
          ret=0
        else
          ret=1
        fi
      fi
    fi
  else
    echo -e "Test $file: \033[1m\033[33mMISSING .expected FILE\033[0m"
    continue
  fi

  report "$file [+mem2reg]" "$file" "$ret"
done

# ---------------------------------------------------------------------------
echo ""
echo "=== Phase 2: elimination (--sw mem2reg must remove promotable vars from Core) ==="

declare -A elim_expected
elim_expected=(
  [0341-mem2reg_simple.c]=0
  [0342-mem2reg_multi.c]=0
  [0343-mem2reg_if.c]=0
  [0344-mem2reg_if_one_branch.c]=0
  [0345-mem2reg_loop.c]=1
  [0347-mem2reg_no_promote_arg.c]=0
  [0350-mem2reg_mixed.c]=1
)

for file in "${!elim_expected[@]}"; do
  expected_creates=${elim_expected[$file]}

  if [[ ! -f ./ci/$file ]]; then
    echo -e "Test $file: \033[1m\033[33mNOT FOUND\033[0m"
    fail=$((fail+1))
    continue
  fi

  $CERB --nolibc --pp core --sw mem2reg ci/$file > tmp/core_out 2>/dev/null
  actual=$(grep -c 'create(' tmp/core_out || true)

  if [[ "$actual" -eq "$expected_creates" ]]; then
    report "$file [create($actual)==$expected_creates]" "$file" 0
  else
    echo "  → got create($actual), want $expected_creates"
    report "$file [create($actual)!=$expected_creates]" "$file" 1
  fi
done

# ---------------------------------------------------------------------------
echo ""
echo "MEM2REG PASSED: $pass"
echo "MEM2REG FAILED: $fail"
[ $fail -eq 0 ]
