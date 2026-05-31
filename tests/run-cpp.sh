#!/bin/bash

# Like run-ci.sh, but drives the same ci corpus through the in-tree preprocessor
# (--switches internal_cpp) instead of the external `cc -E` + c_lexer path.  The
# internal cpp is meant to be a drop-in replacement, so each test is compared
# against the *same* ci/expected/*.expected oracle the external path uses; any
# difference is a real divergence between the two preprocessors.

TESTSDIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
cd ${TESTSDIR}

# This initialises citests and skip
source ./tests.sh

# Load function for setting up CERB and CERB_INSTALL_PREFIX
source ./common.sh

mkdir -p tmp

pass=0
fail=0

# Known internal-cpp-specific divergences from the external path (these pass on
# run-ci.sh but differ here).  Keep this list short and annotated; it is the
# honest record of where the in-tree preprocessor is not yet byte-identical.
cpp_skip=(
)

# Tests that ONLY make sense under the internal preprocessor: they check the
# macro-expansion carets/columns and "expanded from:" notes, which the external
# `cc -E` path cannot reproduce (it collapses an expansion to the macro-call
# site).  They live in their own tests/cpp directory (with tests/cpp/expected),
# so run-ci.sh never sees them; the .expected files capture the internal output.
cpp_only=(
  0001-macro-arg-token-error.error.c        # invalid string char in a macro argument
  0002-macro-arg-parse-error.error.c        # parse error in a macro argument
  0003-macro-macro-arg-token-error.error.c  # arg is a macro expanding to a bad string
  0004-macro-macro-arg-parse-error.error.c  # arg is a macro expanding to a parse error
  0005-magic-comment-macro.error.c          # object-like macro expanded in a CN magic comment
  0006-magic-comment-macro-arg.error.c      # function-like macro expanded in a CN magic comment
  0007-magic-comment-macro-chain.error.c    # macro-expansion chain on a CN parse error
)

function doSkip {
  for f in "${skip[@]}"; do [[ $f == $1 ]] && return 0; done
  for f in "${cpp_skip[@]}"; do [[ $f == $1 ]] && return 0; done
  return 1
}

# Arguments:
# 1: test case name
# 2: result (0 is success)
function report {
  #If the test should fail
  if [[ $1 == *.error.c || $1 == *.undef.c ]]; then
    res="1 - $2";
  else
    res=$2;
  fi

  # If the test is about something currently not supported
  # This can still test the parser
  if [[ $1 == *.unsup.c ]]; then
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

  echo -e "Test $1: $res"
}

if [[ $# == 1 ]]; then
  citests=($(basename $1))
  cpp_only=()
fi

# Run one test under --switches internal_cpp and compare to its .expected.
# $1: the directory holding the test (ci or cpp); $2: the test file name;
# $3 (optional): extra switches appended to internal_cpp (e.g. at_magic_comments).
function run_test {
  dir=$1
  file=$2
  switches="internal_cpp${3:+,$3}"
  if [ ! -f ./$dir/$file ]; then
    echo -e "Test $file: \033[1m\033[33mNOT FOUND\033[0m";
    fail=$((fail+1));
    return
  fi

  if doSkip $file; then
    echo -e "Test $file: \033[1m\033[33mSKIPPING\033[0m";
    return
  fi

  if [[ $file == *.syntax-only.c ]]; then
    $CERB --switches $switches --nolibc --typecheck-core $dir/$file > tmp/result 2> tmp/stderr
  else
    $CERB --switches $switches --nolibc --typecheck-core --exec --batch $dir/$file 1> tmp/result 2> tmp/stderr
  fi
  ret=$?;
  if [ -f ./$dir/expected/$file.expected ]; then
    if [[ $file == *.error.c || $file == *.syntax-only.c ]]; then
      # removing the last line from stderr (the time stats)
      if [ "$(uname)" == "Linux" ]; then
          sed -i '$ d' tmp/stderr
      else # otherwise we assume this is macOS or BSD
          sed -i '' -e '$ d' tmp/stderr
      fi;
      if ! cmp --silent "tmp/stderr" "$dir/expected/$file.expected"; then
        ret=0;
      fi
    else
      if ! cmp --silent "tmp/result" "$dir/expected/$file.expected"; then
        if [[ $file == *.undef.c ]]; then
          ret=0;
        else
          ret=1;
        fi
      fi
    fi
  else
    echo -e "Test $file: \033[1m\033[33mMISSING .expected FILE\033[0m";
    return
  fi
  report $file $ret
}

# Setup CERB and CERB_INSTALL_PREFIX (see common.sh)
set_cerberus_exec "cerberus"

# Running the shared ci corpus, then the internal-cpp-only macro tests
for file in "${citests[@]}"
do
  run_test ci $file
done
for file in "${cpp_only[@]}"
do
  # The cpp-only tests include CN magic comments, which only become CERB_MAGIC
  # tokens (and so are macro-expanded + re-parsed) under at_magic_comments.
  run_test cpp $file at_magic_comments
done
echo "CPP PASSED: $pass"
echo "CPP FAILED: $fail"

[ $fail -eq 0 ]
