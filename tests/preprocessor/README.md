# Internal C preprocessor tests

Oracle for the in-tree C preprocessor (switch `--sw internal_cpp`), built from the
[cscout](https://github.com/dspinellis/cscout) C-preprocessor test suite.

- `cpp/cppNN-*.c` — test inputs (from cscout `src/test/cpp/`).
- `cpp/cppNN-*.c.out` — expected preprocessed output (from cscout
  `src/test/out/cppNN-*.c.out`, with the fixed two-line cscout harness preamble
  stripped — see `fetch-cscout.sh`).
- `cpp.json` — `diff-prog.py` config (`name: out`, no args, matches `cppNN-*.c`).
- `fetch-cscout.sh` — (re)imports the inputs and goldens.
- `magic/` — hand-written tests for macro expansion inside `/*@ … @*/` and
  `/*$ … $*/` (cscout/gcc/clang do not support these). Added in commit C17.

## Running

Compare the `cpp_dump` binary (added in commit C4) against the goldens:

```sh
cd tests
USE_OPAM='' ./diff-prog.py <path-to>/cpp_dump preprocessor/cpp.json
```

`cpp_dump` reads a `.c` file and prints the preprocessed token stream
reconstructed by `Preproc_output.reconstruct`, whose spacing is tuned to match
cscout's goldens (not gcc's). Some goldens are empty (e.g. `cpp04-pdtest`, whose
`#define`s are all unused) — a valid case.

Trigraph / line-splicing tests (e.g. `cpp01-trigtest`) require translation phases
1–2, which land last (commit C18); they fail until then.
