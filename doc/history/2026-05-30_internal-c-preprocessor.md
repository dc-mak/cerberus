# Internal C Preprocessor for Cerberus

## Status & session handoff (2026-05-30)

**State:** planning only — *nothing implemented yet*. No code written, no files
created. This plan is final and was iterated heavily with the user; it is awaiting
ExitPlanMode approval. Branch: `preprocessor` (in `/home/dhruv/cerberus`).

**To resume:** re-read this whole file (it is self-contained, incl. Appendix A
algorithm). If still in plan mode, call ExitPlanMode to get approval, then start at
commit **C0**. Build with `make && make install` (not raw dune). Set `USE_OPAM=''`
for tests.

**Decisions already locked (do not relitigate):**
- Internal cpp is **switch-gated** (`SW_internal_cpp`), parallel to external
  `cc -E` which stays the default.
- Magic comments: **macro expansion only** (no directives inside them).
- **Phases 3–4 first**; trigraphs/line-splicing deferred to last commit (C18).
- Test oracle = cscout `cpp*.c` inputs + `cpp*.out` goldens via `diff-prog.py` +
  a standalone `cpp_dump` binary; magic comments get hand-written goldens.
- **Locations are the second key motivation:** accurate columns + Clang-style
  "expanded from:" macro chains. Preprocessor works in `Lexing.position`;
  `Preproc_token` is **parameterised** `'loc t`; `Cpp` lifts via
  `map Preproc_location.of_lexing`. Provenance lives on **`Cerb_position.t`**
  (opaque record field — non-breaking), **not** a new `Cerb_location.t` variant.
  Parser seam = synthetic `Lexing.position` + side-table (forced by Menhir).
- Commit headers `<50` chars, repo `(scope)` style; bodies wrapped 72; explain
  *why*. Code comments = plain `(* … *)` paragraphs priming intuition / citing the
  spec, no boxing.

**Useful facts already gathered (so you needn't re-explore):**
- Existing lexer `parsers/c/c_lexer.mll`; tokens in `parsers/c/tokens.ml`.
- Grammar funnels all locations through `c_parser.mly:17-21`
  (`pos`/`region`/`point`/`pointCursor`) → the single enrichment seam.
- `c_parser_driver.ml`: `to_pos` at `:21`, `after_before_msg` at `:3-18`,
  magic→CN at `:118-127`, `parse_loc_string` at `:77-88`.
- External cpp invocation: `pipeline.ml:125` (`cpp`), default cmd
  `cc -std=c11 -E -C -nostdinc -undef -D__cerb__`.
- `util/cerb_position.mli` — `t` is **opaque**; `util/cerb_location.mli` — `t` is a
  `private` variant (hence provenance goes on position, not location).
- Switch how-to + pass how-to are in CLAUDE.md / the loaded memory.

**Not yet done that the user may want next:** save a memory pointer in
`MEMORY.md` (blocked here by plan mode); actually begin C0.

## Context

Today Cerberus does **not** preprocess C itself.

`pipeline.ml:125` (`cpp`) shells out to
`cc -std=c11 -E -C -nostdinc -undef -D__cerb__`, and the existing lexer
`parsers/c/c_lexer.mll` only *tokenizes already-preprocessed text*.

Because the external `cpp` runs with `-C` (keep comments), CN "magic comments"
`/*@ … @*/` and `/*$ … $*/` survive into the lexer — but their contents are
treated as a comment by `cpp`, so **macros are never expanded inside them**.
A user who writes `#define N 10` and `/*@ requires x < N @*/` gets a literal `N`
in the CN annotation.

The goal is to build an **internal C preprocessor** (translation phases 3–4:
pp-tokenization + macro expansion + directives) implementing the Dave Prosser /
Spinellis algorithm (`expand`/`subst`/`glue`/`hsadd` with hide sets), that
additionally **macro-expands the contents of magic comments**. It should be
correct enough to pass the cscout `cpp` test suite, built as small,
independently reviewable commits.

### Second motivation — accurate source locations

Today the external `cpp` reformats source, so the columns the lexer sees do not
match the original file, and all macro-expansion provenance is lost.

The internal preprocessor must preserve **accurate line *and column*** for every
token, and the **full macro-expansion chain** for tokens produced by (possibly
nested) macro expansion, so Cerberus/CN can emit Clang-style diagnostics:

```
t.c:22:2: warning: type specifier missing, defaults to 'int'
        ILPAD();
        ^
t.c:17:17: note: expanded from:
#define ILPAD() PAD((NROW - tt.tt_row) * 10)    /* 1 ms per char */
                ^
t.c:14:2: note: expanded from:
        register i; \
        ^
```

The primary location is the *use site* (`22:2`); each `note: expanded from:`
points (with a caret) at the relevant token inside successively inner macro
**definition bodies** (`17:17`, then `14:2`).

So every emitted token must carry an ordered provenance chain: its outermost use
location, plus — for macro-expanded tokens — each inner expansion step down to
its spelling location in a macro body.

### Decisions (confirmed with user)

- **Switch-gated, parallel.** New switch `SW_internal_cpp`. External `cc -E`
  stays the default until the internal engine reaches parity.

- **Magic comments: macro expansion only.** Inside `/*@ @*/` / `/*$ $*/`, expand
  C macros in scope at that point; do **not** honor `#define`/`#if`/… written
  literally inside a magic comment.

- **Phases 3–4 first.** Trigraphs (phase 1) and backslash-newline splicing
  (phase 2) are deferred to a final commit.

- **Test oracle:** cscout's own golden outputs, compared with `tests/diff-prog.py`.
  Inputs are `src/test/cpp/cppNN-*.c`; **goldens are `src/test/out/cppNN-*.c.out`**
  (i.e. `<input>.out`, already diff-prog's `<input>.<name>` convention with
  `name=out` — no renaming). **Each golden begins with a fixed two-line cscout
  preamble** that must be stripped on import (it is harness boilerplate, not
  preprocessor output):
  ```
  int main();
  static void _cscout_dummy1(void) { _cscout_dummy1(); }
  ```
  The remaining lines are the preprocessed output, with **cscout-specific
  whitespace** (e.g. a doubled space where an argument carried leading space) —
  so `Preproc_output.reconstruct` is tuned to cscout's spelling, *not* gcc's.
  Magic-comment behaviour is unsupported by gcc/clang/cscout, so it gets
  hand-written golden tests of its own.

- **Locations are first-class.** Tokens carry accurate line/column and a
  macro-expansion provenance chain; integration feeds **located tokens directly
  to the parser** rather than reconstructing text (text loses columns and
  provenance). Diagnostics render the chain Clang-style.


## References & sources

- **Algorithm** — Dave Prosser's complete macro-expansion algorithm (X3J11/86-196),
  annotated/corrected by Diomidis Spinellis:
  <https://www.spinellis.gr/blog/20060626/cpp.algo.pdf>
  The full pseudocode is reproduced in **Appendix A** below. C0 saves a plain-text
  copy (via `pdftotext`) to `doc/history/cpp-macro-expansion-algorithm.txt` for
  easy reference in later commits.

- **Test inputs** — cscout C-preprocessor tests, `cppNN-*.c`:
  <https://github.com/dspinellis/cscout/tree/master/src/test/cpp>
  (raw: `https://raw.githubusercontent.com/dspinellis/cscout/master/src/test/cpp/<name>.c`)

- **Test goldens** — cscout expected outputs, `cpp*.out`:
  <https://github.com/dspinellis/cscout/tree/master/src/test/out>
  (raw: `https://raw.githubusercontent.com/dspinellis/cscout/master/src/test/out/<name>.out`)
  C0 imports these into `tests/preprocessor/`, renaming to diff-prog's
  `<input>.<name>` convention.


## Design

### Layering — a located-token pipeline (NOT text reconstruction)

The preprocessor is a function over a phase-3 token stream, where **every token
carries its full source provenance**.

The expanded stream is converted to parser `Tokens.token`s and fed to the
existing Menhir parser **with locations attached**.

Text reconstruction is used *only* for the standalone `cpp_dump` test oracle (to
diff against cscout goldens); it is **not** on the parser path, because
reconstruct-then-relex destroys columns and macro provenance — the whole point
of the added requirement.

### Location representation across the pipeline

The preprocessor works **entirely in `Lexing.position`** — the raw currency its
own lexer's lexbuf produces. It never touches `Cerb_position`/`Cerb_location`.

`Preproc_token` is **parameterised over its location type**, `'loc
Preproc_token.t`:

- the lexer instantiates it at `(Lexing.position * Lexing.position)` (bare
  spelling region);

- the engine instantiates it at `Preproc_location.t` (spelling + expansion
  chain), introduced only once `Cpp` lifts the lexer stream.

`Preproc_location.t` itself is pure `Lexing.position`. It is lowered to a
provenance-bearing `Cerb_position.t` **once**, at the feed seam (`pos`/`to_pos`).
That is the single `Lexing.position → Cerb_position.t` conversion point.

### Module data flow

```
                       source.c (raw bytes)
                            │
                            ▼
                ┌────────────────────────┐  phase 3: bytes → pp-tokens
                │    Preproc_lexer.mll    │  loc = (Lexing.position pair)
                └───────────┬────────────┘  (no Preproc_location dependency)
                            ▼
        (Lexing.position pair) Preproc_token.t list
                            │
                            ▼
        ┌───────────────────────────────────────────────┐  phase 4 (Prosser):
        │                 Cpp  (engine)                  │  lift via map
        │  lift: map Preproc_location.of_lexing          │  of_lexing, then
        │  expand / subst / glue / hsadd / stringize     │  expand/subst/…;
        │    ├─ Macro_table  (#define/#undef env)        │  directives; builds
        │    ├─ Cpp_eval     (#if/#elif constexpr)       │  expansion frames
        │    └─ directive loop (#include/#line/#error…)  │  via push_expansion
        └───────────────────────┬───────────────────────┘
                                │ Preproc_location.t Preproc_token.t list
              ┌─────────────────┴───────────────────┐
              ▼                                      ▼
   ┌────────────────────┐          ┌───────────────────────────────────┐
   │  Preproc_output    │          │        Preproc_token_feed         │
   │  reconstruct→text  │          │  Preproc_location.t Preproc_token │
   │  (TEST ORACLE ONLY)│          │     .t  →  Tokens.token           │
   └─────────┬──────────┘          │  + synthetic Lexing.position      │
             ▼                     │  + side-table[pos] = Preproc_loc  │
       cpp_dump binary             └─────────────────┬─────────────────┘
             │                                       │ tokens + Lexing.position
             ▼                                       ▼
   diff vs cscout cpp*.out                  ┌────────────────────┐
                                            │  c_parser (Menhir) │ $startpos/$endpos
                                            └─────────┬──────────┘  : Lexing.position
                                                      │ actions call pos/region/point
                                                      ▼
                          pos / to_pos : consult side-table, LineMap-map the
                          Preproc_location → Cerb_position.t (provenance filled)
                                                      ▼
                          region/point (UNCHANGED) → Cerb_location.t → Cabs AST
                                                      ▼
                          later phases (desugar / Ail) hold Cerb_location.t
                                                      ▼
                          Pp_errors / location_to_string read the start
                          position's provenance → "note: expanded from:" carets
```

### New modules

All under `parsers/c/`, auto-included via dune `(modules :standard)`.

Write the `.mli` first for each (per CLAUDE.md). Primary type named `t`, hidden
implementation, `compare`/`print` where applicable.

**`Preproc_location`** (`preproc_location.mli`/`.ml`) — per-token provenance, in
`Lexing.position`:

```ocaml
type frame = { macro_name : string option
             ; use : Lexing.position * Lexing.position }  (* invocation site *)

type t = { spelling  : Lexing.position * Lexing.position  (* where text lives:
              original file for ordinary tokens, a macro body for expanded *)
         ; expansion : frame list }   (* outer→inner; [] for ordinary tokens *)
```

Ops: `of_lexing` (spelling = lexbuf pair, `expansion=[]`); `push_expansion`
(record a macro-invocation frame); `primary` (outermost `use` if expanded, else
`spelling` — the primary caret); `compare`; `print`.

**`Preproc_token`** (`preproc_token.mli`/`.ml`) — the pp-token, parameterised
`'loc t`, exposing `map : ('a -> 'b) -> 'a t -> 'b t`:

- record fields: `kind` (header-name | identifier | pp-number | char-const |
  string-literal | punctuator | magic of `{char; payload}` | other | newline),
  `spelling : string`, `preceded_by_space : bool`, `hide_set` (functional
  `Set.Make(String)`), `loc : 'loc`;

- `compare`/`print` parameterised over the loc's;

- the lexer produces `(Lexing.position * Lexing.position) t`; the engine produces
  `Preproc_location.t t`.

**`Preproc_lexer`** (`preproc_lexer.mll`) — phase-3 tokenizer: `Lexing.lexbuf` →
`(Lexing.position * Lexing.position) Preproc_token.t list`:

- each token's `loc` is the plain `(lex_start_p, lex_curr_p)` pair — **no
  dependency on `Preproc_location`**; columns are accurate because the lexbuf
  reads the original source directly;

- handles pp-numbers (maximal munch), string/char literals, punctuators, comments
  (→ one space, sets `preceded_by_space`), explicit `newline` tokens (the
  preprocessor is line-oriented);

- the magic delimiters `/*@…@*/` / `/*$…$*/` → a `magic` token carrying raw inner
  text + delimiter char + loc;

- header-names (`<…>`) lexed only when the directive handler requests it.

**`Preproc_output`** (`preproc_output.mli`/`.ml`) — **test oracle only.**
`reconstruct : _ Preproc_token.t list -> string` (loc-agnostic), matching cscout
golden spacing (separating space only where adjacent tokens would otherwise
re-tokenize, the `+`/`+` → `+ +` rule). Used by `cpp_dump`; not on the parser
path.

**`Macro_table`** (`macro_table.mli`/`.ml`) — immutable env, `Map.Make(String)`:

- `ObjectLike of Preproc_location.t Preproc_token.t list | FunctionLike of
  {params; variadic; body}` (bodies stored already lifted, empty expansion
  stacks, spelling = position in the `#define`);

- ops: `define` (with §6.10.3#2 redefinition-compatibility check), `undef`,
  `find`, `mem`; threaded **functionally**.

**`Cpp_eval`** (`cpp_eval.mli`/`.ml`) — `#if`/`#elif` controlling-expression
evaluator:

- replace `defined X`/`defined(X)`, macro-expand, map remaining identifiers → 0;

- recursive-descent integer-constant-expression evaluator (full precedence: `?:`,
  `||`, `&&`, bitwise, shifts, comparisons, `+ - * / %`, unary `! ~ + -`) over
  `intmax_t`/`uintmax_t` semantics; returns a bool.

**`Cpp`** (`cpp.mli`/`.ml`) — the engine:

- **on entry, lifts** the lexer's `(Lexing.position*Lexing.position)
  Preproc_token.t list` to `Preproc_location.t Preproc_token.t list` via
  `Preproc_token.map Preproc_location.of_lexing` (empty stacks), then works
  uniformly in `Preproc_location.t`. This lift is *required* because Prosser
  rescans (`expand(subst(…) • TS')` concatenates fresh output with pending input,
  so the sequence must be one loc type);

- holds the mutually recursive `expand` / `subst` / `glue` / `hsadd` /
  `stringize` / `select`, translated **faithfully** from the Prosser pseudocode
  (one module, per CLAUDE.md's mutual-recursion guidance);

- plus the line-oriented **directive loop** with a conditional-inclusion stack;
  token sequences are plain lists; `expand` passes `newline` tokens through (so
  function-like invocations span lines), and the directive scan segments at
  `newline` tokens to find `#`;

- **provenance:** when `subst` emits a macro-*body* token, it keeps the body
  spelling and `push_expansion`es a frame (macro name + use-site region); nested
  expansions push further frames; `glue`/`hsadd` propagate provenance (a pasted
  token takes the left operand's spelling with the combined chain);

- entry point `preprocess : include_dirs:string list -> filename:string ->
  Preproc_location.t Preproc_token.t list`, plus a magic-comment hook running
  `expand` (no directives) on a magic token's inner tokens.

**`Preproc_token_feed`** (`preproc_token_feed.mli`/`.ml`) — the parser seam:

- converts the expanded `Preproc_location.t Preproc_token.t list` into a
  Menhir-compatible token supplier producing `Tokens.token`s, reusing the shared
  decoder (below);

- gives each token a **unique synthetic `Lexing.position`** whose line/column are
  the token's *primary* (use-site) coords and whose `pos_cnum` (or a parallel
  index) keys a **side-table** mapping back to the full `Preproc_location.t`;

- the side-table is what `pos`/`to_pos` and the error path consult to recover
  provenance.

### Why the side-table seam is unavoidable

Menhir's token currency is `Lexing.position` and cannot be changed — even the
incremental API "expects to be supplied with triples of a token and start/end
positions of type `Lexing.position`."

So the rich `Preproc_location.t` must degrade to a `Lexing.position` for the
parser and be recovered afterwards; the side-table is how the chain rides
through. This round-trip is forced by Menhir, not incidental.

### Provenance lives on `Cerb_position.t`, not `Cerb_location.t`

`Cerb_position.t` is an *opaque* type (`cerb_position.mli` exposes only `type t`
+ accessors), so adding a field is a **non-breaking** change — no pattern match
anywhere needs touching.

By contrast `Cerb_location.t` is a `private` *variant* that code matches on, so a
new variant there breaks every exhaustive match. (Putting macro info on the
position also mirrors Clang, whose per-position `SourceLocation` encodes
spelling-vs-expansion.)

```ocaml
(* in cerb_position.ml — internal record, type t stays opaque *)
type macro_frame =
  { macro_name : string option
  ; caret : Lexing.position * Lexing.position }   (* an "expanded from" caret *)

type t = { … existing file/line/col/cnum … ; provenance : macro_frame list }
```

- `caret` uses `Lexing.position` (already carries file/line/col), **not**
  `Cerb_position.t`, so `t` stays non-recursive and no bespoke coords type is
  needed;

- the feed fills `provenance` from the `Preproc_location` frames + spelling
  (outer→inner), each `Lexing.position` `LineMap`-mapped to source coordinates;

- `line`/`column` keep returning the **primary** coords; `from_lexing` defaults
  `provenance=[]`; `compare` ignores it; `to_json`/`change_cnum`/`set_source`
  preserve it;

- **`Cerb_location.t` is untouched** — a `Loc_region (p1,p2,_)` carries the chain
  via `p1`. Only the renderer reads `Cerb_position.provenance`.

### Error reconstruction for unexpected tokens

`c_parser_driver.ml:3-18` (`after_before_msg`) handles parser errors: on an
unexpected token it reconstructs the offending lexeme from `Lexing.position`s
(via `MenhirLib.ErrorReports`).

With the token-feed, the lexbuf is not reading text in the usual way, so this
path must instead recover the offending token's `Preproc_location.t` from the
side-table (keyed by the `Lexing.position` Menhir reports) and render its
spelling + source location **through the macro chain**.

This is explicitly tested: an unexpected token *inside a macro expansion chain*
must be reported at the right place, with the expansion notes (see C16).

### Switch & pipeline wiring

- `switches.ml`/`.mli`: add `SW_internal_cpp`; `| "internal_cpp" -> Some
  SW_internal_cpp` in `read_switch`; add to the equality arm of `pred`.

- `pipeline.ml` `cpp`/`c_frontend`: when `Switches.(has_switch SW_internal_cpp)`,
  run `Cpp.preprocess` and drive the parser via `Preproc_token_feed` instead of
  spawning `cc -E` and lexing text. External `cc -E` stays the default and
  unchanged. `conf.cpp_save` is honored via `Preproc_output`.


## Implementation — small, reviewable commits

One commit per new file/type, per change to an existing file/type (kept
compiling with stubs where a later commit supplies the real behaviour), or per
new piece of functionality. The engine `Cpp` is grown across several functionality
commits.

Example headers follow the convention below (`<50` chars, repo-style `(scope)`
prefix). Build after each with `make && make install`.

### Phase 0 — scaffolding & test oracle

- **C0** — `(cpp) Add design doc for internal cpp` — **DONE (setup)**
  Design doc at `doc/history/2026-05-30_internal-c-preprocessor.md`; algorithm
  text at `doc/history/cpp-macro-expansion-algorithm.txt`; cscout inputs +
  preamble-stripped goldens imported under `tests/preprocessor/cpp/` via
  `tests/preprocessor/fetch-cscout.sh`; diff-prog config
  `tests/preprocessor/cpp.json`. (`cpp_dump` binary + CI wiring still pending —
  they arrive in C4.)

- **C1** — `(cpp) Add Preproc_location provenance type`
  New `preproc_location.{mli,ml}` (Lexing.position-based; `of_lexing`,
  `push_expansion`, `primary`, `compare`, `print`).

- **C2** — `(cpp) Add parameterised Preproc_token`
  New `preproc_token.{mli,ml}` (`'loc t` + `map`, `compare`, `print`).

- **C3** — `(cpp) Add Preproc_lexer (phase-3 tokeniser)`
  New `preproc_lexer.mll` producing `(Lexing.position pair) Preproc_token.t list`.

- **C4** — `(cpp) Add reconstruct, cpp_dump and tests`
  New `preproc_output.{mli,ml}`; new `cpp_dump` `(executable)` in
  `parsers/c/dune`; `tests/preprocessor/` with cscout *no-macro* inputs + goldens
  (renamed to diff-prog's `<input>.<name>`), a `cpp.json` config, and the CI line
  in `.github/workflows/ci.yml`. End-to-end golden test for token/spacing cases
  (`cpp03`, `cpp18`).

### Phase 1 — macro engine (grows `Cpp`)

- **C5** — `(cpp) Add Macro_table`
  New `macro_table.{mli,ml}` (define/undef/find, redefinition check). Unused yet.

- **C6** — `(cpp) Expand object-like macros`
  New `cpp.{mli,ml}`: entry lift via `map of_lexing`; directive loop with
  `#define`/`#undef`; object-like `expand`/`subst`/`hsadd` + provenance push;
  point `cpp_dump` at the engine. Pass `cpp09`/`cpp10`/`cpp11`/`cpp25`.

- **C7** — `(cpp) Expand function-like macros, # and ##`
  Grow `Cpp`: argument collection (paren-matching, comma split outside nested
  parens), `stringize`, `glue`, varargs. Pass
  `cpp04`/`cpp05`/`cpp07`/`cpp12`/`cpp14`/`cpp16`.

- **C8** — `(cpp) Add Cpp_eval constant-expr eval`
  New `cpp_eval.{mli,ml}`. Unit-tested directly; not yet wired into `Cpp`.

- **C9** — `(cpp) Handle conditional directives`
  Grow `Cpp`: `#if`/`#ifdef`/`#ifndef`/`#elif`/`#else`/`#endif` + `defined`, using
  `Cpp_eval`. Pass `cpp22`/`cpp23` + `ansi-p9x`.

- **C10** — `(cpp) Handle #include/#line/#error`
  Grow `Cpp`: header resolution against `include_dirs`, include stack, line
  markers, `#pragma`. Pass `cpp02-inc`.

### Phase 2 — frontend integration & locations

- **C11** — `(location) Add provenance to Cerb_position`
  Add `provenance` field + `macro_frame` + accessors to the opaque
  `Cerb_position` (non-breaking); `compare` ignores it; `to_json`/`change_cnum`/
  `set_source` preserve it. Renderer not changed yet (stub: ignore provenance).

- **C12** — `(cparser) Share token-decoding helper`
  Factor the constant/string/keyword decoding out of `c_lexer.mll`'s `initial`
  rule into a shared helper; `c_lexer` keeps working through it (compilation-
  preserving refactor). Used by the feed next.

- **C13** — `(cpp) Add Preproc_token_feed`
  New `preproc_token_feed.{mli,ml}`: token supplier + shared decoder + synthetic
  positions + side-table. Standalone-testable.

- **C14** — `(cpp) Wire SW_internal_cpp into pipeline`
  Add the switch; change `pos`/`to_pos` (`c_parser.mly:17-21`,
  `c_parser_driver.ml:21`) to consult the side-table; dispatch in `pipeline.ml`.
  Goal: real C files parse via internal cpp with **accurate line/column** (chain
  not yet rendered). Sanity-run `tests/bytes` + CI subset with the switch on.

- **C15** — `(location) Render macro expansion notes`
  Teach `Pp_errors` / `Cerb_location.location_to_string` / `head_pos_of_location`
  to read `Cerb_position.provenance` off a location's start position and emit the
  `note: expanded from:` caret chain. Add the `ILPAD`/`PAD` diagnostics golden.

- **C16** — `(cparser) Fix error loc in macro chains`
  Adapt `after_before_msg` / the error path to recover the offending token's
  `Preproc_location.t` from the side-table and report through the chain. Test:
  an unexpected token inside a nested-macro expansion is reported at the correct
  source location with notes.

### Phase 3 — magic comments & deferred phases

- **C17** — `(cpp) Expand macros in magic comments`
  Macro-expand magic-token inner tokens; feed the expanded located tokens through
  the CN re-lex path (`c_parser_driver.ml:parse_loc_string`). Hand-written
  goldens in `tests/preprocessor/magic/`: macros expand inside `/*@ @*/`, literal
  directives inside are **not** processed, CN diagnostics carry sane columns.

- **C18** — `(cpp) Add trigraphs and line splicing`
  Phases 1–2 as a pre-pass over the input buffer. Pass `cpp01-trigtest`.


## Commit message conventions

- **Header `< 50` characters**, matching the repo style: an optional `(scope)`
  or `[CN]` prefix then an imperative summary (e.g. existing
  `(core rewriter) Copy propagation`, `[CN] (cparser) Parse ghost …`). Use a
  scope like `(cpp)`, `(cparser)`, or `(location)`.

- **Body wrapped to 72 columns**, blank line after the header.

- **Explain *why*, be brief about *what*** — focus on the key or unusual aspects
  and the motivation, not a line-by-line restatement of the diff.

- End commit messages with the `Co-Authored-By` trailer when committing.


## Code comment conventions

- Leave concise explanations **next to the relevant code**, as simple paragraphs
  between `(*` and `*)` — no `(* ***** *)` rules, no left/right boxing.

- Comments should **prime intuition** or **refer to the algorithm specification**
  (e.g. "Prosser `subst`, the `## • T` case" or a STD §6.10 clause), rather than
  re-narrating the code in English.

- Keep them short; one well-placed paragraph beats several restating the obvious.


## Verification

- **Per-commit golden (Phase 0–1):**
  `cd tests && USE_OPAM='' ./diff-prog.py <path>/cpp_dump preprocessor/cpp.json`
  diffs reconstructed output against cscout goldens for that commit's features.
  (See `.github/workflows/ci.yml:68-75` for the `diff-prog.py` invocation pattern;
  the CI line is added in C4.)

- **Columns / provenance (C15):** a diagnostics golden triggering a warning on a
  nested-macro use (the `ILPAD`/`PAD` example), checking the `t.c:L:C` primary
  caret and the `note: expanded from:` chain byte-for-byte.

- **Error-in-macro-chain (C16):** a test feeding an unexpected token produced
  inside a macro expansion; assert the parser error reports the right source
  location and expansion notes.

- **Magic comments (C17):** hand-written `tests/preprocessor/magic/*.c` + `*.out`.

- **Regression / integration:** `cd tests && USE_OPAM='' bash run-ci.sh` and
  `./diff-prog.py cerberus bytes/elab.json`, with and without `--sw internal_cpp`,
  to confirm the external-cpp default is unchanged and the internal path
  elaborates real files.

- **Manual spot-check:** `cerberus --sw internal_cpp --sw at_magic_comments
  file.c` on a file mixing `#define` with a `/*@ … @*/` annotation referencing the
  macro; confirm expansion and column-accurate locations.


## Key files

- `parsers/c/c_lexer.mll` — factor its constant/string/keyword decoding into a
  shared helper reused by the `Preproc_token -> Tokens.token` decoder (C12);
  legacy text path otherwise unchanged.

- `parsers/c/c_parser.mly:17-21` — the four location helpers (`pos`/`region`/
  `point`/`pointCursor`); the single seam for enriched locations (C14).

- `parsers/c/c_parser_driver.ml` — `:21` (`to_pos`), `:3-18`
  (`after_before_msg`, C16), `:118-127` (magic→CN), `:77-88` (`parse_loc_string`,
  C17).

- `util/cerb_position.ml`/`.mli` — `provenance` field + `macro_frame` (C11);
  `util/cerb_location.ml` + `*/pp_errors.ml` renderer (C15). `Cerb_location.t`
  variants unchanged.

- `parsers/c/dune` — new modules (auto via `:standard`) + a `cpp_dump`
  `(executable)`.

- `backend/common/pipeline.ml:125` (`cpp`)/`c_frontend` — switch-gated dispatch
  (C14).

- `ocaml_frontend/switches.ml`/`.mli` — `SW_internal_cpp` (C14).

- `tests/diff-prog.py`, `tests/preprocessor/` (new), `.github/workflows/ci.yml`.


## Risks / open items

- **Golden spacing format** (confirmed in C0): goldens are `cppNN-*.c.out` with a
  fixed 2-line cscout preamble (stripped on import) and cscout-specific
  whitespace. `Preproc_output.reconstruct` must reproduce cscout's spacing (incl.
  argument-boundary spaces), which is the fiddliest part of the oracle. Some
  goldens (e.g. `cpp04-pdtest`) are *preamble-only* (all `#define`s unused) — a
  valid empty-output case.

- **Function-like invocations spanning newlines** and the list-based
  `select`/actuals collection are the subtlest part of the Prosser transcription;
  covered by `cpp12`/`cpp16` in C7.

- **`#include` with `-nostdinc -undef`** parity: default `include_dirs` = file's
  directory + any `-I` dirs; no system paths (matches current flags).

- **`Cerb_position` provenance field (C11):** non-breaking (opaque), but audit
  `from_lexing` (defaults `[]`), `compare` (ignores it), and serialisation /
  `change_cnum` / `set_source` (preserve it).

- **Synthetic-position scheme (C13/C14):** encoding an index in `pos_cnum` must
  not collide with position arithmetic in `after_before_msg`
  (`c_parser_driver.ml:3-18`); use a parallel index if needed.

- **Macro-body spellings (C15):** inner-frame carets require the lexer-recorded
  body positions (kept in `Macro_table`) to have original coordinates.


## Appendix A — Prosser macro-expansion algorithm

Transcribed from the Spinellis PDF (see **References**). Notation: `TS` token
sequence, `T` token, `HS` hide set; `T^HS` is a token with its hide set; `•`
separates a list head from its tail; `{}` is the empty sequence. `Cpp` translates
these `and`-linked in one module (per CLAUDE.md mutual-recursion guidance).

```
expand(TS):
  if TS is {}                              -> {}
  if TS is T^HS • TS' and T in HS          -> T^HS • expand(TS')
  if TS is T^HS • TS' and T is a "()-less macro"
                                           -> expand(subst(ts(T),{},{},HS∪{T},{}) • TS')
  if TS is T^HS • ( • TS' and T is a "()'d macro":
       check TS' is actuals • )^HS' • TS'' and actuals are correct for T
                                           -> expand(subst(ts(T),fp(T),actuals,
                                                            (HS∩HS')∪{T},{}) • TS'')
  otherwise TS is T^HS • TS'               -> T^HS • expand(TS')

subst(IS,FP,AP,HS,OS):
  if IS is {}                              -> hsadd(HS,OS)
  if IS is # • T • IS' and T is FP[i]      -> subst(IS',FP,AP,HS, OS • stringize(select(i,AP)))
  if IS is ## • T • IS' and T is FP[i]:
       if select(i,AP) is {}               -> subst(IS',FP,AP,HS, OS)
       else                                -> subst(IS',FP,AP,HS, glue(OS, select(i,AP)))
  if IS is ## • T^HS' • IS'                -> subst(IS',FP,AP,HS, glue(OS, T^HS'))
  if IS is T • ##^HS' • IS' and T is FP[i]:
       if select(i,AP) is {}:
            if IS' is T'•IS'' and T' is FP[j]
                                           -> subst(IS'',FP,AP,HS, OS • select(j,AP))
            else                           -> subst(IS',FP,AP,HS, OS)
       else                                -> subst(##^HS' • IS',FP,AP,HS, OS • select(i,AP))
  if IS is T • IS' and T is FP[i]          -> subst(IS',FP,AP,HS, OS • expand(select(i,AP)))
  otherwise IS is T^HS' • IS'              -> subst(IS',FP,AP,HS, OS • T^HS')

glue(LS,RS):                               -- paste last of LS to first of RS
  if LS is L^HS • {} and RS is R^HS' • RS' -> L&R^(HS∩HS') • RS'   (* undef if L&R invalid *)
  otherwise LS is L^HS • LS'               -> L^HS • glue(LS',RS)

hsadd(HS,TS):                              -- add HS to every token's hide set
  if TS is {}                              -> {}
  otherwise TS is T^HS' • TS'              -> T^(HS∪HS') • hsadd(HS,TS')
```

Support functions: `ts(T)` = macro replacement list; `fp(T)` = formal parameters;
`select(i,TS)` = i-th actual, comma-delimited outside nested parens;
`stringize(TS)` = single string-literal token of the concatenated spellings.

The two intersection (`HS∩HS'`) choices in `expand`/`glue` are the Standard's
unspecified points; this algorithm picks intersection (maximal replacement without
looping). Our `Preproc_location` provenance is orthogonal to the algorithm: hide
sets prevent re-expansion; provenance frames are pushed as `subst` emits body
tokens.


## Post-implementation addendum

### Progress log

- **C1–C10 done** (commits `(cpp) Add Preproc_location …` through
  `(cpp) Handle #include and #pragma once`). The standalone engine is complete:
  object/function-like macros, `#`/`##`, conditionals + `Cpp_eval`,
  `#include`/`#pragma once`. **40/76 cscout goldens pass**; the rest need cscout
  whitespace quirks (double-space, trailing-space), absent headers, varargs edge
  cases, or phase-1/2 (C18).
- **C11–C16 + C14b done — frontend integration complete and parity-verified.**
  `--sw internal_cpp` parses real files via the in-tree cpp. Differential parity
  over `tests/ci` (gensym-normalised): **136/136 elaboration/UB files and 113/114
  parse-error files byte-identical** to the external `cc -E` path; the external
  default path passes `run-ci.sh` 188/0; cscout oracle 40.
  - C12 exposes `C_lexer.token_of_string` + `defer_typedef` (decoder reuse, keeps
    the `` `LEXER `` staging); C13 `Preproc_token_feed` (side-table positions +
    spelling table); C14 wires `SW_internal_cpp` + the `LineMap.position`
    provenance hook + `pipeline.ml` dispatch; C14b plumbs `-I/-D/-U/-include` from
    `conf.cpp_cmd` (so bundled `libc/include` + `builtins.h` resolve).
  - **`[[`**: kept as `LBRACK_LBRACK`; `preproc_lexer.mll` matches
    `'[' whitespace* '['` as one token (like c_lexer's `lbrack_lbrack`).
    Removing the token and using two `LBRACK` in the grammar was tried and
    **rejected** — it adds 56 array-declarator-vs-attribute shift/reduce
    conflicts (LR(1) can't tell `int a[3][...]` from a following attribute).
  - **C16 error reporting**: the "show offending token" policy is threaded
    explicitly through `handle` (`text_show_token` vs `feed_show_token`) — **no
    mutable global** in `c_parser_driver`. A syntax error on a macro-produced
    token reports the right lexeme at the macro use site. `preproc_lexer` is
    lenient on string/char literals so invalid escapes don't crash the feed.
  - Known minor gap: `0339-invalid-string` reports the lex error at the literal's
    start column rather than the inner bad char (the per-token re-lex loses the
    inner position).
- **Post-review cleanups (2026-05-31):**
  - **Structured cpp flags:** the internal path no longer re-parses `-I/-D/-U/
    -include` out of `cpp_cmd`; `main.ml`'s `mk_cpp_config` builds a structured
    `Pipeline.cpp_config` (one source of truth, the cc -E string derived from it)
    threaded via an optional `~cpp_config` on `c_frontend`.
  - **Location recovery without a global:** removed the `provenance_lookup` global
    from `c_lexer`'s `LineMap`.  The parser now builds the tree with *raw*
    positions (feed positions carry a side-table key in `pos_cnum`); a pure
    `recover = { enrich; show_token }` value, threaded per lexer kind, resolves
    them — error locations in `handle`, the whole tree via
    `Cabs_location_map.enrich` (an **eager** structural traversal over Cabs +
    `Symbol.identifier` + `Annot.attributes`; CN/constants untouched; `-w @8`
    enforces completeness).  Text path uses `enrich = Fun.id` (traversal skipped).
    `[[` is lexed as one token in `preproc_lexer` (LBRACK_LBRACK kept — two-LBRACK
    grammar gives 56 array-vs-attribute conflicts).  Strings/chars lexed
    leniently so invalid escapes don't crash the feed.
  - **LineMap global removed (2026-05-31):** `c_lexer` no longer maintains a line
    map.  Preprocessing is done before the lexer runs, so positions are real: the
    `#` line-marker rule sets `pos_fname`/`pos_lnum` directly (verified an error
    in an `#include`d header still reports the header), and `pos` in the grammar
    is `Cerb_position.from_lexing`.  `C_lexer.flags` gains an `enrich` field;
    `create_lexer ~enrich` returns the lexer plus the `to_pos` it uses for error
    messages.  `c_parser_driver` no longer references `C_lexer.LineMap`; `handle`
    takes `~to_pos ~show_token`, and `parse_tokens` receives the token feed (the
    preprocessor's source-position "line map", built by `Preproc_token_feed.make`
    in `pipeline`).  **TODO:** the CN re-parse story (`parse_loc_string` /
    `magic_comments_to_cn_toplevel`) under this scheme still needs figuring out.
  - **TODOs (deferred, agreed with user):** (1) a *lazy* scheme mapping positions
    only just before printing, and/or a *switch* between eager/lazy (eager chosen
    now for simplicity + zero API change for library backends); (2) once the
    engine is fully working, **investigate Menhir's incremental API** to tidy the
    driver/seam; (3) honour `conf.cpp_save` on the internal path; (4) 0339's
    inner-char column for invalid-string lex errors.

- **Wrapped `cpp` library + `raw_loc_map` redesign (2026-05-31):** the standalone
  `Preproc_*` modules were moved into a self-contained, *wrapped* dune library
  `cpp` (stdlib-only), so they namespace as `Cpp.Location`, `Cpp.Token`,
  `Cpp.Lexer`, `Cpp.Macro_table`, `Cpp.Eval`, `Cpp.Output`, `Cpp.Preprocessor`.
  The parser seam was simplified in several ways the earlier plan did not foresee:
  - **One map, returned by the engine.** `Preproc_token_feed` is **deleted**.
    `Cpp.Preprocessor.preprocess` now returns `Location.t Token.t list *
    raw_loc_map`: an *opaque, lookup-only* side table (`Preprocessor.lookup`)
    keyed by a **synthetic `pos_bol` counter** (unique per non-Newline token, *not*
    an accurate bol). `pos_fname`/`pos_lnum`/`pos_cnum` on each token stay accurate,
    so raw tokens are debuggable; the entry holds the *real* `pos_bol`, the
    macro-expansion chain (`expansions`), and the lexeme. `from_raw map p` swaps the
    key back for the real bol (fixing the column) and attaches the chain.
  - **One lexer instance feeds the parser.** `token_of_string`/`token_of_lexbuf`
    are gone; `C_lexer.create_lexer ~inside_cn ?from_raw ()` (optional `from_raw`,
    `unit` last) is the *single* way to build a lexer on both paths. In
    `C_parser_driver.parse_tokens` a **single** `create_lexer` instance lexes the
    whole stream (so the typedef-deferral TYPE/VARIABLE markers carry across
    tokens); each pull feeds it a fresh per-token lexbuf holding that token's
    lexeme, positioned at its real source start.
  - **Renames:** `enrich`/`enrichment` → `from_raw`/`raw_loc_map`;
    `Cerb_position` `provenance`/`macro_frame` → `expansions`/`macro_use`;
    `Cpp.Location` `macro_frame` → `frame`, `provenance` → `expansions`.

- **C15 done (`bc2724901`):** `Cerb_location.expansion_notes` reads
  `Cerb_position.expansions` and renders the Clang-style `note: expanded from
  macoro 'NAME'` caret chain off a location's start position; the primary caret is
  the outermost macro use. Verified on `tests/cpp/0001`/`0003` and obj-macro chains.

- **C16 inner-char fix (`14debfa0e`) — 0339 gap closed.** The "known minor gap"
  above (invalid-string lex error landing on the literal's start, not the inner
  bad char) is **resolved**:
  - *Non-macro tokens* report the real `inner.lex_start_p` (the single-lexer re-lex
    now positions the per-token lexbuf at the literal's real source start, so the
    bad char's `pos_cnum` is accurate). `0339` now carets the `\e` at `2:6`.
  - *Macro-body tokens* (e.g. `cpp/0003`, where the bad char lives in a macro body
    that is not spelled at the use site) use a new
    `C_parser_driver.Error_in_expansion of Errors.cparser_cause * Cerb_position.t`:
    the supplier resolves the position itself and `shift_innermost_caret`s the
    innermost "expanded from:" note onto the actual bad character, keeping the
    primary caret at the use site. `handle` turns the exception into a CPARSER
    failure directly (no dummy-lexbuf re-resolution).
  - Dead code from the abandoned arg-frame model removed (`rebase_arg`,
    `Location.wrap_expansion`).

- **`tests/cpp` corpus + `run-cpp.sh` (2026-05-31):** `tests/run-cpp.sh` drives
  the shared `ci` corpus through `--switches internal_cpp` (compared to the same
  `ci/expected` oracle), then four **cpp-only** macro tests in `tests/cpp/`
  (`tests/cpp/expected`) that exercise lex/parse errors inside macro arguments and
  nested-macro arguments — caret/notes cases the external `cc -E` path cannot
  reproduce. **Status: `run-ci.sh` 188/0 (external default), `run-cpp.sh` 192/0
  (internal), cscout oracle 44/76.**

- **Known: `parse_tokens` is over-complicated.** The single-lexer feed juggles two
  lexbufs (a per-token `inner` plus a `dummy` that carries positions to Menhir),
  does a TYPE/VARIABLE marker un-pop, and resolves errors bespoke. A `TODO` on the
  function records that it should be simplified later (a good moment for the
  deferred Menhir-incremental-API investigation).

### C17 design — expand macros in top-level magic comments (2026-05-31)

**Goal.** Under `--switches internal_cpp`, macro-expand the contents of a
top-level `/*@ … @*/` magic comment using the macros in scope *at that comment's
position*, so e.g. `#define N 10` makes `/*@ requires x < N @*/` see `10`.

**The Lem obstacle (decided with user).** A magic payload reaches the CN
re-parse as a bare `string` carried in a *Lem-generated* type
(`Cabs.EDecl_magic : Loc.t * string` at top level; `Annot.attributes` for the
statement/loop/call sites), and `cerb_frontend` does not depend on the `cpp`
library — so an OCaml `Cpp.Macro_table.t` **cannot ride through the AST**. The
macro table is therefore threaded *out of band*, not in Cabs.

**Carrier — a local side table (chosen over a raw_loc_map field).**
`Cpp.Preprocessor` captures, per magic comment, the macro table in scope and
surfaces it; `C_parser_driver.parse_tokens` keeps a *local* table keyed by the
magic token's synthetic key and hands it to `magic_comments_to_cn_toplevel`.
- *Snapshot capture (engine).* Within one run of non-directive lines the macro
  table is constant (a `#define`/`#undef` is a directive, which forces a flush),
  so at each flush in `process_lines` every `Magic` token in the chunk shares the
  current `macros`. Record `src-position → macros` into a mutable table threaded
  through `process_lines`/`do_include`. `assign_keys` then copies the snapshot
  into the token's `entry.macro_defns` (new `Macro_table.t option` field, `Some`
  only for `Magic` tokens). The engine's public `macro_defns` type is just
  `Macro_table.t` (already opaque).
- *Driver.* `parse_tokens`' supplier, on the `CERB_MAGIC` it gets back from
  `c_lexer`, looks up the magic token's key in the map and stashes
  `key → macro_defns` in a local `(int, Macro_table.t) Hashtbl` (keyed by the
  synthetic `pos_bol`, which the `EDecl_magic` loc still carries because the magic
  post-pass runs *before* `Cabs_location_map.from_raw`). Keying by the int avoids
  generic equality on `Cerb_location.t`.

**Re-parse — reuse `parse_tokens`, expanding the payload as located tokens.**
`parse_loc_string` gains `?macro_defns`. With `None` (external path, or the
internal path before this change) it is unchanged: a text lexbuf + `create_lexer`.
With `Some defns`:
1. `Cpp.Preprocessor.expand_fragment defns lexbuf` lexes the payload string
   (`Cpp.Lexer.tokens`, lifted via `Location.of_lexing`), runs `expand defns`,
   and `assign_keys` → `(Location.t Token.t list, raw_loc_map)`.
2. Feed that through the *same* token-feed core as the main parser, but with
   `~parse:C_parser.cn_toplevel` and `~inside_cn:true` (so `c_lexer` still decodes
   CN keywords from the expanded lexemes).

**Position resolution — eager for the fragment.** The main path defers position
resolution to a post-pass (`Cabs_location_map.from_raw` over the `TUnit`), which
recovers real `pos_bol` *and* attaches expansion chains. That post-pass **does not
descend into CN subtrees** and expects a `TUnit`, whereas `cn_toplevel` returns a
CN external-declaration list. Writing a full CN traversal is out of scope, so the
fragment feed instead **resolves positions eagerly**: the supplier writes
`Cerb_position.to_file_lexing (from_raw map p)` (real `pos_bol`/`pos_cnum`) onto
the dummy lexbuf, so CN nodes are built with correct columns and *no* post-pass is
needed. Consequence (accepted for this cut): CN diagnostics get **accurate
file:line:column but no “expanded from:” notes** inside the magic comment — except
lex errors, which still route through `Error_in_expansion` and so keep their chain.
`parse_tokens` is refactored into a shared `feed` core parameterised by
`~inside_cn`, `~parse`, and an eager/lazy flag; the top-level wrapper keeps the
lazy `TUnit` post-pass, the fragment wrapper uses eager + no post-pass.

**Scope (chosen).** Top-level `EDecl_magic` only. Statement/loop/call-site magic
re-parses later in `Cabs_to_ail`, which has neither the map nor the snapshots;
threading `macro_defns` there is a deferred follow-up.

**Risks / parity.** Existing internal-path magic tests use no macros, so `expand`
is the identity and the eager-resolved columns must match the current text path;
verified against `run-cpp.sh`. `Cpp.Lexer` must tokenise CN payloads acceptably
(it produces generic pp-tokens; CN keyword/`inside_cn` handling stays in
`c_lexer`). A new `tests/cpp` case exercises a macro used inside `/*@ … @*/`.

**C17 status — done (2026-05-31).** Implemented as above:
- `Cpp.Preprocessor.preprocess` now returns `(tokens, raw_loc_map, macro_defns)`,
  where `macro_defns : Macro_table.t Int_map.t` is built immutably (snapshots
  threaded functionally through `process_lines`/`do_include` like `once`, then
  re-keyed by synthetic key in `assign_keys`). New `expand_fragment`.
- `c_parser_driver`: `parse_tokens` refactored into a shared `feed_parse` core
  (params `~inside_cn ~parse`; always lazy — raw positions ride into the AST and a
  post-pass resolves them). `parse_loc_string` gained `?macros ?from_raw_pos` and
  returns the fragment's `raw_loc_map` (when one was used);
  `magic_comments_to_cn_toplevel` gained `?macro_defns ?from_raw_pos`, looks up the
  in-scope table by the magic loc's `pos_bol`, and resolves the re-parsed CN tree
  against the fragment map (see the CN-chains note below).
- Verified: a macro used in a top-level `/*@ spec … @*/` expands (internal errors
  show the *expanded* tokens / parse states; external show the literal), with
  source-accurate carets.  `tests/cpp/0005` (object-like), `0006` (function-like),
  `0007` (macro-expansion chain on a CN parse error) cover it; `run-cpp.sh` runs
  the cpp-only group with `at_magic_comments`.
  Status: `run-ci.sh` 188/0, `run-cpp.sh` 195/0, cscout 44/76.
- Remaining limitation: statement/loop/call-site magic comments are still
  unexpanded (they re-parse later in `Cabs_to_ail`, which has no `macro_defns`).

#### Macro chains inside CN diagnostics (2026-05-31)

The "expanded from:" notes live in the `expansions` list on a `Cerb_position.t`,
but Menhir hands semantic actions only a flat `Lexing.position`, which can't hold
that list.  The main path copes by *defer-and-recover*: the synthetic `pos_bol`
key rides through the parser inside the `Lexing.position`, then one post-pass
(`Cabs_location_map.from_raw`) walks the AST and rebuilds each position into a
`Cerb_position.t` *with* its chain.

The first C17 cut couldn't apply that to the magic-comment fragment — `from_raw`
skipped CN subtrees — so it resolved the fragment **eagerly** (writing flat
`Lexing.position`s straight onto the dummy), getting correct columns but dropping
the chain inside CN.  That is now fixed:

- `Cabs_location_map.from_raw` gained a `?traverse_cn` flag and a structural
  traversal of the (generated) `Cn` types, reusing the existing `ident`/`type_name`
  rewriters for the `'a`/`'ty` parameters.
- The fragment feed is now plain **lazy** (the `~eager` param and the
  `(file,pos_cnum)`-keyed `spellings` table that propped up eager mode are gone;
  `show_token` is back to the `pos_bol` lookup).  `parse_loc_string` returns the
  fragment's `raw_loc_map`, and `magic_comments_to_cn_toplevel` resolves the CN
  decls against *that* map with `~traverse_cn:true` — which is where the chains get
  attached.
- The outer TU post-pass keeps `~traverse_cn:false` (the default): the fragment is
  already fully resolved, and re-applying the *outer* map would be wrong — a
  resolved real `pos_bol` can collide with an outer synthetic key.  Because the
  outer pass then leaves CN alone, the magic comment's own `loc` (used to build the
  enclosing-region `magic_loc` fields) is resolved explicitly before
  `update_enclosing_region`.

Both lex and parser errors inside a `/*@ … @*/` now carry the chain
(`tests/cpp/0007`).

- **Remaining after C17:** C18 (trigraphs + backslash-newline splicing, phases 1–2
  pre-pass; unblocks `cpp01-trigtest` and the remaining cscout goldens); statement/
  loop/call-site magic-comment expansion (needs `macro_defns` threaded into
  `Cabs_to_ail`). Lower priority: honour `conf.cpp_save` on the internal path;
  simplify `parse_tokens`.

### Integration revision (approved 2026-05-30)

A review question — *how does the new lexer hook into the existing parser, and how
is fidelity with `c_lexer` guaranteed?* — led to a hardened integration design.
Full version: `~/.claude/plans/steady-strolling-dahl.md`. Key points (authoritative
for C11+):

- **`Preproc_lexer` is NOT a replacement for `c_lexer.mll`.** It makes pp-tokens
  for the engine; `c_lexer` keeps making `Tokens.token` for Menhir and stays the
  default (external `cc -E`) path. The internal path is switch-gated only.
- **The seam is one line:** `pos x = C_lexer.LineMap.position x`
  (`c_parser.mly:17`). Menhir is monolithic; the token supplier sets
  `lexbuf.lex_start_p/lex_curr_p` and Menhir reads them as `$startpos/$endpos`.
  Reuse `handle` + `MenhirLib.ErrorReports.wrap` verbatim; swap only the closure.
- **Decode by delegation (fidelity is structural).** The feed turns each expanded
  pp-token into a `Tokens.token` by **re-lexing its spelling through the existing
  `c_lexer` decoder** — `C_lexer.token_of_string ~inside_cn:false` (C12, exposed
  from `c_lexer.mll`). No re-implementation of constant/keyword/string decoding.
  `Magic` → `CERB_MAGIC`; `Newline` dropped; end → `EOF`.
- **Typedef hack reused, not rebuilt.** Factor the `LSIdentifier` deferral out of
  `create_lexer` into `C_lexer.defer_typedef : (lexbuf -> token) -> [ `LEXER of
  lexbuf -> token ]` (preserving the `` `LEXER `` staging tag). Both `create_lexer`
  and the feed wrap their raw producer with it, over the **unchanged**
  `Lexer_feedback` global the **unchanged** parser still mutates. `decode_next`
  (the feed's raw producer) occupies `initial`'s slot but is a different function:
  it pops a pp-token and decodes its spelling.
- **Staging preserved.** `Preproc_token_feed.make : … -> t` is a staged
  constructor (abstract `t`: cursor + side table, fresh per parse);
  `lexer : t -> [ `LEXER … ]`. No shared mutable state across parses.
- **Locations.** The feed precomputes a `Cerb_position` (with the C11 `provenance`
  field) per token endpoint into a side table keyed by a synthetic `pos_cnum`;
  `LineMap.position` becomes a side-table lookup in internal mode. `region`/`point`
  and range composition are untouched.
- **Fidelity gate (C13.5, new + decided):** a token-level differential
  (external+`c_lexer` vs internal+feed, identical `Tokens.token` streams on a
  macro-free corpus) **plus** end-to-end elaboration parity (`run-ci.sh`,
  `bytes/elab.json`) with and without `--sw internal_cpp`, before the switch is
  trusted.
- **Decisions:** keep C1–C9; expose the decoder from `c_lexer.mll`; token +
  end-to-end fidelity gate.

### Earlier progress note (C1–C4)

### Deviations from the plan

- **C4 CI line deferred.** The plan had C4 add the blocking
  `./diff-prog.py <cpp_dump> preprocessor/cpp.json` line to
  `.github/workflows/ci.yml`. Deferred to C18 because (a) the cscout suite only
  goes fully green at C18, so a blocking step would keep CI red across C5–C17,
  and (b) CI runs the *installed* `cerberus` binary, whereas `cpp_dump` is an
  un-installed dune executable — wiring it needs an install/build step best added
  once. The oracle still runs manually exactly as the README documents. At C4,
  16 declaration-only goldens pass (cpp31–cpp45, cpp02).

- **`return code: 0` golden prefix.** `diff-prog.py` prepends a
  `return code: N` line to captured program output, so every golden needs that
  first line. C0's import omitted it; C4 prepends it to all `cpp/*.c.out` and
  updates `fetch-cscout.sh` to emit it on future imports.

- **`cpp_dump` location.** Placed in its own subdir `parsers/c/cpp_dump/` (not a
  bare `(executable)` in `parsers/c/dune`) so the `c_parser` library's
  `(modules :standard)` does not swallow it; it links `mem_concrete` to satisfy
  the virtual `cerb_frontend`.
