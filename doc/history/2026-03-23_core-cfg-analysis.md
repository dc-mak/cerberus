# Core CFG Analysis

**Date**: 2026-03-23
**Switch**: `--sw cfg`
**Output**: `<basename>.cfg.json`

## Summary

Adds a control-flow graph (CFG) analysis for Core programs. For each user-defined
function, the analysis traverses the Core expression and builds a graph of basic
blocks (nodes) connected by labelled control-flow edges.

## Control-flow constructs

| Construct | Role |
|---|---|
| `Esseq / Ewseq` | Sequential composition; no node created, acc threaded through |
| `Eif` | Branch node (condition text only); if-true / if-false edges |
| `Erun` | Non-returning jump; run edge to target Esave node |
| `Esave` | Labeled loop-header node; absorbs first basic block of body |
| `Eannot / Ebound` | Transparent wrappers |
| Everything else | Atomic — accumulated into the current basic block |

## Key design decisions

### Single-pass accumulator with on-the-fly block merging

`build_expr` threads an `acc` (current open block) through the recursion.
Atomic expressions append to `acc`; control-flow constructs flush it.

In `Esseq(_, e1, e2)`:
- `exits = [single]` (straight-line): carry the same `acc` into `e2` — no flush,
  no seq edge. Chains of atomics accumulate into one block without any extra pass.
- `exits = multiple` (join from Eif): flush all exit accs, create join acc,
  emit seq edges.
- `exits = []` (e1 = Erun): traverse `e2` with a disconnected acc for completeness
  (to emit any Esave nodes needed by forward Erun references).

### No empty nodes

`flush_acc` has precondition `stmts ≠ []`. Only `Esave` may receive an empty acc
(at top of function or at a join point before any atomic). It handles this by
checking `acc.stmts = []` and forwarding `acc.incoming` to the new save node rather
than calling `flush_acc`.

### Forward Erun

`Erun sym` emits edge `run_id → sym` immediately. Since Esave syms are used as node
IDs directly, the edge is valid even if the Esave node hasn't been emitted yet.
All Esave nodes are guaranteed to be emitted by the end of the full traversal.

### Node IDs as symbols

Esave nodes use their Esave symbol as `node_id`. All other nodes use a fresh symbol
(`Symbol.fresh_pretty "cfg_node"` or `"cfg_join"`). This makes Erun targets
resolvable without a lookup table.

### Esave node text

Shows just the header: `save (k : bty) (x1 = e1; x2 = e2)`.
Does NOT include the body (which is shown via sub-nodes).
The first basic block of the body is absorbed into the Esave node via accumulator
threading.

## Files

- `ocaml_frontend/rewriters/core_cfg.mli` — public interface
- `ocaml_frontend/rewriters/core_cfg.ml` — implementation
- `ocaml_frontend/switches.mli` / `switches.ml` — `SW_cfg` / `"cfg"`
- `backend/common/pipeline.ml` — integration point

## Post-implementation addendum

*(To be filled after implementation and testing)*
