# One implicational proof for both K215 logical layers

This is an isolated, checked refactoring proposal against ProveIt commit
`2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`. It does not change a machine,
enumerator, consistency statement, or set-theoretic interpretation.

## Concrete result

The existing 58-step `DominatedImplication` proof already contains K, Peirce,
evaluation `a -> ((a -> b) -> b)`, and the pivot formula
`(a -> (b -> c)) -> ((b -> a) -> (b -> c))`.
Five further modus-ponens applications derive S. Taking the domination relation
to be `True` supplies the unrestricted `Lukasiewicz.Implicational` interface.
Consequently, the separate 107-declaration `cd_0` through `cd_106` development
in `Lukasiewicz.lean` can be removed.

| Source metric | Before | After |
| --- | ---: | ---: |
| Combined Lean source bytes | 42,715 | 18,668 |
| Combined source lines | 819 | 426 |
| MP nodes in the two logical derivations | 164 | 63 |

The first two metrics compare the original `DominatedImplication.lean` and
`Lukasiewicz.lean` with the proposed core, new `ImplicationalBasis.lean`, and
shortened `Lukasiewicz.lean`. The MP metric counts the 58 core nodes and 106
old independent nodes, versus 58 shared nodes plus five new applications.
It excludes the one-MP `lift_right` API wrapper common to both versions. These
are source-graph metrics, not minimal-proof bounds, whole-repository savings,
or expanded proof-term sizes. No machine-endpoint speedup is claimed.

## Proof of S

Write `B(x,y,z)` for `(x -> y) -> ((y -> z) -> (x -> z))`.
The existing evaluation theorem is `E(y,z) = y -> ((y -> z) -> z)`.

From a theorem `H : T(x -> (y -> z))`, use B once to derive
`T(((y -> z) -> z) -> (x -> z))`. Compose this implication with E using
B and two more MP applications. This gives `T(y -> (x -> z))`.
Thus exchange of two antecedents costs three MP applications.

For S, set `X = a -> b`, `Y = (b -> c) -> (a -> c)`, and
`Z = (a -> (b -> c)) -> (a -> c)`. The existing composition theorem gives
`T(X -> Y)`. The existing pivot theorem, at `(b -> c,a,c)`, gives `T(Y -> Z)`.
Two MP applications to `B(X,Y,Z)` produce `T(X -> Z)`. The exchange rule gives
`T((a -> (b -> c)) -> ((a -> b) -> (a -> c)))`, using three more MP applications.

All five applications are checked in the abstract setting: no decoder,
injectivity, truth code, natural-number arithmetic, semantic completeness,
or assumption about formula representation is used.

## Compatibility

The public `Lukasiewicz.Implicational` structure, its constructor fields,
and `k`, `peirce`, `composition`, and `s` retain their names and types.
They move to a pure module importing the shared core. The original module
imports this new module, so existing callers need no edit. Its entire Tarski
namespace tail is byte-for-byte unchanged.

The core's existing `rho8_all`, `composition`, and `lift_right` signatures and
proof bodies remain unchanged. Three exports are added: `basisK`,
`basisPeirce`, and `basisS`. The new renderer resolves supporting nodes by
their formulas rather than hard-coded generated numbers. The input derivation
is unchanged; the renderer's existing `--lean` and `--rocq` outputs are unchanged.

## Checks completed

- Lean 4.32.0 compiled the 15-module dependency closure, including the unchanged
  Tarski semantic bridge, Code254, KCode222, DomRho8, and KCodeDom.
- A separate typed public API audit and a downstream assumption audit passed.
- The new core results and all four unrestricted basis results are axiom-free.
  Tarski completeness retains `propext`, `Classical.choice`, and `Quot.sound`;
  `cdom_iff_c222` retains `propext` and `Quot.sound`.
- The synchronized generator reproduces the proposed core byte-for-byte.
- Public source headers, structure text, and the unchanged Tarski tail were
  compared mechanically. `git apply --check` accepts the integration patch
  against the pinned checkout.

The complete machine endpoint has not been rebuilt for this proposal. The
checks cover the changed proof and its immediate logical/semantic clients.
Rebuilding the machine endpoint is the remaining integration gate.

## Reproduction and integration

From this directory, with a pristine checkout of the pinned source:

```sh
python3 inspect_refactoring.py --repo /absolute/path/to/ProveIt
python3 verify_closure.py --repo /absolute/path/to/ProveIt --lean /path/to/lean
```

The verifier uses only Lean's shipped libraries for this closure, never edits
the checkout, creates fresh `.olean` outputs, verifies unchanged input sources
against the pinned Git objects, and records source hashes, compiler version,
exit codes, and logs. Its current reproduction command includes both audits
in the same build; the included receipt records the original 15-module build
and the two separately compiled audits.

To integrate after review, run `git apply --check integration.patch` and then
`git apply integration.patch` from the ProveIt root, using the patch's absolute
path when needed. The patch updates the renderer, extends the shared core,
adds `ImplicationalBasis.lean`, and replaces the duplicate proof in
`Lukasiewicz.lean`. Preserve the old derivation in Git history and the supplied
receipts. Refresh the existing endpoint's source/dependency receipts after its
normal validation procedure.

`verification/source_metrics.json`, `verification/closure.json`,
`verification/audits.json`, and their logs contain the evidence for this scope.
