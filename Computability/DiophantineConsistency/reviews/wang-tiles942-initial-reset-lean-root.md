# Derived finite initialization walls and exact reset alternatives

Date: 2026-10-26. Independent full source/check review and fresh replay:
ROOT. See the author receipts for [initial strips](wang-tiles942-initial-strip-author.md)
and [reset color1](wang-tiles942-reset-horizontal-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942InitialStrip.lean (148 lines) | b20872f398fc330069ba8eec137d295bc6f6418b6c215a53afcff6334128a100 |
| WangTiles942InitialStripChecks.lean (66 lines) | 76f7e6be2f41bac54a1399dd40c4ee6875fedf34eb10da111ebce72168c1c442 |
| WangTiles942ResetHorizontal.lean (92 lines) | 1cba7e914d13a2d6053b5d35b7b308f08093ae99d36c8963952f0de05f663ebc |
| WangTiles942ResetHorizontalChecks.lean (69 lines) | c15cc9f8fd6844b4d0f8f8169f2ba0912709a5bc91522aae219614d6c1651254 |

ROOT read all four complete frozen files before fresh direct runs with
`lake env lean -M6000 -j1`. Each main output was a separate temporary
object; the checks imported the frozen author-built main objects. All
four passed. Main logs are empty and all thirteen axiom reports contain
only the standard axioms. No entire dependency or umbrella rebuild is
claimed.

The initialization theorem requires only actual Allowed row tiles, true
horizontal matching, positive natural periodN, and Start at zero. West3
forces the actual head initializer at1. Periodic Start at-N and periodic
head atN+1 supply finite failures of the left and right initializer tails.
Their first failures have facing color2 or4; minimality excludes another
initializer, leaving exactly the true seam alternative. Every intervening
tile is proved, and wall distances satisfy0<L<=N,2<=R<=N+1. No wall,
globally unique Start, time matching, run or rectangular quotient is
supplied. The marked-plane specialization derives all its row premises.

The South row is seeded: Start leaves1 at0, the actual initializer leaves
headColor(1,0)=4 at1, and both tails leave plain0. It must be compared with
the actual blank machine after its first action, not an all-zero row.
The precise whole-row machine correspondence remains subsequent work.

For horizontal color1, structural family elimination uses the actual
directional target rail bound at least6. Reset tuples have exactly
south434/435/436. Both west1 and east1 also admit genuine seams, retained
in the iff statements. The allowed seam(1,437,1,437) has both horizontal
edges1 but is not reset; thus even their conjunction does not remove the
explicit nonseam requirement. A forged reset with south433 is rejected.

These packets supply local reset grammar and derived initial geometry,
not whole-row run semantics or halting. The native machine-language
equivalence, converse/controller, other frontiers and internal-ZFC proof
remain open. Decimal equation display and size metrics are unchanged.
