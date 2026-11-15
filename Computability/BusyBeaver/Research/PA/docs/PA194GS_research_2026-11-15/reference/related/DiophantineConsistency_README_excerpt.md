# A Diophantine equation for syntactic consistency of ZFC

Research started 23 October 2026, from repository commit `22e75dd6b8`.
This directory contains active research, its Lean proofs, and the delivered
manuscripts in [con-zfc-diophantine-forms](con-zfc-diophantine-forms/README.md).
The manuscript collection was moved here from the Cardinals reports tree
on 23 October 2026 at the repository owner's request.

The target is one integer-coefficient polynomial, with an exactly stated
witness domain, whose absence of zeros is equivalent to the absence of a
finite derivation of falsity from the repository's ZFC axiom predicate.
Neither consistency nor inconsistency is assumed.

The current priority is Lean proofs that the smallest constructed equations
under different size metrics have no solutions exactly when `Con(ZFC)`, and
that this equivalence is provable in **intuitionistic PRA**. A Lean theorem
asserting the existence of an object-theory derivation is sufficient; a
printed derivation is not required. The exact candidate theory and proof
boundary are specified in [IPRA_AXIOMATIZATION.md](IPRA_AXIOMATIZATION.md)
and tracked in [IPRA_PROVABILITY_PLAN.md](IPRA_PROVABILITY_PLAN.md).

**Trace75 research candidate (3 November 2026).** A separate
[decimal display](research/trace75-bfs-decimal-display/equation.pdf) gives a
ten-positive-variable, 75-operation, degree-402 candidate. Its displayed
rows, fixed coefficients, liveness and degree have external finite checks,
including a structural comparison with the Lean evaluator. The fixed-port
native, standard and equality-only iPRA proof-existence statements have now
passed a [five-stage final assembly](research/trace75-bfs-ipra-final-assembly-plan/RUNNER.md)
on the compatible trace, reverse and forward provider, with an independent
result audit. The statements use the selected mapped native refutation
negation or the Gödel–Gentzen-translated consistency sentence. The four
retained baseline objects have a separate [direct-producer audit](research/trace75-baseline-four-provenance/README.md);
their upstream transitive ancestry, other unrebuilt ancestry, package/dynamic
inputs and formal external-file semantics remain outside those checks. The
maintained root equation is
unchanged. See the [trace75 plan](research/ten-positive-ipra/PLAN.md) for the
current proof boundary.

**Current proof status (1 November 2026).** Lean has native iPRA proof-existence
endpoints for the maintained [14-variable degree-150 equation](equation.pdf),
the [13-variable 86-operation degree-56 equation](equation86.pdf), the
[13-variable 87-operation degree-36 equation](equation36.pdf), the
[14-variable 90-operation degree-30 equation](equation30-direct.pdf), the
[14-variable 91-operation degree-30 equation](equation30.pdf), the
[15-variable 93-operation degree-26 equation](equation26.pdf), the
[16-variable 96-operation degree-24 equation](equation24.pdf), the
[17-variable 99-operation degree-20 equation](equation20.pdf), the
[22-variable 112-operation degree-16 equation](equation16.pdf), the
[26-variable 124-operation degree-12 equation](equation12.pdf), the
[33-variable 139-operation degree-8 equation](equation8.pdf), the
[30-variable 138-operation degree-8 equation](equation8-30.pdf), the
[42-variable 164-operation degree-6 equation](equation6.pdf), the
[40-variable 160-operation degree-6 equation](equation6-40.pdf), the
[36-variable 148-operation degree-6 equation](equation6-36.pdf), the
[35-variable 145-operation degree-6 equation](equation6-35.pdf), the
[34-variable 144-operation degree-6 equation](equation6-34.pdf), the
[33-variable 143-operation degree-6 equation](equation6-33.pdf), the
[32-variable 142-operation degree-6 equation](equation6-32.pdf), the
[31-variable 141-operation degree-6 equation](equation6-31.pdf), the
[51-variable 187-operation degree-4 equation](equation4.pdf), the
[50-variable 186-operation degree-4 equation](equation4-50.pdf), the
[49-variable 185-operation degree-4 equation](equation4-49.pdf), and the
[47-variable 179-operation degree-4 equation](equation4-47.pdf), and the
[46-variable 178-operation degree-4 equation](equation4-46.pdf), and the
[44-variable 176-operation degree-4 equation](equation4-44.pdf), and the
[43-variable 175-operation degree-4 equation](equation4-43.pdf), and the
[42-variable 174-operation degree-4 equation](equation4-42.pdf), and the
[41-variable 170-operation degree-4 equation](equation4-41.pdf). Each endpoint
uses the native negation of Foundation's particular arithmetized ZFC
refutation predicate. The displayed polynomials, circuit counts and exact
degrees have separate finite checks; the degree calculations are not Lean
degree theorems and no global minimum is claimed. Since 3 November 2026 the
tree also holds native and standard endpoints for the
[22-variable degree-10](research/adaptive-square-sums22-degree10/equation10-22.pdf),
[26-variable](research/adaptive-square-sums26-degree8/equation8-26.pdf),
[27-variable](equation8-27.pdf) and 28-variable degree-8 candidates
([promotion record](reviews/aq22-28-current-source-promotion/README.md)).
The 12-variable, 95-operation, degree-70 free-J graph at the compact44 tuple
`β = 2^590069 − 1` also has native, standard and equality-only endpoints in
the tree ([`Compact44/IPRAOrdinary12`](Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean)).
They rest on its all-model halting calibration, whose 472-module research
closure was [promoted into `Compact44/`](reviews/compact44-source-promotion/README.md).
The smaller 12-variable graphs on the same tuple also have all three endpoints
([`Compact44/IPRAOrdinary12Chain`](Lean/DiophantineConsistency/Compact44/IPRAOrdinary12Chain.lean),
[record](reviews/ordinary12-chain-source-promotion/README.md)):

| Operations | Exact degree |
| --- | --- |
| 94 | 84 |
| 92 | 164 |
| 91 | 172 |
| 90 | 172 |
| 89 | 172 |

Package 115's 13-positive, 87-operation, degree-51 free-J equation is the
thirteen-positive 51 / 87 frontier point. It has all three endpoints too
([`Compact44/IPRAOrdinary13`](Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean),
[record](research/ordinary13-freej87-endpoint/README.md)). They come from an
all-model reduction to the 95-operation literal.
Package 72's 13-positive, 98-operation, degree-28 equation P13 is the
lowest-degree thirteen-positive point. It also has all three endpoints
([`Compact44/IPRAOrdinary72`](Lean/DiophantineConsistency/Compact44/IPRAOrdinary72.lean),
[record](research/ordinary13-p72-endpoint/README.md)). These rest on a
dedicated soundness proof, through the six compact44 leaf facts, and a
converse from the canonical halt data.
Its fourteen-positive sibling P14 (101 operations, degree 24) is the
lowest-degree fourteen-positive point. It has all three endpoints as well
([`Compact44/IPRAOrdinary72P14`](Lean/DiophantineConsistency/Compact44/IPRAOrdinary72P14.lean),
[record](research/ordinary13-p72-endpoint/README.md#the-fourteen-positive-sibling-p14)).
P14 promotes P13's product `E = XY` to an unknown and adds the residual
`E − XY`, so in every `IΣ₁` model its zeros are exactly P13's.
Package 65's fourteen-positive 92-operation, degree-26 equation also has all
three endpoints
([`Compact44/IPRAPositive65`](Lean/DiophantineConsistency/Compact44/IPRAPositive65.lean),
[record](research/fourteen-p65-endpoint/README.md)). It reuses P13's generic
soundness sections, with the exact-index section split so that it accepts 65's
ordinary strong norm (`P72Exact.exact_ordinary`). Its converse reuses P13's
extraction of the halt data.
Package 64's fourteen-positive 83-operation, degree-30 equation has all three
endpoints too
([`Compact44/IPRAPositive64`](Lean/DiophantineConsistency/Compact44/IPRAPositive64.lean),
[record](research/fourteen-p64-endpoint/README.md)). Its finalizer is a sum of
squares minus one. A local norm minimum (`P64Norm`) shows that this forces the
auxiliary residual to be `1` and the others to vanish. Its early congruence
uses the modulus `Y²` with `gcd(Y², H) ∣ 9` (`P64Early`). An independent
[captured-provider replay](research/fourteen-p64-independent-replay/README.md)
and [artifact review](reviews/p64-captured-replay-independent/README.md)
check the eight P64 modules with one import shim. The package’s missing
pinned source and payload files have been [restored](research/fourteen-p64-payload-provenance/RESTORATION.md);
file-to-Lean port equality remains external.
For package 65, an [alternate captured-provider assembly](research/p65-unconditional-ipra-alternate-provider/README.md)
checks the three unconditional endpoints for the same P65 Lean expression,
using a separately constructed halt-side witness and a
[62-module replay](research/p65-reverse-provider/README.md) of the reverse
direction. A further [30-module captured-provider replay](research/p65-canonical-endpoint-provider/README.md)
checks the merged canonical endpoint source and has an independent manifest
and log review. A later [post-merge replay](research/p65-post-merge-replay/README.md)
recompiled all eight modules in the manifest-visible closure of the changed
P72 sources, including the endpoint, and passed an independent artifact
[review](reviews/p65-post-merge-replay-independent/README.md). These replays
inherit transitive provider ancestry; the external file binding remains
separate from the Lean checks.
Package 73's thirteen-positive 92-operation, degree-30 equation has all three
endpoints
([`Compact44/IPRAPositive73`](Lean/DiophantineConsistency/Compact44/IPRAPositive73.lean),
[record](research/thirteen-p73-endpoint/README.md)). Its zeros map to zeros of the
95-operation free-J literal: the first and main carriers coincide, and the
normalized strong norm is the ordinary one with index `Δi`. The converse uses
the halt data.
Package 62's thirteen-positive 83-operation, degree-114 equation has all three
endpoints as well
([`Compact44/IPRAPositive62`](Lean/DiophantineConsistency/Compact44/IPRAPositive62.lean),
[record](research/thirteen-p62-endpoint/README.md)). They rest on four new pieces:
a product-unit guard, a centered two-root restoration, an early congruence
modulo `4q⁴` with `gcd(4q⁴, H) ∣ 3`, and a signed index theorem for the
ordinary-blank ordinate `c(Tf − 1) − Rf²` (`OrdinaryBlankSignedIndex`).
Package 57's twelve-positive 89-operation, degree-258 equation followed
([`Compact44/IPRAPositive57`](Lean/DiophantineConsistency/Compact44/IPRAPositive57.lean),
[record](research/twelve-p57-endpoint/README.md)). It needs three further
pieces:

- a four-root restoration of its fused main-and-first carrier;
- the plus-sign variant of the ordinary-blank index theorem, because its
  fused strong/auxiliary norm leaves the sign of `f` free;
- in the converse, the odd-ordinate residue `y_halt ≡ −1 (mod 4(Δic²)²)`.

**CURRENT2011 carrier forms (2 November 2026).** The lower-operation and
lower-degree carrier forms of the maintained coefficient tuple now also have
native, standard and equality-only iPRA endpoints. They cover the 14-variable
67/106, 66/118, 71/80 and 72/68 forms ([`ModelCarrierCurrent`](Lean/DiophantineConsistency/ModelCarrierCurrent.lean),
[`ModelCarrierSpheres`](Lean/DiophantineConsistency/ModelCarrierSpheres.lean))
and the 13-variable 69/174, 70/140, 71/128, 73/126, 74/122, 72/124, 77/96,
76/96, 75/96 and 84/92 forms ([`ModelThirteenCarrier`](Lean/DiophantineConsistency/ModelThirteenCarrier.lean),
[`ModelThirteenForms`](Lean/DiophantineConsistency/ModelThirteenForms.lean),
[`ModelThirteenStrong`](Lean/DiophantineConsistency/ModelThirteenStrong.lean),
[`ModelThirteenSquares`](Lean/DiophantineConsistency/ModelThirteenSquares.lean)).
The 14-variable 67-operation degree-94 form of
[package 188](con-zfc-diophantine-forms/188-pell-orientation-exact-projection/native/README.md),
which uses the ordinary strong norm `(i c²)² = Delta (f² − 1)`, has the same
three endpoints since 3 November 2026
