# Squaring negative Pell solutions to reuse the positive classification

## Result

The checked replacement proves the existing statement

`x^2 - n*(n+1)*y^2 != -1` for integer `n,x,y` and `2 <= n`

by a first-coordinate congruence. It deletes the independent strong-induction
Pell descent in `ConsecutivePell.lean` and reuses the fundamental-unit theorem
already present in `NativePellBootstrap.lean`.

The first coordinate is sometimes called the half-trace. The actual field trace
is twice that coordinate. Accordingly the prototype helpers are named
`pow_x_mod` and `positive_x_mod`; exposition should say first-coordinate congruence.

## Mathematical mechanism

Write D=n(n+1), and u=(2n+1,2), the existing fundamental positive norm-one unit.
Multiplication of Pell pairs gives

    (u^k * u).x = (2n+1)*(u^k).x + 2n(n+1)*(u^k).y.

Consequently every nonnegative power has first coordinate congruent to 1 modulo
2n. Classification by the existing fundamental unit transfers this congruence
to every positive norm-one pair with nonnegative second coordinate.

Now suppose x^2-D*y^2=-1. Squaring x+y*sqrt(D), then choosing the nonnegative
second coordinate, gives the norm-one pair

    X = 2*x^2+1,    Y = |2*x*y|.

Its first coordinate is positive, and its second coordinate is nonnegative,
without any case split on x or y. The classification gives `2n | X-1`, hence
`2n | 2*x^2`. The original equation gives

    2*x^2+2 = 2n(n+1)*y^2.

Thus `2n | 2`. Since `n >= 2`, positivity and the elementary divisor bound
`Int.le_of_dvd` yield a contradiction.

The proof uses one small induction on powers to preserve a congruence. It has no
new induction on integer solutions, no decreasing second-coordinate construction,
and no `Int.toNat` descent bookkeeping.

## Existing code reused, exact source locations

Snapshot: `9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9`.

- `ConsecutivePell.lean`: private descent declaration/proof at lines 19-64,
  public wrapper at 67-69.
- `NativePellBootstrap.lean`: `firstUnit` starts at 153;
  `firstUnit_fundamental` at 158; the unchanged block ends at 192.
- `FirstPellCarrier.lean`: `first_norm_facts` already demonstrates the related
  first-coordinate divisibility technique for carrier parameters. The new
  contribution is applying a squared negative-norm solution to this positive
  classification, then deriving the obstruction `2n | 2`.

## Proposed migration

1. Move `firstUnit` and `firstUnit_fundamental`, unchanged, to the small new
   `ConsecutivePellUnit.lean` module. Preserve their existing namespace
   `DiophantineConsistency.NativePellBootstrap`, hence preserve existing names.
2. Have `NativePellBootstrap.lean` import this module and delete the moved block.
3. Replace the old descent in `ConsecutivePell.lean` by `pow_x_mod`,
   `positive_x_mod`, and the new proof of the unchanged public theorem.

The attached patch implements exactly these steps. The low-level extraction
avoids importing all native source-row machinery into the arithmetic norm lemma.
A direct import cycle was NOT found in the reviewed target-local graph; do not
claim that a cycle presently exists. The extraction is dependency separation.

## Measured source reduction

Counting nonblank declaration/proof lines, excluding comments, imports,
namespace commands, and the copied/moved foundation:

| Code | Lines |
| --- | ---: |
| Existing private descent plus public wrapper | 49 |
| New power congruence, classification wrapper, and public proof | 33 |
| Reduction in these declaration/proof blocks | 16 (about 33%) |
| Existing fundamental unit declaration/proof moved unchanged | 34 |

These counts include all statement lines consistently. They are a local source
comparison, not a whole-project size or compile-time claim. Imports and the extra
module add a little scaffolding. The mathematical benefit is eliminating a second
Pell descent and retaining one positive classification as the central argument.

## Validation and limits

`PellTracePrototype.lean` is a standalone prototype importing pinned Mathlib. Its
fundamental-unit block is copied verbatim from the current repository solely so
the replacement can be checked independently. In the migration this code is
moved, not duplicated. The successful kernel check reports only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom.

The prototype was checked with Lean 4.32.0 and Mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`. The full ProveIt project was not rebuilt.
The direct arithmetic replacement and the moved low-level module are supplied
as reviewable sources. The huge higher-level native module is unchanged apart
from its import and removal of the moved declarations.

## Novelty boundary

The audit of both excluded proposal collections found no proposal to replace
`ConsecutivePell.norm_ne_neg_one` in this way. This is distinct from already
proposed Pell parity reuse, signed congruence APIs, source-register decoding,
and generic cast normalization. Its prerequisite, the positive fundamental-unit
classification, is already proved in the repository and remains applicable after
those earlier proposals are assumed applied.
