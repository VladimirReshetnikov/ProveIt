# C: remove the external beta-positivity parameter from the positive zero-set equivalence

Pinned repository commit: `3299f4aa4c9ae38b0f5a1c00a1f0d23f6cbdb114`.

## Concrete existing interfaces

`GapSource66.lean` currently assumes `hβ : 0 < ports 0` in:
- `old_positive_gaps`;
- `fromOld_positive`;
- `positiveZeroEquiv`;
- `exists_positive_zero_iff`;
- `exists_positive_nat_zero_iff`.

The existing `toOld_positive` theorem has no zero-set premise and genuinely needs
an appropriate sign condition. It must NOT simply lose `hβ` at that generality.
For example, with all input registers equal to 1 and beta=-2, q=-1 and the
transformed register 16 is 0. This is a positive input, not a source zero.

## Arithmetic fact supplying the omitted guard

Write beta = ports 0, J = x 0, L = x 24, N = x 16 and q = 1+beta*J.
The actual first two rows give:

- Both systems: `L = q^2 - 1`.
- Old system: `N = q*(1+L)`.
- Gap system: `N = q*L`.

On either positive zero set J>=0, L>0 and N>0. The final factor is positive,
so q>0. Since q is an integer, if q were at most 1 it would equal 1, forcing
L=0; therefore q>1. Thus beta*J>0, and J>=0 implies beta>0.

The common checked kernel uses a positive integer D:

```lean
theorem beta_pos_kernel {β J L N D : ℤ}
    (hJ : 0 ≤ J) (hL : 0 < L) (hN : 0 < N) (hD : 0 < D)
    (hquad : L = (1 + β * J)^2 - 1)
    (hlinear : N = (1 + β * J) * D) : 0 < β
```

D=L and D=1+L are its two applications. Positivity is recovered from a solution;
it is not asserted for arbitrary parameter tuples. When beta<=0, both complete
positive zero sets are empty, so an equivalence between them remains valid.
Strict positivity of L is essential to the sign-recovery claim: with beta=0,
J=1,L=0,N=1, the old first two rows vanish but beta is not positive. This is only
a boundary example for the two rows, not a claimed full source solution.

## Guard-free equivalence without a classical choice of a guard

Let `A` and `B` denote the two solution subtypes and let `G` be beta positivity.
The baseline supplies `e : G -> A ≃ B`. The equations supply `ga : A -> G` and
`gb : B -> G`. Define:

```lean
def discharge {A B : Type*} {G : Prop} (e : G → A ≃ B)
    (ga : A → G) (gb : B → G) : A ≃ B where
  toFun a := e (ga a) a
  invFun b := (e (gb b)).symm b
  left_inv a := (e (ga a)).left_inv a
  right_inv b := (e (gb b)).right_inv b
```

Lean's proof irrelevance aligns the guards in the inverse laws. No element is
chosen from an empty solution type and no proof of G is required globally.
The source-specific application is a five-line definition of
`positiveZeroEquiv_all ports`, followed by
`(positiveZeroEquiv_all ports).exists_subtype_congr` for integer existence.
The existing `positive_nat_iff` then supplies the positive-natural endpoint.

The supplied patch is additive: every existing declaration is retained, and the
new APIs are `gap_positive_beta`, `old_positive_beta`, `positiveZeroEquiv_all`,
`exists_positive_zero_iff_all`, and `exists_positive_nat_zero_iff_all`.
Users of the new endpoints no longer thread a separate beta-positivity proof.
The old API remains available unchanged for compatibility.

## Evidence and implementation boundary

`GuardDischarge.lean` is an isolated Lean 4.32/Mathlib prototype. It copies the
complete literal `GapSource66.rows` and `SplitCertificate59.sourceRows`
declarations from the pinned source into separate namespaces. The copied
function bodies are unchanged. `table_binding.json` records the declaration
hashes; namespaces deliberately differ so no cached project theorem is imported.
The source-specific guard proofs call the scalar kernels directly with rows
0 and 1, so their compilation checks definitional binding to the actual tables.

The prototype checks all of:
- the generic guarded-equivalence discharge;
- the shared integer sign kernel;
- old and gap literal-row normalizations;
- beta positivity for both exact positive source zero sets;
- the guard-free equivalence and existence adapter, with the existing guarded
  equivalence supplied as an explicit parameter;
- absence of positive zeros on either side for beta<=0.

The complete prototype compiled with exit code 0. `compile_log.json` contains
compiler output and standard axiom lists. `discharge` uses `[Quot.sound]`; the
arithmetic and endpoint proofs use only `[propext, Classical.choice, Quot.sound]`.
There is no `sorryAx`, admission, or new axiom declaration.

`guard_free_equivalence.patch` and the complete proposed `SourceGuard.lean` and
`GapSource66.lean` implement the same additive adapter against the real module
names. Full project-import integration has NOT been compiled. The checked
prototype's `e` parameter is discharged in that patch by the existing maintained
`positiveZeroEquiv ports`. This is reuse of an established theorem, not an
additional mathematical premise of the new public result.

The proposed integration adds 90 physical lines, including the entire reusable
helper. This is an interface and hypothesis simplification, not an immediate
line-count reduction. No runtime improvement or complete build is claimed.

## Relationship to proposal B and the assumed baseline

This uses the same positive-factor source arithmetic as proposal B, but its
endpoint is stronger: a public equivalence of full solution sets for every
parameter tuple. The family relationship should be explicit; do not count the
shared sign/factor mechanism twice as independent mathematics.

The independent novelty audit found no prior proposal recovering beta positivity
from solution membership or eliminating this external parameter. The nearest
prior packet b, section 8.3, supplies q,L,N decoding equalities; those are assumed
already available. Packet f projects beta positivity from an existing beta_min
premise; it does not derive that premise from source equations. The generic
equivalence-discharge utility itself is not claimed as new mathematics.

## A smaller direct route for a later integration

The guard-recovery adapter is minimally disruptive because it reuses the old
public equivalence. A more direct proof of the guard-free equivalence needs even
less arithmetic: gap row 1 gives q>0 from N=qL, and old row 1 gives q>0 and
N-q=qL from N=q(1+L). The P-gap is supplied independently by rows 3,5,6.
Thus future rewriting of the positivity chain can avoid the quadratic row and
beta recovery altogether. This is an implementation refinement of C, not an
extra independently counted proposal. It has not been integrated or assigned
hypothetical source savings.

## Hash boundary clarification

All canonical table hashes include the single LF immediately after the closing table bracket. The old table is 1774 UTF-8 bytes, SHA-256 `bb4b3bba67a6c924be4659789ddad7e87fa7cb050f1343dc939e6e74a523deca`. This exact region is identical in the repository, algebra prototype, and guard prototype. The initial guard receipt omitted that LF and therefore hashed 1773 bytes as `931674ff3c6862678f1cf2fd56e0b484df9ffe0ea9c0ac67259075b438964428`; there was no function-body difference. Both conventions are recorded explicitly in the updated manifest.
