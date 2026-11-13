# Independent review of forward norm and positive-gap drafts

The factor extraction, source interfaces and successor-representation argument
are mathematically consistent as stated; this review found no concrete
source-level mismatch. The drafts remain unelaborated and rely on the actual
parent zero, ring facts and signed half-bound explicitly shown in their types.

Given the existing `first_ne_zero` and `auxiliary_ne_zero` facts and discrete
ordered-ring bound `square_ge_one`, the zero equation has two terms at least
1 and two nonnegative squares. Thus the auxiliary square is 1 and the
strong residual square is 0. The latter gives `A=I²`; rewriting the auxiliary
with that coefficient permits the existing `square_aux_ne_neg_one F` lemma
to rule out −1, and `sq_one` yields `U=1`. Positive i and c give `I>0`,
so `A>=1` by `F.discrete`; f is positive and cannot be 1 because that would
force A=0. Discreteness then gives f>=2. With the explicit signed `2R<c`
assumption, the preceding unelaborated order lemma excludes V=1 and yields
`V<y_parent` from U=1. The checker independently confirms the mod-4
square-coefficient exclusion and bounded sphere consequences; the generic
model proof still depends on its `Facts` and on Lean elaboration.

The literal and generic `value71` bodies agree after their auxiliary
implementations are identified; the checker compares these pinned definitions,
normalizing the namespace-qualified `Carrier65.Core` name. The source-level
`change` and evaluator rewrite remain untested and the historical evaluator
has its own object/provider qualifications.

For `0<D : DiffRing V`, the pinned `nonneg_iff` has exactly the orientation
`D=ι a` used by the representation draft. Since D is nonzero, a is positive;
model discreteness gives `1<=a`, and `n=a−1` satisfies `n+1=a`. Therefore
`ι(n+1)=D`. Applying this to `D=y_parent−V` has the correct forward
orientation and directly gives a shifted natural coordinate. None of these
source steps establishes positivity at the actual parent zero by itself.

The half-bound/cast composition, Lean literal graph evaluation, update of the
same remaining coordinates, reverse witness map, all-model zero equivalence
and iPRA endpoint remain separate. Tactics, model cast simplifications,
prospective imports and transitive provider/axiom closure were not checked.

From `Computability/DiophantineConsistency`:

    set -o pipefail
    timeout 30s python3 -I -S -B research/current2011-shear-forward-norm-order-draft/check.py | cmp - research/current2011-shear-forward-norm-order-draft/result.json
    timeout 30s python3 -I -S -B research/current2011-shear-positive-gap-representation-draft/check.py | cmp - research/current2011-shear-positive-gap-representation-draft/receipt.json
    timeout 30s python3 -I -S -B reviews/current2011-shear-forward-norm-gap-independent/check.py | cmp - reviews/current2011-shear-forward-norm-gap-independent/receipt.json

All receipts reproduce; no Lean, build, staging or reviewed-source edits.
