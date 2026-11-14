# Generic and PAeq term-recursion ranks

`rankFinite` generalizes the prior arithmetic-language identity-rank criterion
to any encoded, arithmetic-definable language. Given a term recursion whose
function-node result bounds every child output, it proves the actual recursor
has the identity rank in every IΣ₁ arithmetic model. The criterion is proved
for arbitrary model codes, including nonstandard codes.

`target_bShift_rank` and `target_subst_rank` instantiate it for the current
PAeq language's bound-variable shift and term-substitution recursors. These
are rank prerequisites for bounding witnesses of their recursion graphs; they
do not by themselves establish those graph bounds, formula substitution
compatibility, or a proof-code compiler.

From the repository root, with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-term-rank/check.sh
```

The final module passed a fresh suffix check against the checked PAeq formula
object and audited project/Foundation objects. Printed dependencies contain
no `sorryAx`. The full nested script replay remains pending.
