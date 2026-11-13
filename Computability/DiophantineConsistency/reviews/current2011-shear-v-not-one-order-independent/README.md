# Independent source review of the forward shear order draft

The proposed order implications and the checked graph-to-carrier expression
are mathematically consistent; this review found no concrete source-level
mismatch. The draft is unelaborated, and the exact model-zero extraction,
coordinate construction and 72/46 bridge remain open.

For `c>=1`, `T>=1` and `2*rank<c`, the product `c*(T−1)>=0`
gives `c*T>=c` and `d=c*T−rank>0`, with `2d>c`. For `f>=2`,
`f²>=4` and `(f²−4)d>=0`, so `f²d>2c>=c+1`. Thus
`f²*(c*T−rank)−c` cannot be 1. No sign restriction on rank is needed.
The source's explicit `hct`, `hgap`, `hf4`, and `hproduct` follow this
chain. Its use of nonlinear tactics remains untested.

For the second lemma, assume the auxiliary norm equals 1, `A>=1`,
`y>=1`, and `V!=1`. If `y<=V`, then `V²−y²>=0`; both
`A*(V²−y²)` and `y²−1` are nonnegative and sum to zero. It follows
`y=1` and `V=1`, a contradiction. Thus `V<y`. The ring inequalities
and the sign of the norm are in the correct direction; this does not
construct the natural coordinate `y−V`.

The pinned `Carrier65.core` defines exactly
`V=f²*(c*(v 6)−rank)−c`, with `f=v 4`, `c=(eta+zeta)*Y+eta`.
The review checker compares the full common prefix/suffix of the literal
71-row parent and 72-row child and their exact five-to-six auxiliary edits;
80 deterministic signed modular evaluations corroborate the shear identity.
Those finite controls do not prove the identity or a zero map.

The stated route to hypotheses is plausible but remains a substantive
binding obligation. In particular, `ArithmeticCarrier94Indices.ordinary_first_indices`
returns `2*R<c` only after its full positive-coordinate, fixed-port, transport,
first/main/ordinary-strong and auxiliary hypotheses. `R` there is a natural
expression using truncated subtraction. A client must derive the same named
rank from the actual parent zero, including the gap that controls `q−F`, and
transport its inequality into `DiffRing V` via the appropriate order embedding.
It must also bind `I²=A` and the auxiliary equation, derive `f>=2` using
`i,c>0` and model discreteness, and represent `y−V` by a positive model
natural. The child-to-parent absolute-value witness, literal Lean evaluation,
all-model zero equivalence and iPRA endpoint are separate obligations.
There is no newly checked theorem or assertion of consistency here.

Both the author's finite receipt and this review receipt reproduce:

    set -o pipefail
    timeout 30s python3 -I -S -B research/current2011-shear-v-not-one-order-draft/check.py | cmp - research/current2011-shear-v-not-one-order-draft/result.json
    timeout 30s python3 -I -S -B reviews/current2011-shear-v-not-one-order-independent/check.py | cmp - reviews/current2011-shear-v-not-one-order-independent/receipt.json

The review pins the inspected draft, both literal graphs and relevant Lean
source texts. No Lean process, build, provider verification or staging was run;
source inspection cannot establish tactic elaboration or the target model casts.
