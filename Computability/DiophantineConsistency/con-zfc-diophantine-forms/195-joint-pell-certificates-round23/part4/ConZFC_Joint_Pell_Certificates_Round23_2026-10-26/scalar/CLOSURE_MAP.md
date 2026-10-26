# Local proof roles and historical paths

The **current whole numerical specialization** is exactly the four Start-only
4127 ports under `inherited_positive10/native4127/start_only_ports/`, with its
full unmodified proof and controller. No incoming radix-67 or Start-4177 port
is used in either new equation.

`PROOF.md` is the full current ordinary arithmetic composition. Every new
center definition, polynomial identity and signed majorant used in the proof
is explicitly restated there, including the `N=qY` substitution. Its unbounded
Pell, rank, projection and fresh native witness interface is the full local
`inherited_positive10/PROOF.md`, which in turn resolves its inherited proof
sources in that directory's `CLOSURE_MAP.md`. These are the current semantic
dependencies, not generic scalar box assumptions.

The immutable historical source copies in `source_centers/` retain their
original relative references:

* Its `PROOF.md` is the incoming **whole_product/PROOF.md**.
* Its `ALGEBRA.md` is the incoming whole-product exact identity proof.
* Its `COMPACT_PROOF.md` resolves the historical `../compact/PROOF.md` reference.
* Its `exact_polynomials.json` contains the original complete collected formal
  polynomials at the older weights. The current checker recollects independently
  at the NEW free-chart weights `(4,2,1,5,4,2)` rather than trusting those degrees.

Historical references from those files to an old report or old coefficient
closure are attribution context, not current dependencies or new tuple bindings.
Their quotient identities and majorant are completely reproduced in the current
proof; their old square-transport hypotheses are NOT silently inherited into
the free chart. The new `UE*b²` proof is explicitly different.

`verify.py` imports no producer. `replay.py` additionally executes the entire
retained frozen baseline and native clean-copy replay. Finite checks authenticate
numerals, geometry and algebra; the stated ordinary unbounded proofs are not
replaced by finite tests or described as a new end-to-end formalization.
