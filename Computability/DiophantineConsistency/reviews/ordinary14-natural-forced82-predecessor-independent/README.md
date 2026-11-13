# Independent review: conditional natural-82 predecessor draft

The three displayed factor equations and nonnegativity assumptions in [the predecessor source](../../research/ordinary14-natural-forced82-predecessor-draft/README.md) are mathematically sufficient for the desired predecessor conclusion in the intended natural-model setting, assuming the stated ordered-ring and natural additive-order properties. The original finite-control receipt and the independent receipt below reproduce. This is a mathematical and source-signature review, not a Lean elaboration or an iPRA proof.

Put `Delta=a²+4a+3`. With `a>=0` in an ordered ring, `Delta>=3>1`. The first equation rules out `r=0` since `ellPart>=0`. If `f=0`, the strong equation becomes `I²+Delta=0`, contradicting nonnegativity of a square. If `y=0`, the auxiliary equation becomes `Delta*t=1`, where `t=(f²−1)*v²`. Since `Delta>1`, the product equation forces `t>0`; **discreteness** then gives `t>=1`, making `Delta*t>=Delta>1`, a contradiction. The cited source helper `ModelDifferenceRing.one_le_of_pos` explicitly requires the corresponding natural-model fact that every positive value is at least one.

The discreteness qualification is necessary: in the nondiscrete ordered field of rationals, `a=0`, `ellPart=0`, `r=1`, `f=2`, `I=3`, `y=0`, and `v=1/3` satisfy all three displayed equations. This is not a counterexample in a model of natural arithmetic; it shows why arbitrary ordered-ring unit reasoning would be insufficient. After nonzeroness is shown, the proposed proof uses natural-model order and `exists_add_of_le` to obtain successors; discreteness alone is not an additive predecessor theorem for arbitrary ordered rings.

The partial-shift source proposes the correct pointwise composition: subtract one in slots 3, 8, and 11, then shift all slots by one; those three slots remain unchanged and the others are incremented. The graph-specific source now proposes deriving the helper's factor hypotheses from an 82 zero: it transfers that zero to the partially shifted 74 valuation, obtains the unit-factor equations from the existing residue and own-zero drafts under beta representation and positivity, converts the auxiliary and strong pair equations to ring equations, and instantiates the helper. Its `a` value and first-factor product are proposed as images of natural-model values, hence nonnegative. Our receipt checks the relevant 74 graph rows and field selections against the pinned graph and checks that the source calls the expected declarations. The first-factor identity additionally uses associativity and commutativity to identify `ell` with `(X*Y*Y)*k`.

These are source-level checks and mathematical implications, not evidence that the proposed calls, tactics, coercions, predecessor extraction, model bridge or imported declarations elaborate. The graph-specific source still assumes beta representation and positivity; the selected symbolic ports must be linked to those assumptions. It does not establish the endpoint, provider/axiom closure, or binding to the physical PDF.

The independent receipt pins the source, checks selected assumptions, model signatures and graph-factor rows, verifies the rational example exactly, and runs finite modular controls for the partial shift. Those finite controls do not replace the universal arguments above.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-forced82-predecessor-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-forced82-predecessor-independent/result.json
```
