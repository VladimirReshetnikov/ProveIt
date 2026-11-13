# Independent review: positive-83 reverse carrier arithmetic

This focused independent review covers the signed/natural arithmetic and
positive gap in the pinned 83 reverse-root proposal. The distinct graph/tuple
and `CrossRootCut` review is handled separately. The author receipt and the
finite control receipt reproduce; the source remains unelaborated and there
is no Lean/provider/axiom or endpoint validation here.

For natural q,X,K,F and signed `C=q−F−alpha`, the 83 carrier is
`Q=C*(X+K*q)−F*q`. If Q>0 then C>0: otherwise both terms are nonpositive.
The proposed `gap_of_carrier` uses exactly those nonnegative natural casts;
it does not require X≥q², a prior positive gap, or positivity of K. The
resulting strict `F+alpha<q` is what justifies interpreting the model-natural
truncated subtraction C as the signed difference via `P72Root.ι_tsub`.

An actual 83 first-norm zero is proposed to supply Q>0 and b|Q through the
same `root_data`/signed-square and natural-reflection chain reviewed in
`../ordinary13-positive81-carrier-data-independent/`. Here b=J*beta>0 is
explicitly obtained from positive J and represented positive natural beta;
X=q*w>0 follows from q=1+b and positive w. With
`P=C*(X+K)−F`, the identity `Q−P=b*(C*K−F)` yields b|P. Since Q>0,
C*X>0 and q≥1, splitting on the sign of `C*K−F` gives P>0, matching the
called `reduced_companion` assumptions and direction. Signed divisibility is
reflected to a model-natural positive quotient in `positive_target`, which
then constructs a fresh r with the positive root branch. The first norm's
original signed root need not have been positive.

The source composes the proposed forward and reverse witnesses at the same
compact port tuple; the exact 83 parent `PolynomialBridge` is still a premise
of its native client. In particular, the compact beta cast, literal graph
extraction, helper proof scripts and all inherited positive-81 calibration
and provider obligations remain unelaborated. No concrete arithmetic,
divisibility-orientation or premise mismatch was found. The checker exercises
53,143 Q-positive gap cases, all three signs of `C*K−F`, 8,409 applicable
reverse divisibility cases and 2,968 positive-root cases; these are controls,
not a proof for nonstandard models.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive83-reverse-arithmetic-independent/check.py | cmp - reviews/ordinary13-positive83-reverse-arithmetic-independent/receipt.json
```
