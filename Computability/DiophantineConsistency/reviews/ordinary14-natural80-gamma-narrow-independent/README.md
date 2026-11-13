# Independent review: narrow natural-80 gamma contradiction

The [narrow source draft](../../research/ordinary14-natural80-gamma-narrow-draft/README.md) states mathematically sufficient **conditional** facts for the proposed gamma-zero contradiction in an `IΣ₁` arithmetic model. It explicitly leaves the graph-to-norm link, port facts, rank bound and index lower bound as hypotheses or separate obligations. Both receipts reproduce; no Lean model theorem or iPRA derivation is established.

For `first_ordinate_lower`, the hypotheses are `P>0`, `n>=2` and `2*ycoord n (2*(P−1)+1)=k`. Positivity justifies the natural subtraction identity `P−1+1=P`; setting `B=2*(P−1)+1` gives `B+2=2P+1`. The cited recurrence equations yield `ycoord 2 B=2*(B+2)`, so `2*ycoord 2 B=8P+4`; the cited strict monotonicity transfers the bound to `n>=2`. The draft does not purport to derive either the recurrence coordinate or `n>=2` from a graph zero.

For `gamma_zero_impossible`, the stated assumptions include `U>0`, `Y>=8`, `k>0`, `R+1<k`, `X<eta+Y*k`, and the exact signed-magnitude main norm with `G=0`. The cited `direct_main_orientation` has no separate positive-`G` assumption, and proposes a positive quotient `d` and the natural balance `U*(X+a*c)+H*(R+1)=H*k+U*d`, where `a=X*Y+Y`, `c=eta+Y*k` and `H=3+4a`. The norm gives the exact identity `d²−((a+1)c)²=1+(2a+2)c²>0`. All quantities here are nonnegative model values, so `d>(a+1)c>X+a*c`; positivity of U and H then makes the balance's left side strictly smaller than its right side because `R+1<k`, contradiction. Even `c=0` would be covered by the positive constant 1, though `X<c` itself excludes that case in a natural model.

The checker pins the draft and three cited source files, inspects the explicit premises and `G=0` instantiation, and checks the square-comparison and recurrence arithmetic identities as exact sparse polynomials. The cited classification and orientation theorem, natural-order instances, tactic scripts, source imports and model consequences are not elaborated here. In particular, the displayed assumptions cannot be silently discharged from an 80-graph zero by this packet. The two `#print axioms` commands are unexecuted; provider/axiom closure and symbolic-byte/PDF bindings remain open.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-gamma-narrow-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-gamma-narrow-independent/result.json
```
