# Independent source review: natural four-block conversion

No mathematical gap was found in the unchecked `research/trace74-natural-block-draft/Trace74NaturalBlock.lean`, SHA-256 `b3f2e1f92ff8686d5f2743252fd19bdda095a87f7d0722e068f91ba758b4aed2`. No Lean was run; imported theorem/provider compatibility and tactic elaboration remain unverified.

The theorem explicitly assumes q=beta*J+1, C>0, C<=q, F<q, HP*J>=1 and a natural R whose difference-ring cast equals the stated signed rank expression. From C>0 and C<=q it gets q>=1 and C>=1; these and HP*J>=1 justify the cast of `C-1` and `HP*J-1`. Monotonicity gives `C-1<=q-1`, and F<q with q>=1 gives `F<=q-1`, justifying the two further truncated subtractions `(q-1)-(C-1)` and `(q-1)-F`. The checked all-ring four-block identity then converts the explicit signed-rank assumption to the claimed natural equation via injectivity of the cast.

No inequality comparing F+C to q is assumed or needed; in particular the signed input `q*(q-F)-C` need not be a natural subtraction. This is a conditional generic conversion. The draft does not obtain a natural rank representative, digit bounds, population hypotheses or any graph zero, and it does not prove a fixed-port guard or iPRA theorem.
