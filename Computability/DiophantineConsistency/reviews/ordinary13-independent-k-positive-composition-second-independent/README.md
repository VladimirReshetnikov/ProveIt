# Independent source review: positive-k composition

The reviewed `research/ordinary13-independent-k-positive-composition-draft/` proposes the implication from an exact fixed-child zero to positivity of its independent slot 10. The source call directions and arguments agree at the level reviewed; it remains unelaborated and inherits the documented rank-helper orientation issue.

The same `graph intPorts`, `v`, and temporary hypothesis `v 10=0` feed `child_J_positive` and `first_norm`. The beta bound comes from the same fixed-port client. The call to `first_norm_F_lt_q` passes the matching q, beta, J, shifted F and alpha, `X+K0` and r in the source declaration's order. The retained helper's q is `1+J*beta`, whereas the graph client's q is `beta*J+1`; commutative multiplication supplies the proposed equality. Converting `F<q` to `F≤q` is in the correct direction.

The imported generic rank is the model-natural truncated expression `((q−1)*(q−F)+alpha)*(q²−1)+(MC+q*MF)*J`. Its existence is not assumed independently by this client: the proposed rank helper is called under the derived `F≤q`. An independent integer-polynomial normalization confirms the graph client's signed `rankRing` agrees with the child `rankExpr` after commuting products. The final contradiction client receives that same natural rank, the same valuation, child zero and zero-k hypothesis; the concluding order step is directed from k≠0 to k>0.

The composition's README accurately flags the inherited rank-representation source: the retained helper concludes `ι(rank)=signed`, while the child lemma's goal is `signed=ι(rank)` and currently ends in `linear_combination h`. As documented in the separate rank-representation review, that likely needs its hypothesis orientation reversed, such as `linear_combination -h`. This composition imports the unchanged source and does not itself repair the issue. Other simplification, model cast, exact graph binding and provider defects may remain. No Lean build or actual axiom report was produced.

The separate checker pins the sources, reproduces the author's receipt, checks exact argument names/order and same-tuple uses, and independently normalizes the two signed rank polynomials. These checks are source-level evidence, not a Lean parser, type checker, arbitrary-model theorem or iPRA endpoint. In particular, positive k would not by itself prove `eta≤k` or the required parent-child zero correspondence.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-independent-k-positive-composition-second-independent/check.py | cmp - reviews/ordinary13-independent-k-positive-composition-second-independent/receipt.json
```
