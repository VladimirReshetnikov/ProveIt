# Independent source review: residue exact-index client

The proposed client passes the actual 90 graph's early-index facts to `P72Exact.indices_ordinary` with the correct arithmetic coordinates: `X=v 6`, `Y=Y p v`, `T=v 5+1`, `eta=v 9+1`, `i'` and u as explicit model-natural witnesses, and modulus `q⁴`. The early source supplies the first-Pell coordinate and `k=2n+4Q*s`; the rank window yields `R+1<q⁴`. The separate `main_index_of_natural_norm` invokes the generic main Pell classification on its explicit natural norm.

The theorem explicitly retains the actual graph zero, represented natural ports, positive J/beta/X, positive-C gap, `R>=26`, rank window, positive strong witness and f, main Pell index and norm, the entire strong equation, and the entire signed-ordinate `absdiff` auxiliary equation with a natural u. It uses the **original** `P72Exact.indices_ordinary`, so eta remains the shifted positive `v 9+1`; the separate eta-natural draft is not assumed here. The output is the proposed exact relation `mainIndex=R` and `2n=R+1`, conditional on all those premises.

No later Bézout property or `q|X` conclusion is hidden in this index client. The main-root, strong and auxiliary graph extraction, fixed-port binding, provider/axiom provenance, parent bridge and iPRA endpoint remain separate. The source's tuple and theorem interfaces were independently checked and the author's receipt reproduces; no Lean elaboration was run.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue-exact-index-model-independent/check.py | cmp - reviews/ordinary13-residue-exact-index-model-independent/result.json
python3 -I -S -B research/ordinary13-residue-exact-index-model-draft/check.py | cmp - research/ordinary13-residue-exact-index-model-draft/receipt.json
```
