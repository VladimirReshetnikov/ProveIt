# Independent source review of the Pell-run majorant client

The proposed valuation, one-parameter projection and final application have the intended source-level shapes. In particular, after selecting the Pell blueprint, construction and `pairValueBound`, `PellValueMajorant` is exactly the `hH` premise of `PRAWitnessPR.wb_resultDef`. No concrete interface mismatch was found. This is an **unelaborated** client of two unelaborated source drafts; it is not evidence of a checked Lean theorem or a complete witness bound.

In the context `[result,time,parameter]`, the proposed term's `#2` and `#1` select parameter and time respectively. The inspected constructors give

```text
F = exp2(2*(parameter+2)*time, 0)
  = 2^(2*(parameter+2)*time * 2^0),
H = (F+F+1)*(F+F+1).
```

Thus the proposed valuation statement has the intended `H=(2F+1)²` form and does not depend on the result slot. Its `simp` proof, including quoted-term valuation, numeral normalization, `exp_zero` and `two_mul`, remains an elaboration obligation; source-level algebra and finite controls cannot show that Lean's simplifier closes it.

For `j : Fin 1`, only `j=0` occurs, and `e j.succ.succ=e 2`; therefore the proposed parameter function equals `![e 2]`. The exact `Fin.cases`/`funext` proof text appears in the existing `PRAWitnessPR` source. Replacing that function in the proposed majorant and unfolding `run` matches the upstream horizon theorem with `u=e 1`, `a=e 2` and the existing `i≤e 1` hypothesis. The `rw` and `change` steps are plausible by these definitions, but their actual elaboration and instance/provider selection have not been tested.

The generic result theorem also requires witness-bounded zero and successor clauses. Its `WB` conclusion concerns model-level witness bounds and does not by itself supply a single uniform code bounding every nested witness of the bounded period formula. Those premises, the quoted period evaluation, full code/correctness, and classical-to-intuitionistic transfer remain open.

The independent checker pins the exact source drafts and generic interfaces, checks the constructor and `hH` shapes, verifies the copied finite-vector proof pattern, and evaluates asymmetric time/parameter and unused-result-slot controls. These are source and finite arithmetic checks, not a Lean proof.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-run-majorant-client-independent/check.py | cmp - reviews/ordinary13-pell-run-majorant-client-independent/receipt.json
```

No Lean, build, staging, provider audit, axiom report or iPRA derivation was produced.
