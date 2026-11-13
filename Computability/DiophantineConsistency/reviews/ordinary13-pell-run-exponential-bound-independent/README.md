# Independent source review of the paired Pell-state bound

The proposed proof's inequality directions, represented-power identities, model hypotheses, and pairing rewrite agree with the inspected source declarations. No concrete source-level defect was found. The file remains **unelaborated**, so the inspection does not prove that simplification, typeclass inference, tactics or the selected providers actually work in a coherent Lean build.

The Pell source defines `xcoord i a=π₁(run i a)` and `ycoord i a=π₂(run i a)`. In the pinned Foundation source, `pair_unpair` is a simp lemma for `⟪π₁ z,π₂ z⟫=z`, and `pair_polybound` is a simp lemma giving `⟪x,y⟫≤(x+y+1)²`. Their source forms support the proposed `simpa [xcoord,ycoord,sq]`; whether Lean elaborates that exact use remains untested. Given `x,y≤F`, the intermediate sum is at most `2F+1`, and the use of ordered-semiring multiplication has the expected nonnegativity side conditions in the stated arithmetic-model setting.

For the power step, the directions and argument order are correct:

```text
power B u ≤ power (Exp.exp B) u
          = power (power 2 B) u
          = power 2 (B*u) = Exp.exp (B*u).
```

They use the inspected `lt_exp`, `power_mono_base`, reversed `power_two`, and `power_iterate` declarations respectively. The helper also covers `B=0` and `u=0` under the represented-power conventions. For the horizon step, `B=2*(a+2)≥1`, so `i≤u` permits the inspected exponent-monotonicity theorem; the `x_le` and `y_le` results have the same source model assumptions and the resulting transitivity chain has the right direction.

The proposed theorem is still an inequality about `run`, not the exact `PellValueMajorant` predicate. A client must separately normalize `pairValueBound.vval` in context `[result,u,a]`, identify the one-parameter `construction.result` with `run i a`, and elaborate those transformations. The separate zero/successor witness bounds, nested period-formula witnesses, a uniform primitive-recursive code, and model-to-iPRA transfer remain open.

The independent checker pins the proposal and Foundation/project sources, inspects the exact pairing and power lemma signatures and the draft's proof steps, and evaluates the source's natural pairing formula on bounded Pell controls. The tests do not prove the arbitrary-model inequality or validate Lean elaboration. The imported Foundation source has its own `IOpen` assumptions; their inference from the draft's model assumptions, like all provider and instance resolution, is not replayed here.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-run-exponential-bound-independent/check.py | cmp - reviews/ordinary13-pell-run-exponential-bound-independent/receipt.json
```

No Lean, build, staging, axiom report or iPRA proof was run.
