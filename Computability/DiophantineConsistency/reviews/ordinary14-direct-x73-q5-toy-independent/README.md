# Independent review: q=5 direct-X toy

The proposed positive 73-graph toy witness at `(beta,K0,MC,MF)=(4,1,2,5)` has q=5, R=339 and X=2^339 not divisible by 5. The literal factors agree with the witness substitutions. The first Pell recurrence gives `4m | k−R−1`, while `25 | Y` gives `U=25Y | m=XY²`, so the corrected gamma is integral. The reviewed Pell floor and same-index auxiliary constructions supply the remaining symbolic identities and positivity under their stated hypotheses. These enormous Pell witnesses are not expanded by the checker; one independent smaller same-index auxiliary completion is evaluated.

The fixed-q parent exclusion is conditional on a separate valid exact-index and trace replay for that toy parent. A toy-port construction does not resolve existence equivalence at the actual compact ports or establish an iPRA theorem. No Lean is run. Run `python3 -I -S -B check.py` and compare with `result.json`.
