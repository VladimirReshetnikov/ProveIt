# Proposed h-witness replacement for the Pell period

This source-only client addresses the h obligation from the six-witness conditional `WB` draft. The existing h is **exactly** the candidate bound, so no witness change or positivity assumption is needed. The proposed proof and its prospective imports are unelaborated; the source receipt is not a Lean proof.

Before h is introduced, the outer environment is `[c,m,a]`. The candidate bound `boundH` is the polynomial `2*#1*#0`, namely `2*m*c`. The literal `bodyH` contains four remaining existentials in order x, y, r, t, followed by `finalBody`. The draft proposes to unpack them, use the separately stated `BodyEvaluationBridge` on the vector `[t,r,y,x,h,c,m,a]`, extract its equation `h=2*m*c`, and return the **same** h and original body evidence. This preserves every graph and witness, including at c=0.

`hReplacement` keeps the body-evaluation bridge as an explicit premise; `hReplacement_closed` proposes to supply the separately drafted bridge. Both the closed client and the bridge remain unelaborated. The four-quantifier `change`/evaluation steps, eight-slot vector reduction, `BodyData` conjunction projection and the `BoundTerm.vval` simplification are exact points requiring a compatible Lean check. The import names an inert prospective module, not an authenticated provider.

This addresses only the h replacement. The c/x/y replacements, six hierarchy facts, full `WB` assembly and all dependent source/object compatibility remain open. A model-level `WB` theorem, even if checked, would not by itself supply a uniform primitive-recursive bound/code for the complete period formula or an iPRA derivation. The conditional parent lift and displayed consistency endpoint remain separate.

The checker pins the source dependencies, checks the quoted body and bound signatures, traces the intended contexts and tests 1,125 finite `(c,m,a)` instances. It does not inspect Lean's generated AST or prove the replacement. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-period-h-replacement-draft/check.py | cmp - research/ordinary13-pell-period-h-replacement-draft/receipt.json
```

No Lean, build, staging, provider authentication or axiom report was performed.
