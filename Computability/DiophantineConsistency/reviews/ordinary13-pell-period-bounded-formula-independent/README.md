# Independent source review of the bounded Pell formula proposal

The quoted binder names, represented-Pell argument order, last-bound position, and proposed hierarchy and characteristic-code interfaces match the inspected sources. No concrete source-level mismatch was found. This does **not** validate the Lean quotation, syntax, tactic elaboration, provider ancestry or iPRA proof existence: the draft explicitly assumes its evaluation bridge and its period theorem comes from a separate unelaborated source provider.

The proposed quote has free inputs `(m,a)` and existential binders `(c,h,x,y,r,t)`. The source definitions `xDef` and `yDef` use `(output,time,parameter)`, so the occurrences `yDef(c,m,a)`, `xDef(x,h,a)`, and `yDef(y,h,a)` have the intended source-level argument order. The proposed `PeriodEvaluationBridge` explicitly states the equality between that quoted evaluation at `![m,a]` and the six model-coordinate witnesses; it is an assumption, not a proved consequence of the checker. The conditional assembly supplies these witnesses in the same order and uses the separately drafted period theorem.

The existing `bnd` source adds one last coordinate, and its existential clause imposes a strict `<` bound using `lastVar`. The existing implication theorem evaluates the bounded formula at `Fin.snoc e w`; this agrees with the proposed third parameter. The intended `hierarchy_bnd`, language map, three-input bounded Boolean characteristic theorem and open characteristic-matrix signatures match the inspected declarations and the existing `PRARhoBoundedCharacteristic` usage pattern. These observations are source checks, not evidence that the new declarations have been elaborated or that the chosen period provider is compatible.

No bound `w` is constructed by these interfaces. The stated polynomial-growth warning is justified for this particular formula: at parameter `a=0`, the recurrence gives `y_m≥2^(m-1)` for positive m; with `h=2*m*y_m` and `y_h≥h`, the explicitly existentially bound output `y=y_h` is at least `m*2^m`, while `bnd` requires it to be strictly less than w. This does not rule out a larger primitive-recursive bound, a different encoding, or a different proof strategy. Even a characteristic code for the bounded formula would still need the indicated bound, graph binding and logic-transfer work.

The independent checker pins the exact draft and source APIs, checks the quoted clauses, represented-graph signatures, `Fin.snoc`/strict-bound clauses, hierarchy and characteristic interfaces, and repeats small growth controls. These checks do not prove the assumed evaluation equivalence or any Lean theorem.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-period-bounded-formula-independent/check.py | cmp - reviews/ordinary13-pell-period-bounded-formula-independent/receipt.json
```

No Lean, build, staging, provider audit, axiom report or model-to-iPRA transfer was run.
