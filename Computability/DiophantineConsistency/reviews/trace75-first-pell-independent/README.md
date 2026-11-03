# Independent review: trace75 first and doubled Pell facts

The frozen accepted packet supports the conditional source theorem `Trace75Pell.first_and_doubled`. `check.py` rehashes source/copies, runner, Lean binary, recorded input pins, object and captured logs, and independently resolves the direct and selected inherited objects. Exact paths and hashes are in `check-output.txt`. We did not replay Lean or audit complete historical/project/package/dynamic ancestry.

In any `ORingStructure V` model of IΣ₁, the theorem takes arbitrary natural ports `p` with `0 < (p 0 : V)`, an all-positive `v : Fin 10 → V`, and `value75 (ports p) (ι ∘ v)=0` in `DiffRing V`. Let `D=delta p v`, `U0=U p v`, `E0=E p v`, `K=k v`, `C=c p v`, `aa=D*U0*U0*E0`, and **unscaled** `P=X p v*(Y p v*Y p v)`. It produces a single tuple `tau,f,n,I : V`, with `tau,f,n,I` positive and `n≤K`, satisfying

```
E0=tau²,  1+aa=f²,
xcoord n (2*(P−1)+1)=tau,  2*ycoord n (2*(P−1)+1)=K,
I=2*U0*tau*f,
(1+2*aa)²=1+D*I²,  D*(4*aa*(1+aa))=(D*I)²,  C² ∣ I.
```

Both roots and doubled strong identities use the same `tau,f` and the same input tuple. The proof obtains `E0=1+P*(P+1)*K²`, invokes `positive_parameter_solution P tau K`, and uses `K>0` to exclude `n=0`. Its conclusion is **only `n>0`**, not `n≥2`, and it does not identify `n` with the separately recovered odd main index. The theorem is a necessary condition for a positive Lean trace75 zero, not a halt equivalence, trace74 guard, iPRA theorem or Lean theorem interpreting external JSON/coefficient bytes.

The accepted object is `cea9dcd9cc72467aa28113a65178cb7763170960ef0a4b215153537fb77bfbb9`. Its direct `Trace75Factors` provider is the independently reviewed object `1bae9331cfbca4e35cb48916f135b63eedc8b5c827f8f24ae6f12b2dff111975`; direct `ArithmeticPellFirstNorm` and selected root/model/trace objects match recorded pins. First-resolution of the earlier factors overlay and the other paths is checked post hoc, not a complete compile-time closure audit. The receipt records inner Lean exit 0; the sole named report is exactly `[propext, Classical.choice, Quot.sound]` and stderr is empty. The runner rejects coded warnings/errors and `sorryAx`, but does not enforce a named axiom whitelist; that report was independently inspected. The terminal precedes final runner assertions and no separately retained actual outer-exit receipt was found.
