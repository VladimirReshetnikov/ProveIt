# Independent review: reverse cross-product and 80 output

This review covers `research/ten-positive-reverse-cross-prototype` and `research/ten-positive-80-reverse-output-parts-prototype`, their frozen source statements and accepted author checks. `check.py` verifies the current source and runner against their receipt pins, copied source, output object and log hashes, successful exit, axiom output, and first selection of each source-direct import against the runner's hardcoded path/hash. Full paths, hashes, and receipt hashes are in `check-output.txt`. The review did not replay Lean; source-object ancestry, transitive provider resolution, packages and dynamic libraries remain inherited.

`TenPositiveReverseCross.cross_zero` is universally quantified over an arbitrary commutative ring and `M,tau,f,y,u,I,Q,Z`. It assumes the **same** values satisfy `Z=M*(tau*f*y)`, `Q=I*I` and `I*I*u*u+y*y=1+I*I*y*y`, and concludes exactly

```text
(Q-1)*Z*Z - (M*M)*(tau*tau*f*f)*(Q*u*u-1) = 0.
```

The proof rearranges the auxiliary norm as `(I*I-1)*y*y=(I*I*u*u-1)` and factors the residual; no cancellation, division, nonzero assumptions or positivity are used. The explicit ring-general statement does not construct any witnesses. The selected direct `ReverseCarrier.olean` provider is the same object reviewed in `reviews/ten-positive-reverse-carrier-ingredients-independent` (SHA `614ce881139dbf86b9080fa156e87f2c84d0b19eceabc522b008f44b8c9ebbaa`).

`TenPositive80ReverseOutputParts.output_zero` takes arbitrary integer parameter tuple `p : Fin 4 → ℤ`, arbitrary commutative ring and valuation `v : Fin 10 → R`, and scalar `tau,f,y,u,I` with six explicit same-witness hypotheses:

```text
(graph p).e.evalRing v = tau*tau
f*f = (graph p).a.evalRing v+1
(graph p).q.evalRing v = I*I
(graph p).v.evalRing v = u
(graph p).z.evalRing v = (graph p).m.evalRing v*(tau*f*y)
I*I*u*u+y*y = 1+I*I*y*y
```

Then `(graph p).output.evalRing v=0`. The reviewed source uses `Direct80Graph.output_eval` and `g_eval`, then the cross theorem, for this exact selected symbolic 80 graph; `(graph p).m.evalRing v` is the same M in the two identities. These hypotheses are **not** derived here, and no valuation, positive coordinates, 90-to-80 implication, arithmetic-model join, fixed external parameter binding, or iPRA proof follows solely from this theorem. The tuple is symbolic; the separate known external K0-byte mismatch is not resolved by this result.

Successful observations are `cross-attempt02` and `parts-attempt02`. Their exact selected object hashes are `4f9440ae58ba151097fcfbb040a519adbff3414577022b821a50e8c4a15eb4d0` and `a74ef818061432bddc4914aea57c52e3e08e705ffb385ccf4fe6b387ce07b33e`. Both author `#print axioms` reports list `[propext, Quot.sound]`. In the parts receipt the direct imports select the cross object above and `/tmp/tenpositive-80graph-d2v79zbc/Direct80Graph.olean` SHA `95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4`. The runner also separately pins the transitive `ReverseCarrier` object; at review time its first matching path on the parts receipt's `LEAN_PATH` is `/tmp/reverse-carrier-fr1w8a_6/ReverseCarrier.olean`, with the same hash. That post-hoc transitive path inspection is narrower than a complete transitive import or source-object audit.
