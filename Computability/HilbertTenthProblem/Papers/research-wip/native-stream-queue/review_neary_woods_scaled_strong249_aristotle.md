# Independent review of the corrected scaled-strong249 U9 bundle

**PASS with the separately frozen degree correction.** All six complete sources cost249=129M+120A, retain43 positive witnesses and have the identical complete positive zero tuples as their respective250 parents. The supported degree bounds are **936** for geometry-only scaling, **1038** for joint-only and **1048** for both, in each program interface. The original934/1046 derivations are not accepted. Geometry-only remains the best proved degree bound among these equal-cost variants. The separate universal84 frontier is unchanged.

This review binds both the unchanged original trio and the correction; neither may silently stand in for the other:

| Artifact | SHA256 |
|---|---|
| Original249 MD | `2230f44faee7e2ecebb0ce29722462f121a49e85addf3740d8b8b54efd7bc8a4` |
| Original249 PY, inert | `ba382dda0e52d6821a5808a3dcc92fb45c4e8bbf0b5e1c2510b9b607ccea21ad` |
| Original249 JSON | `e8fb322a18ec77cf9936ebb7d9e25d86414b66f8db561c4a64edb2ef16aba35c` |
| Degree correction MD | `ada1718ff4e93eb4b48e50d1362b8912973c6d629e1f724878a4e12804a39f11` |
| Degree correction JSON | `573effd459ea14b1ca82b98cc3a61a5ba37e41ada68965200cf382f35ebe1366` |

All are under `/tmp/` with basenames `neary_woods_scaled_strong249_tesla` and `neary_woods_scaled_strong249_degree_correction_tesla`.

## Complete static source audit

I independently reconstructed each child as a map of literal row definitions from the two actual250 arrays, then compared every one of the1494 emitted rows. The only difference between the two parent source interfaces is the first duration producer: its fixed program input is `program_bound` or `program_E`. Their declared parameter counts are six or five including ordinary x; both retain43 existential positive witnesses and all11 fixed-numeral roles.

For each scaled core the three private intermediates `ic2,ic22,normalized_strong_Q` are deleted, two rows are added, and R16 and the strong subtraction are changed. I checked the exact old private consumer sets and the paid c², Delta*c² and f² definitions. The removed coefficients have no additional consumers. A single-core variant changes the final subtraction to its already paid Delta; the both-core variant pays one extra multiplication for the discriminant product.

Fresh static topology and liveness checks find249 live rows and all supplied ports live in each variant. Single-core variants retain244 literal parent definitions, delete3, edit3 and add2. Both-core variants retain239 literal definitions, delete6, edit5 and add5. All domains, program interfaces, fixed U9 recipes and fixed-numeral recipes are identical to the parent. The certificate before the final subtraction costs248=129M+119A with the stated single product comparison. This is not a248-operation polynomial.

I also traversed the complete product spine as a graph, stopping at the16 declared parent factor names. Each factor occurs exactly once in its15 multiplication rows, including each strong factor. This verifies the complete-output scope of the scaling argument, rather than assuming a handwritten finalizer unrelated to the saved source. No row values or source polynomials were evaluated or propagated by the checker.

## All-ring identities and positive-domain cancellation

At each actual cut, `Ac2=Delta*c²`. The old auxiliary coefficient is `Delta²*i²*c⁴`; the new square `(i*Ac2)²` is identical over every commutative ring. The auxiliary norm is consequently unchanged, and the changed strong factor is exactly Delta times the old strong factor. The private-consumer audit and unchanged product spine lift these identities to

```
F_geo=Delta_g*F250,
F_joint=Delta_j*F250,
F_both=Delta_g*Delta_j*F250.
```

The final subtractions are necessary and are charged. No zero equation or recovered unit was used to derive these identities.

The author correctly proves both multipliers positive before invoking the parent theorem. I checked the actual loader and hatted-pack definitions against the displayed formulas. Positive inputs and fixed positive d0,r0 give M>0, Q>=2, B>=2, duration_J>0 and q0>0. The geometry X and Y are then positive directly.

For the joint side, the literal hatted selector pack subtracts exactly `1+P+P²`, leaving `S1+S2+P*S0+P²*S1>=0`; the hatted output pack leaves `ZU+P*ZV0+P²*ZV1>=0`. The shared range word `H_U+P*H_V` is strictly positive. Thus Zhigh is positive even when all four unshifted selectors vanish, without assuming the signed repunit equation or bit typing. The low field `16B*(M*(quotient_hat-1)+z)+8` is positive before imposing a quotient equation. Consequently F3>0, q>1, `Z0=(q-1)F3>=0`, and both joint X and Y are positive. Therefore each `Delta=(a+1)(a+3)>0` on the entire stated positive supplied domain.

Cancellation is now legitimate and gives equality of complete positive tuples with250, at the same ordinary input and program parameters. The corrected source does not require refreshed native witnesses. Parent universality, chronology, input loader, signed pretyping and unbounded existential history remain inherited from the accepted250 theorem. The author does not confuse the scaled strong factors with unit factors: after cancellation they equal their discriminants, while the parent factors equal1. The two numbered original boundary remarks correctly preserve this distinction and the failure of unrestricted signed-zero equivalence.

## Degree finding and corrected manual proof

**Review remark 1 (retained incorrect geometry accounting).** Original MD lines219–225 state `deg Yg<=1`, `deg ag<=4`, `deg Delta_g<=8` and the bounds934/1046. The first three assertions are false: the literal `Yg=(2*geo__odd_half+1)*Q` multiplies two degree-one quantities. I reported this during review. The author retained the original bytes and issued the pinned correction. With ell the linear part of load_r, d0 the fixed repunit divisor, r0 the fixed recoder radix and j the duration quotient, the nonzero leader is

```
(Delta_g)_top=4*r0²*d0^8*geo__odd_half²*ell^6*j².
```

Its degree10 directly refutes the discriminant bound8. The correction properly calls934/1046 unsupported by the stated product-bound argument; it does not claim to have proved exact total degrees exceeding those numbers.

I independently checked the remaining parent bound manually from the actual formulas. Geometry has `(deg X,deg Y,deg a,deg Delta,deg c)=(3,2,5,10,3)`. The genuine main-norm cancellation gives14; the auxiliary norm gives40; the first norm9; normalized strong24; index6; coupled-linear6. These sum99. The four outer factors have bounds4,2,2,3 and sum11.

For the joint core, the actual packed prefixes give q0 at most5, q at most14, F3 at most13 and Z0 at most27. Hence X<=41, Y<=15, a<=56, Delta<=112, c<=16. The main norm uses `D0=X+ga*(4a+3)` of degree at most57, giving129 after cancellation. The auxiliary coefficient has degree at most290 and its square gap at most32, giving322. The other four factors have bounds73,178,57,57. Their sum is816. Thus the full parent product bound remains99+11+816=926; it does not inherit the erroneous discriminant8 claim.

Multiplying by the actual discriminants now gives936,1038,1048. The correction JSON overrides precisely the six intended metadata fields and binds the unchanged complete-source hashes. No on-zero degree simplification, saved-array degree propagation, exact total-degree claim or global optimum is needed.

## Coverage and evidence limits

I read the full original271-line MD and213-line PY inertly, its complete six-source structure and relevant receipt metadata, the full138-line correction and its JSON, the full438-line250 proof, both250 arrays, and the full147-line84 scaled-strong proof. Shared parent definitions were checked across the two interfaces, rather than treating their duplicate occurrence as a second mathematical proof. The static comparison covers every child definition in all six arrays, along with full topology, liveness, consumer and interface checks.

The immediate parent pins are250 MD `1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330`,250 JSON `d2f1ae7870cb8ec295d4401a8e9c951047f0e92cf2b6e6f4bb723c6b483f1ebf`, and84 MD `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`. The full compiler, external U9 simulation and ancestral Pell results remain inherited through that accepted parent; they were not independently recertified from scratch here.

Only newly written static metadata code ran before this review froze. It has no source-value evaluator or degree propagator. No author, predecessor, supplied, archived or frozen helper was executed or imported; the author's64 prefix contexts and five coefficient checks were read but not replayed. No complete native tuple or compiler table was materialized, and no repository/Git mutation occurred. The companion receipt includes all six static results and correction bindings. The new static checker and receipt are frozen evidence, not an authorized future replay suite.
