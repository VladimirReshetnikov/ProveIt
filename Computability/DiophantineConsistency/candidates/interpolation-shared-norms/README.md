# Shared norms in the complete interpolation equations

These are **the same three integer polynomials as the pinned interpolation parents**, evaluated with fewer live binary operations. All six source34 coefficients, all unknowns, the unrestricted-integer domains, every zero, and the exact degrees are unchanged.

| Complete equation | Variables | Parent operations | New operations | Exact degree |
|---|---:|---:|---:|---:|
| [integer12_degree4832.json](integer12_degree4832.json) | 12 | 248 | **239** =148M+60A+31S | 4,832 |
| [integer12_degree16000.json](integer12_degree16000.json) | 12 | 223 | **215** =134M+50A+31S | 16,000 |
| [integer13_trace_degree1072.json](integer13_trace_degree1072.json) | 13 | 190 | **184** =114M+38A+32S | 1,072 |

Squaring and multiplication by any fixed scalar count as multiplication. Reuse is free. Counts cover the complete prefix and final norm, with no dead gates. The entire source34 tuple remains live: `beta`, `K0`, `MC`, already shifted `MF`, `cone_A`, and `cone_B`. Their 615,883 raw bytes are pinned and checked; no new large coefficient leaf is introduced. Since the polynomial itself is unchanged, its expanded coefficients and coefficient height are unchanged as well.

This is an ordinary exact circuit optimization. The inherited ordinary native/compiler/refutation calibration stays explicit. Neither the identities nor the finite receipts assert consistency or establish a new Lean/internal-ZFC theorem. No Lean process, frozen H10 emitter, power array, or machine simulation is used. The canonical positive13 page is unaffected.

## Five operations saved in the common norm

Let `u²=D,v²=E`. The first biquadratic square in each parent has equal middle coordinates:

```
(a+h*u+h*v+f*u*v)².
```

Its four coefficients are computed as

```
a²+(D+E)h²+DE f²,
2h(a+E f),
2h(a+D f),
2(af+h²).
```

The parent computes the same expressions with separate repeated products. Reassociate the already needed center term `x²+D+E` as `x²+(D+E)`, so the sum `D+E` is shared. Factor `2h` across both middle coefficients. Together these changes save four operations on each actual whole circuit. The certificate separately checks all changed coefficients; it does not assume a relation among the five radicals.

For the final biquadratic element `a+b*u+c*v+f*u*v`, the old two successive quadratic norms are replaced by the exact polarization

```
H=a²−D b²−E c²+DE f²,
K=af−bc,
Norm=H²−4DE K².
```

The product `DE` is already live in the first square. This saves one further operation. Both evaluations collect to the same eleven-term integer polynomial in the six **free** cut variables. The identity holds over every commutative ring, including all degenerate scales and radicands. No nonzero assumption, rational division, new root choice, or change of witnesses is involved.

## Remaining prefix sharing

All three parents form `q=beta*J+1` and later recompute `q−1` in the transport expression. Reuse the existing `beta*J`. This saves one subtraction in each complete circuit.

The two twelve-variable parents have three further shared computations:

```
Q=Delta*(Delta*I²),
L=u²+Dm+H²,
Q0=L+30H²,
C0=u*(L+2Dm)+H³,
C1=L+2u².
```

The strong product `Delta*I²` is already needed in `Df`. Reusing it saves one multiplication. The three quintic coefficients are pointwise identical to the parent's `Q0,C0,C1`; sharing `L` saves one addition across them. The small literal30 replaces31 inside the factored quadratic coefficient, with the additional `H²` already present in `L`. This does not change a coefficient of the final polynomial.

The product-weight parent also shares `1+c²` between its auxiliary bound and `K=T²+(1+c²)`, saving one more addition. The compact parent has no such auxiliary bound. Thus the whole reductions are nine, eight and six operations, respectively.

## Exact whole-circuit certificate

[build.py](build.py) reads only the inert pinned parent JSON, matches the **complete** old norm against its literal stored gates, and emits each replacement plus a remap for every retained dependency. It imports no inherited builder. The generated [certificates](certificates/) list actual cut indices and output bindings.

[check.py](check.py) independently normalizes each old and new cut expression as a sparse polynomial over the integers. It then verifies every other mapped leaf and gate after operand remapping, rejects any undeclared input to an identity, covers every new node, and binds the final output. This is a finite induction proving equality of the whole stored circuits. The proof does not rely on modular sampling or on a digest used as an algebraic identity test.

The checker also recounts topology/liveness, authenticates all138 unchanged source members, checks all six fixed payloads against prior raw hashes, reproduces all three child JSON files and certificates byte-for-byte, and rejects operation-preserving changes to the final subtraction and the beta leaf. The supplementary96 modular evaluations per whole equation include former `c=0,v=0,s=0,r=0` slices. They are diagnostics only.

The [exact-degree certificate](DEGREE.json) transports the authenticated parent leading witnesses through the proved pointwise identities. The twelve-variable upper bounds are also checked directly from the new gates. For trace13 the syntactic gate bound is1152 because it ignores cancellation; the exact1072 certificate replays only the pinned finite free-polynomial calculation, separately from any inherited emitter. The selected nonzero coefficients remain

```
12/4832:  2^5024*3^3120*beta^2560
12/16000: 2^13056*3^8640*beta^6912
13/1072:  2^976*3^640*beta^480.
```

Their monomials and the exact trace cancellation data are recorded in `DEGREE.json`. No degree decrease is claimed.

Run the complete candidate checks with

```
python3 check.py
python3 -O check.py --output CHECKS_OPTIMIZED.json
```

Both modes pass with the same algebraic, structural, degree and binding results. The only receipt difference is the reported optimization mode. `build.py` regenerates the three equations, three certificates, and `METRICS.json`; it does not touch any original source member. `MANIFEST.json` seals the candidate files, excluding itself.

## Sources and inherited mathematics

The complete 138-member interpolation release is retained unchanged under [source](source/), with its manifests, coefficients, reconstruction recipe,943 tiles, original proofs, report, licenses and notices. [SOURCE_PINS.json](SOURCE_PINS.json) pins every byte and the original arrival archive SHA256 `f44b903de17a70316787ff57562a3d8fe3bdec12791e266318cedb49e7125f72` at arrival commit `85ae4070019efd66ea3e58e9a67d287528094e8b`.

The twelve-integer existence proof is [INTERPOLATION12.md](source/proofs/INTERPOLATION12.md); its strong witness is fixed before selecting the intersective residue. The thirteen-integer proof is [TRACE13_PROOF.md](source/proofs/TRACE13_PROOF.md); its field-trace congruence recovers the cubic odd scale before guard recovery and square extraction. Their ordinary signed native and syntactic calibration dependencies remain attached. The [independent arrival review](../../PROPOSAL_REVIEW_TWELVE_INTERPOLATION.md) and replay receipts distinguish these ordinary unbounded arguments from finite artifact checks.
