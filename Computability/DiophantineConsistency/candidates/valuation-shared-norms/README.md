# Two complete twelve-integer circuits with shared norms

These are **pointwise identical** to the accepted valuation-separated parents, with seven fewer live binary operations each. The whole source34 tuple, integer domain, twelve unknowns, every zero and all expanded coefficients remain unchanged.

| Complete equation | Parent operations | New operations | Exact degree |
|---|---:|---:|---:|
| [integer12_degree2400.json](integer12_degree2400.json) | 215 | **208** =134M+42A+32S | **2,400** |
| [integer12_degree2912.json](integer12_degree2912.json) | 209 | **202** =128M+42A+32S | **2,912** |

Squaring and multiplication by fixed scalars are charged. Reuse and the six specified constant leaves are free, as in the parents. Every declared coordinate, constant leaf and operation is live. This is a complete-circuit count, including all denominator clearing and the final norm.

The comparison is against the original `215/2400` and `209/2912` files in `ConZFC_Valuation_and_Signed_Certificates_2026-10-23.zip`, SHA256 `11267f89709f1bb10ba1237d29733727d9c41cebd783041419eb0773e6e7f937`. Those ordinary reductions were independently reviewed and accepted at commit `d946ae6618`. Both new points also dominate the earlier twelve-integer interpolation operation/degree points. The separate thirteen-integer `184/1072` form retains a tradeoff with one more variable.

This packet adds exact arithmetic identities and finite certificates. Its inherited ordinary consistency equivalence is unchanged. It neither proves consistency nor adds a Lean/internal-ZFC endpoint. Lean remains paused. The canonical positive-integer PDF is unaffected.

## The seven saved operations

The same five norm identities used in [interpolation-shared-norms](../interpolation-shared-norms/) transfer without changing their hypotheses. In the first biquadratic square, the middle two coordinates are equal. For `u²=D,v²=E`, write them as

```
(a+h*u+h*v+f*u*v)².
```

Compute its scalar and two middle coefficients as

```
a²+(D+E)h²+DE f²,
2h(a+Ef),
2h(a+Df).
```

The fourth coefficient `2(af+h²)` is unchanged. Share `D+E` with the reassociated existing term `x²+(D+E)` and share `2h` across both middle coefficients. This saves four operations on each actual full circuit.

The final biquadratic norm uses the exact polarization

```
H=a²−D b²−E c²+DE f²,
K=af−bc,
Norm=H²−4DE K².
```

Its product `DE` is already live. This saves one more operation. Both forms expand to the same eleven-term integer polynomial in the six free cut variables.

Two prefix identities account for the remaining savings:

```
q−1 = beta*J,             where q=beta*J+1,
Q = Delta*(Delta*I²).     The inner product is already used by Df.
```

They remove one subtraction and one multiplication. No variable is shifted, no sign chart is changed, and no extra coefficient leaf or positivity premise is introduced. All identities hold over every commutative ring, including zero or negative values of any displayed intermediate expression.

## Exact proof for the entire stored circuits

[build.py](build.py) reads only the inert parent JSON. It matches the **complete** stored norm, then emits seven acyclic replacements and a dependency remap. No original builder or emitter is executed. The two [certificates](certificates/) bind the exact parent and child hashes, cut indices, retained nodes and output.

[check.py](check.py) uses the pinned copy of the independent [exact cut checker](common/check_engine.py). It collects each changed expression as a sparse integer polynomial in its free cuts. Every other mapped leaf and gate must agree after operand remapping; every new node is covered and the final output is bound. Undeclared inputs in a cut identity are rejected. Thus the proof covers the complete polynomial, not only a finalizer formula or sampled evaluations.

The rational child has 238 live nodes and the integral child 232. Both have exactly seven verified cut identities. The checker also authenticates all 120 unchanged parent-subtree files, all six actual coefficient payloads, all fixed binding paths, the complete operation census, and byte-identical deterministic regeneration. It rejects operation-preserving changes to the final subtraction and beta leaf, and a false leading-coefficient claim. The extra96 modular comparisons per child, including zero-multiplier slices, are supplementary diagnostics.

The coefficients are the original coherent source34 values: `beta=2^1064921−1`, `K0`, `MC`, **already shifted** `MF`, `cone_A=2^1113`, `cone_B=2^666104`. All six remain live, and all 615,883 minimal raw bytes agree with the previously reviewed tuple. Expanded coefficient height is unchanged because the entire polynomial is unchanged.

## Exact degree from the actual child gates

In addition to transporting the parent proof through pointwise equality, [leading.py](leading.py) proves the leading monomial directly from **each actual stored child**. Its coefficient domain is the polynomial ring in the six formal ports over the integers. It uses graded lexicographic order on the twelve unknowns, with `T` first.

At a multiplication, it multiplies exact coefficient polynomials and adds unknown exponents. At an addition or subtraction, it chooses the larger monomial or combines equal leading coefficients exactly. If that combination cancels, the certificate fails rather than guessing a lower term. Neither child needs such a fallback: the exact leading calculation succeeds at every gate. This is an induction over the actual arithmetic DAG, not a generic degree field read from metadata.

The resulting attained coefficients are

```
[j^1152 w^288 v^288 s^160 r^160 c^320 T^32] P2400
    =2^2400*3^1440*beta^1152,

[j^1408 w^352 v^352 s^192 r^192 c^384 T^32] P2912
    =2^2848*3^1760*beta^1408.
```

They are positive at the authentic beta. The generic exact degrees therefore survive specialization of all six ports. The computation stores beta powers symbolically, so no enormous expanded numeral or final polynomial is materialized. The largest exact scalar in the leading certificate is only 5,638 bits. [DEGREE.json](DEGREE.json) records the actual monomials, factorizations, scalar digests and per-gate noncancellation result. The separate syntactic gate upper bounds agree with 2400 and2912.

## Reproduce and provenance

Run:

```
python3 check.py
python3 -O check.py --output CHECKS_OPTIMIZED.json
```

Both modes pass with identical identity, degree, count, liveness, binding and negative-control results. Only the reported Python mode differs. [CHECKS.json](CHECKS.json) and [CHECKS_OPTIMIZED.json](CHECKS_OPTIMIZED.json) retain the evidence. `build.py` regenerates both complete equations, both certificates, `METRICS.json` and `DEGREE.json`. It never changes a parent source. `MANIFEST.json` seals all candidate files except itself.

The complete 120-file `integer12/` component is copied unchanged under [source](source/), including its own helpers, both originals, coefficient payloads/reconstruction recipe, inherited root-fusion package, source34 native proofs, full-residue interpolation proof and independent audits. Its unbounded arithmetic proof is [PRIME_TWELVE.md](source/proofs/PRIME_TWELVE.md). The original root license and notice are preserved as [LICENSE.PARENT](LICENSE.PARENT) and [NOTICE.PARENT.md](NOTICE.PARENT.md). The unrelated direct quartic and positive 98 components are not copied or claimed here.

[SOURCE_PINS.json](SOURCE_PINS.json) pins this exact subtree and the unchanged generic proof helpers from the preceding shared-norm checkpoint. It identifies the immutable accepted review commit rather than depending on a mutable common review document. All original attribution and proof boundaries remain attached. The [scoped arrival review](../../PROPOSAL_REVIEW_VALUATION_INTEGER12.md) distinguishes the ordinary unbounded calibration from finite replay evidence.

For repository integration, note that `source/inherited/root_fusion/verification/LATEX_BUILD.log` is an intentional pinned inherited file despite the repository's generic log ignore rule. A clean checkout must contain it for the sealed 120-member inventory to pass.
