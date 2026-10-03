# Paid mass-coordinate circuits for fixed-horizon three-mass certificates

A natural-coordinate change gives a complete arithmetic saving in actual emitted source certificates while preserving their unique natural zero fibers. Replace each branch's offset `u` by a natural mass coordinate `v=e+u`. The inverse `u=v−e` is natural on complete natural zeros, as proved below. The ordinary raw input `N0=x+1`, selector/control/value equations, requested outputs, and polynomial finalizer remain paid.

For the concrete reversible `INC2; DEC2` source at external horizon two, the best emitted old circuit costs **60 operations**, and the new one costs **56**. The compact exact-target certificate with its cleaned physical-time output also costs **60→56**. A three-increment chain gives **116→107** for native final-value/time outputs and **114→105** for the compact cleaned target/time certificate. These compare complete literal circuits, not just changed rows. The comparison is against the explicitly emitted schedules, not an optimality result. A zero-test fixture ties its best old schedule.

The [standard-library checker](three_mass_arithmetic.py) and [deterministic receipt](three_mass_arithmetic.json) include literal complete circuit sources and original exported affine/product certificates for six representative fixtures. They reproduce all counted forms from pinned Git archives. This is an externally bounded compiler improvement, **not a fixed-arity universal bound**. The witness count remains `2Bh`; no unknown horizon is packed and no unbounded counter encoder is supplied.

## Actual source and domains

Both inputs come from immutable commit `4e270aa4648c5fd7e18626507531046715976535`:

The exact archive pins are:

- `Three_Mass_Reversible_Computation.zip`: `fd86a8a6b71735ef08ebd7913498603213244484da8b23d81876b10c40ffd1de`.
- `Exact_Targets_Three_Mass_Units.zip`: `d69d8df9ee3a2074bcff1ef400853724eafb679ada8b287ef397eb8891965dcc`.

The executed native `code/certificate.py` has SHA-256 `fed96578694af665258fca9eeab14fa94d8a56e810de8f684a2c9fdcd9d751e8`; the exact-target `clean_targets.py` has SHA-256 `a79405023df5a1038a69bc947314979093df39be8da7abcdf5588f77da848315`. The vendored native certificate source is checked byte-identical. The checker authenticates archives and these source bytes before executing them in temporarily isolated module namespaces; it restores prior `sys.modules` objects and `sys.path`. It neither uses warm bytecode nor runs either full author suite.

The mathematical input is the reviewed deterministic separated reversible source, with no outgoing halt instruction. Its raw positive integer need not be `2,3`-smooth. Here the ordinary external coordinate is **natural** `x`, and the explicitly computed raw value is `N0=x+1`. The horizon `h` and finite branch table are compiler parameters. All selector, old-offset and new-mass witnesses are natural numbers, including zero. Optional `y` and `T` are natural endpoint coordinates, not free unverified values.

The full theorem/API audit remains the [three-mass review](review_batch80_three_mass.md). This note changes the arithmetic representation of that proved finite-horizon relation; it does not repeat the CA universality or radius-reduction proofs.

## Exact substitution and natural-zero bijection

For every step and branch, put

\[
v_{tj}=e_{tj}+u_{tj},\qquad u_{tj}=v_{tj}-e_{tj}.
\]

Let `F` denote the complete original polynomial, including all supplied input/output/time conditions. Define

\[
\widetilde F(x,e,v,y,T)=F(x,e,v-e,y,T).
\]

This is an exact polynomial identity under the displayed substitution over integers, rationals and reals. It is not equality at the same coordinate tuple. Both directions are integer affine coordinate maps. Their natural-domain behavior needs a separate proof: the inverse is not natural on the whole natural orthant.

Write `E_t=Σ_j e_tj`. The old inactive summand becomes

\[
(E_t-e_{tj})v_{tj}.
\]

It is nonnegative for every supplied natural tuple. All other terms remain squares of affine forms. Thus a natural zero still forces every square and inactive product to vanish. `E_t=1` gives exactly one selector equal to one and all others zero. Every inactive `v` then vanishes.

For a selected branch, the actual source forms after substitution are:

| Branch | Old raw value | New raw value |
|---|---|---|
| Increment at `p` | `v` | `p v` |
| Decrement at `p` | `p v` | `v` |
| Positive test at `p` | `p v` | `p v` |
| Zero test, residue `1≤r<p` | `p v+r−p` | `p v+r−p` |
| No-op | `v` | `v` |

Start with `N0=x+1>0`. The value equation identifies the selected old form with the preceding positive raw value. At `v=0`, that form is zero or, for a zero test, strictly negative. Natural integrality therefore forces the selected `v≥1`. Consequently `u=v−1≥0`. The new raw value is positive in every row, so induction applies at the next step. Inactive coordinates restore `u=v−e=0`.

This proves that every complete new natural zero restores an old natural zero, with identical input, state history, output and time. Conversely every old natural zero gives a new one by `v=e+u`. The two maps are inverse, so witness uniqueness is preserved. No side inequality, divisibility oracle or quotient operation is hidden in the new circuit.

For `h=0`, there are no transformed core coordinates and the map is the identity. If `B=0` and `h>0`, each one-hot row is the nonzero constant `−1`, so there is no zero. Missing guards or a premature halt similarly produce no zero by the unchanged control/value conditions. The proof covers arbitrary positive raw cofactors.

This is a reparameterization of the offsets, not elimination of a scalar witness: both old and new cores have `2Bh` natural witnesses. Its value is that a mass coordinate can replace a previously paid `e+u` addition without losing the natural witness contract.

## Factoring the inactive products

For any integer tuple, independently of the zero-set proof,

\[
\sum_j(E-e_j)v_j
 =E\left(\sum_jv_j\right)-\sum_j e_jv_j.
\]

This identity preserves the **entire** polynomial for a fixed coordinate convention. Its right-hand subtraction must not be interpreted as a replacement nonnegativity theorem: nonnegativity follows from equality with the left side.

Factoring is useful only when its sums are shared or cheap. With `B≥3`, if `E` and `S=Σv_j` already exist, the literal direct subcircuit using `E−e_j` costs `B M+(2B−1) A`; the factored subcircuit costs `(B+1) M+B A`. It replaces one multiplication's worth of additions for a net saving `B−2` per step in this schedule. If `S` must be newly computed, its `B−1` additions erase that advantage and make factoring one operation worse. Existing subexpression sharing can alter either tally, so the final DAG is always counted after emission and dead-code removal.

For `B=2`, direct left factors are simply the other selector and require no subtraction. The factored circuit is worse in the worked two-branch fixtures. For `B=1`, the inactive sum vanishes. The emitted comparison handles these boundaries rather than extrapolating the `B≥3` formula.

Every tested matched offset/mass schedule removes exactly `Bh` live additions and leaves its multiplication count unchanged: the offset version computes `v=e+u` internally and uses the identical downstream circuit. A separate emitter compiles the original sparse affine forms directly; it can sometimes avoid those additions without changing coordinates. The prime-three zero-test case below demonstrates why `Bh` is a matched-schedule statement rather than an unconditional improvement over every old evaluator.

## Complete source and fair ledgers

Each arithmetic operation is one `+`, `−`, or `*`; subtraction counts as an addition. Multiplication by a fixed nonunit coefficient is charged. Literal constant arithmetic and multiplication by zero or one are folded. Equal coefficient groups and identical affine ports share work, identical DAG operations are reused, and unreachable gates are removed. Constant bit lengths and integer bit-operation costs are not this operation metric.

The loader computes `N0=x+1` with one addition, and all appearances of `x` in the certificate use that port. This includes the cleaned clock's `192N0` term. Affine forms are not treated as free gates. All squares, inactive products, additions into the final scalar output, source-state weights, final value and requested physical time are included.

For each certificate the checker emits six schedules: original sparse-affine, shared offset, and new mass coordinates, each with direct or factored inactivity. The old column below is the minimum of the four **actually emitted old-coordinate** schedules; the new column is the minimum of its two mass schedules. No claim is made that these exhaust possible SLPs or that one cannot specialize a small known path further.

| Actual fixture | `B,h` | Endpoint interface | Best emitted old | Best emitted new |
|---|---:|---|---:|---:|
| `INC2; DEC2` | 2,2 | Native `y,T` | 21M+39A=60 | 21M+35A=56 |
| `INC2; DEC2` | 2,2 | Compact cleaned `T` | 22M+38A=60 | 22M+34A=56 |
| Three `INC2` steps | 3,3 | Native `y,T` | 38M+78A=116 | 38M+69A=107 |
| Three `INC2` steps | 3,3 | Compact cleaned `T` | 38M+76A=114 | 38M+67A=105 |
| Prime-three zero test | 2,1 | Native `y,T` | 11M+19A=30 | 11M+19A=30 |
| Already halted, empty source | 0,0 | Compact cleaned `T` | 2M+3A=5 | 2M+3A=5 |

The native rows have `2Bh` witnesses plus `x,y,T`; the cleaned rows have `2Bh` witnesses plus `x,T`. The underlying source certificate has `3h+1` affine-square slots and `Bh` inactive-product slots before trivial simplifications. Native endpoint export adds two squares, cleaned time export one. The `B,h` slot ledger alone cannot determine a complete operation count: state codes, primes, clock coefficients, equal coefficient groups and optional endpoints affect affine evaluation and sharing. The receipt therefore supplies exact complete sources, not an operation total inferred from slot counts.

For the two-step example, abbreviate `e_t0=a_t`, `e_t1=b_t`, `v_t0=c_t`, `v_t1=d_t`. The mass polynomial with native outputs is literally

\[
\begin{aligned}
 &(a_0+b_0-1)^2+b_0^2+(c_0+2d_0-x-1)^2\\
+{}&(a_1+b_1-1)^2+(b_1-a_0-2b_0)^2
 +(c_1+2d_1-2c_0-d_0)^2\\
+{}&(a_1+2b_1-2)^2+(2c_1+d_1-y)^2\\
+{}&\left(300(c_0+d_0+c_1+d_1)+8(a_0+b_0+a_1+b_1)-T\right)^2\\
+{}&b_0c_0+a_0d_0+b_1c_1+a_1d_1.
\end{aligned}
\]

The 56-operation DAG in the receipt evaluates this entire expression. In the compact cleaned variant, remove the `y` square and replace the time square's argument by

\[
600(c_0+d_0+c_1+d_1)+16(a_0+b_0+a_1+b_1)
 +192(2c_1+d_1)+192(x+1)+16-T.
\]

That complete DAG also has 56 operations, with the different M/A split shown above. All 228 emitted forms are exactly degree two, verified by their nonzero complete coefficient expansions, not only a formal degree upper bound.

## Exact-target lift and boundaries

The compact cleanup theorem witnesses the forward source and reconstructs the unique cleaned run. Compose its existing affine zero-fiber lift with `u=v−e`: the original forward `(e,u)` coordinates are copied to forward and reverse slots; the two bridge selectors are one, with offsets `Nh−1` and `N0−1`. These offsets are natural on zero fibers by the positivity induction. If the full cleaned certificate is also written in mass coordinates, its copied pairs are `(e,v)` and its bridge masses are simply `Nh,N0`.

No extra reverse witness is quantified in the compact polynomial. This use of the proved cleanup theorem is not a claim of off-zero equality with the full cleaned polynomial or a globally natural affine lift. The checker evaluates the actual supplied `affine_full_witness_lift` at 54 complete natural zeros and checks the complete full certificate and all restored coordinates.

A worked complete fixture uses `x=4`, hence `N0=5`, and `INC2; DEC2` at horizon two. The selected mass coordinates are `c0=5,d1=5`, with `a0=b1=1`; all other core coordinates are zero. The final raw value is five, native time is 3016, and cleaned time is 7968. Both full compact polynomials vanish; the receipt records both complete old and new assignments.

Integrality is essential. For the prime-three zero-test packet at `N0=1`, select residue two and set `v=2/3`: the transformed nonnegative-rational polynomial has a zero, but its restored offset is `−1/3`. More directly, one prime-two decrement at `N0=1` admits `e=1,v=1/2,y=1/2,T=158` as a rational/real zero, while the intended natural guard is false and the restored offset is `−1/2`. Neither fixture is a natural-domain counterexample. They preclude upgrading this coordinate bijection to arbitrary nonnegative rational/real fibers.

## Evidence and remaining obligations

The source-pinned replay checks:

- All eleven literal residue-expanded branch/tick triples after substitution, including both primes and every operation.
- 228 complete symbolic circuit-to-polynomial coefficient equalities across 38 source/cleaned certificates, plus 2280 signed full-output comparisons.
- 76 matched `Bh` addition-saving comparisons and all literal live DAG ledgers.
- 648 complete natural-zero source evaluations, 54 actual compact-to-full cleaned lifts, and 120 rejected horizon/guard fixtures.
- 3264 nonnegative core tuples with affine endpoints supplied from the actual source forms; all eleven enumerated zeros restore natural offsets. The scope is the stated finite boxes, not exhaustive verification of the theorem.
- The explicit natural fixture, both rational boundaries, `h=0`, `B=0`, one-branch cases, and source horizons before/after first halt.

The mathematical proof supplies the all-input zero-fiber statement; finite tests do not replace it. The primitive arithmetic and paired full symbolic coefficient comparisons establish the stated source identities independently of numerical sampling. The producer's full historical suites were not rerun. `emit`/`evaluate` are research algebra routines used with freshly generated authenticated certificates, not public hostile-packet validators; the original intended checker contract is unchanged. An explicit prototype guard permits only free raw input named `x`, native free output/time named `y,T`, or compact-clean free time named `T`. Five valid producer packets outside this interface are rejected, including no-endpoint `h=0` and names that could collide with internal registers or mass renaming. This deliberate restriction keeps the paid loader port and naming claims accurate; it is not a general hygienic replacement for the original compiler.

Reproduce using the pinned Git objects:

```sh
python three_mass_arithmetic.py --repo /path/to/Proofs \
  --expect three_mass_arithmetic.json
```

`--output PATH` writes a deterministic receipt; comparison is recursively type-sensitive. No repository or archive is modified. The free raw integer remains a valuation-coded source input, not an automatically solved ordinary-counter loader. A universal finite table, paid unbounded input decoding and a fixed-arity unbounded-history representation remain separate obligations. The examples here do not establish a new universal operation count.

## Independent review

The separate [mathematical review](review_three_mass_mass_coordinate_math.md) checked the complete natural-zero induction, empty boundaries, raw cofactors, real-domain limitation, and composition with the clean reverse lift against the literal pinned producers. Its independent finite checker compared all eleven primitive triples and 10,080 complete natural tuples.

A subsequent [independent circuit review](review_three_mass_arithmetic.md) reconstructed the actual 38 certificates and expanded all 228 emitted circuits with separate coefficient arithmetic: all whole-polynomial identities, 1686 residual ports, 372 inactive sums, 13,704 live paid gates and 76 matched `Bh` savings agreed. It additionally checked twelve native/clean scale-four identities and all five explicitly unsupported interfaces. The source/receipt pins were `d5607c6c…` and `e13858da…`; its fresh saved-receipt replay passed. Root separately read the complete arithmetic proof/source and replayed the construction. No arithmetic edit was requested; the only requested boundary refinement was the explicit prototype-interface guard described above.
