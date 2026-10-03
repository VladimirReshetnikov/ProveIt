# Independent review of the whole native-fiber classification

Date: 2026-10-03. **Result: PASS for the classification, exact height, and finite counting statements in THEOREM.md §§1–5**, with the theorem's stated dependence on the pinned native soundness and positive-completeness results. The uniform asymptotic in §6 has a separate reviewer and is not certified by this report.

This review includes the strengthened height statement in the revision read at 11:20 UTC: the maximum of all twenty-two supplied coordinates is exactly `y_aux`, without a fixed-coordinate plateau. No mathematical correction is required in the reviewed statements.

## 1. Scope and independent source checks

I read the local pinned selector theorem, prescribed-scale interface, relaxed auxiliary proof, fixed-minus parity proof, odd-index construction, DEPENDENCY-AUDIT.md, and the earlier fixed-slice theorem. In particular, I checked the proof inside PELL_RELAXED_AUXILIARY_PROOF.md, rather than treating the abbreviated `c|m` sentence in the selector as if it also stated `p|m`.

I independently parsed the frozen native_blocks.json as data and symbolically evaluated its gates. I did not import or execute upstream author code or the existing audit script. Each of the four fixtures has twenty-two distinct supplied coordinates and sixty-four acyclic gates. Exactly comparisons 12, 13, and 14 involve `f,i,j,o,y_aux`; their exact residuals are

- `(ic²)² − Δ(f²−1)`
- `(ic²)²((jc−p)²−y²) − (1−y²)`
- `jc−p−(of−c)`

All other thirteen comparisons have no dependence on those five coordinates. This independently agrees with the dependency audit. The finite JSON fixtures validate the literal identities; the general valid-port projection and positive domain are supplied by the pinned interface theorem, not inferred from the fixture sample.

## 2. The seventeen-coordinate forcing is universal

The padded input comparisons and checksum uniquely give the three displayed field formulas. In particular,

`F0 = 16(P−H−Mport+Z)−15 ≥ 1`

because `H+Mport−Z = H OR Mport < P`. The other two fields are positive, and all four padded fields are below `q=16P`. The packing relation then fixes `r`.

The selector's forward soundness, before choosing any converse witness, fixes `p=2r+1`, `X=2^p`, the displayed rounded binomial value `Y`, the main pair `(c,d)`, and `k=ψ_B(r+1)`. Thus `w,s,a,c,d,k` are fixed. The remaining quotient/difference formulas uniquely recover `h,eta,zeta,ga,odd_half,bound_beta`. The first norm and positivity uniquely give `2tau+1=χ_B(r+1)`, so `tau` is fixed as well.

Integrality and strict positivity of these unique values legitimately follow from the pinned positive-completeness theorem for the same valid ports. This use of one existing positive extension does not restrict which values of the remaining auxiliary indices can later be adjoined.

The names in the claimed fixed list number exactly seventeen. The other five really can vary: `f` and `i` strictly increase along the permitted main indices, while at a fixed main index the infinite normalized-index families make `j,o,y_aux` strictly increase. Thus the claim is stronger than merely identifying seventeen potentially fixed names.

## 3. The relaxed-norm rank proof applies at A=a+2

The historical paper first establishes its size hypotheses with `A=a+4`, but its subsequent rank argument uses only

`A≥2`, `Δ=A²−1`, `c=ψ_A(p)`, `c>AΔ²`, and `c²|R`, `R²=Δ(f²−1)`.

The native selector explicitly establishes the same size bound with `A=a+2`; no use of the historical defining equation for `a` remains in the rank lemma. Here is the critical argument with the dependence exposed.

Write `Δ=d0 s0²` with `d0>1` squarefree, and let `F+y0√d0` be the fundamental positive norm-one unit with integer coefficients. For some `e≥1`,

`A=χ_F(e)`, `S=ψ_F(e)`, `s0=y0S`, `Δ=(F²−1)S²`.

The relaxed norm first gives an integer-coefficient Pell solution in this field: `s0|R`, and then squarefreeness gives `d0|(R/s0)`. Therefore, for some `v>0`,

`f=χ_F(v)`, `R=Tψ_F(v)`, where `T=(F²−1)S=Δ/S`.

Also `ψ_F(ep)=Sc`. With `b=gcd(v,ep)` and strong divisibility of `ψ_F`, put `h=ψ_F(b)`. The divisibility `c²|Tψ_F(v)` gives

`c ≤ gcd(c²,Tψ_F(ep)) = c gcd(c,Δ) ≤ T h`,

and hence `h≥c/T≥c/Δ`. If `b<ep`, then `2b≤ep`; doubling and `S<A` give

`2h² < ψ_F(2b) ≤ ψ_F(ep)=Sc < Ac`.

But `c>AΔ²` gives `h²≥c²/Δ²>Ac`, a contradiction. Consequently `ep|v`. Writing `v=em` proves simultaneously

`p|m`, `f=χ_A(m)`, `R=Δψ_A(m)`.

This genuinely excludes solutions in a larger quadratic order that would have been admitted by the isolated relaxed norm. It does not assume `c|m` or a canonical auxiliary index, and it does not claim the false stronger implication `c²|ψ_A(m)`.

## 4. The exact main-index progression has both directions

Once `m=pk`, expansion in the original Pell sequence gives

`ψ_A(pk)/c ≡ k d^(k−1) (mod c)`.

Since `gcd(d,c)=1`, cancellation is valid and

`c²|Δψ_A(pk) ⇔ c|Δk ⇔ c/g|k`, with `g=gcd(c,Δ)`.

This is an equivalence, including the converse: there is no missing extra `p|m` condition, since every constructed `m=(pc/g)l` is already a multiple of `p`.

The binomial expansion modulo `Δ` gives `c≡pA^(p−1) (mod Δ)`, and `gcd(A,Δ)=1`; thus `g=gcd(p,Δ)` and `g|p`. Consequently `M0=pc/g` is an integer multiple of `c`, and every permitted `m` satisfies

`p|m`, `c|m`, `m≥c>2p`, `f=χ_A(m)>χ_A(2p)>2c`.

For every such `m`, `R/c²` is a positive integer and the first varying comparison holds exactly. In particular, no evenness assumption on `m` or oddness assumption on `f` has entered; those properties of some canonical constructions are unnecessary here.

## 5. The normalized-index classification is exact for every allowed m

For an arbitrary permitted `m`, the positive norm becomes

`(RU)²−(R²−1)y²=1`, with `U=jc−p≥c−p>0`.

The integer-coefficient Pell classification at base `R` is applicable even if `R²−1` is not squarefree: `R+√(R²−1)` is the least positive integer-coefficient norm-one unit. It yields a unique positive index `n`. Reduction modulo `R` excludes even `n`, so `U=χ_R(n)/R` is a positive integer.

The two polynomial congruences in the theorem and pinned parity proof hold because `c|R` and `R²≡1−A² (mod f)`. Squaring the `f`-congruence gives the plus-sign chi step-down at comparison index `2p<m`. It is essential here that the step-down conclusion is modulo `4m`, before dividing the integer equality by two. The result is

`n=e p+2mt`, `e∈{1,−1}`.

The two original, unsquared congruences give parity conditions differing by exactly `t`. Since `c>2p` and `f>2c`, opposite signs cannot coincide in either modulus. Thus `t` is even and the native `p` is `3 mod 4`. Necessity is exactly `n≡±p (mod 4m)`.

Conversely, for every positive `n=e p+4mk`, the identities give

`ψ_A(n)≡e c (mod f)`, `n≡e p (mod c)`, and `(-1)^((n−1)/2)e=-1`.

They recover both original minus congruences. Therefore `(U+p)/c` and `(U+c)/f` are positive integers, and the normalized norm holds identically. In particular, the baseline `n=p` works for every permitted `m`, including the minimal `M0`; it does not rely on extending the canonical construction by an unsupported extrapolation.

The remaining thirteen residuals stay zero, proving that these auxiliary tuples give full native witnesses. The residues have distinct least positive representatives `p` and `4m−p`, since `0<p<2m`. Strict increase of `χ_A(m)` and of `ψ_R(n)` proves injectivity and excludes double counting.

## 6. Strengthened exact height: every fixed coordinate is below y

The revised theorem correctly strengthens the initial `max(C,y)` formula to `height=y` for the actual native tuple.

The native bounds give `q<r<X<a<A<c`. Therefore all fixed coordinates other than `c,d,tau` are strictly below `c`, using the displayed quotient formulas; specifically `k<c/Y`, `h<k`, `eta<c`, `zeta<k`, and

`ga<d/(4a+3)<Ac/(4a+3)<c`.

The main norm gives `d²=Δc²+1<A²c²`, since `c>1`; hence `d<Ac<c²`. For the only other potentially large fixed coordinate, write `E=XY`. As `X<2E+1` and `E+1<A=E+Y+2`,

`tau²<tau(tau+1)=(E²+X)(Yk)²<(E+1)²(Yk)²`,

so `tau<(E+1)Yk<(E+1)c<Ac<c²`. Thus every one of the seventeen fixed supplied coordinates is strictly below `c²`.

For the five varying coordinates, `R²=Δ(f²−1)>f²`, `i=R/c²≤R`, and `n≥p≥3` imply

`y≥ψ_R(3)=4R²−1>R≥c²`.

The norm gives `0<U≤y`; the inequalities `c>p` and `f>c` imply `j≤y` and `o≤y` exactly as in the theorem. Hence `y` dominates all twenty-two supplied coordinates. There is no overlooked fixed-coordinate cutoff or native plateau. A plateau would require additional fixed coordinates outside this native tuple or an independently imposed height cutoff.

## 7. Exact finite counting

For fixed `m`, the sinh formula is strictly increasing in `n` and gives the exact inverse cutoff `n≤floor(t_m(H))`. The two arithmetic progressions have the stated floor counts, including the baseline endpoint and the gap before `4m−p`. Replacing `floor(t)` by `t` inside either displayed floor is valid because the added constants and denominator are integers.

The least admissible normalized index is `p`; its height strictly increases with `m` and tends to infinity. Thus precisely the main indices `m=M0l` with `1≤l≤L_H` contribute, and the sum is finite. For `H<1` no positive supplied tuple contributes. The floor formula remains valid for every real `H≥1`, including values below the first tuple height, where the sum is empty.

## 8. Supplemental independent arithmetic checks

These checks use independently written local arithmetic, not upstream author code, and are secondary evidence only.

- Exact reconstruction of eighteen auxiliary tuples passed for `(A,p)=(2,3),(3,3),(4,3)`, `m=M0` and `2M0`, and `n=p,4m−p,4m+p`. The checks verified the `c²` divisibility, all three varying equations, positive integral reconstruction, and domination of all five varying coordinates by `y`. The examples include `g=1` and `g=3`, odd and even `m`, and even `f` at odd `m` for even `A`. These small examples are checks of the auxiliary identities and sufficiency; they are not native-port examples and are not offered as instances of the large-main-index bootstrap.
- A separate modular rank check used the genuine nontrivial suborder `A=7=χ_2(2)`, `p=5`, `c=37829`, `Δ=48`, with `c>AΔ²`. Here `e=2`, `T=12`, and `M0=189145`. Among `1≤v≤756580`, the only indices with `c²|Tψ_2(v)` were `v=378290` and `756580`, exactly `eM0` and `2eM0`. This specifically exercises the integrality-recovery issue hidden by cases with `e=1`; the rank argument itself does not require native parity `p≡3 mod 4`.

## 9. Evidence boundary

The universal conclusions above are deductions from the checked identities and the explicitly inherited native soundness/completeness theorem. No complete astronomical native witness was constructed. No frozen report, pinned source, or public artifact was modified. The review makes no claim of full native-tuple materialization.

Reviewed THEOREM.md SHA-256: `69e48661aa36c1c1eba68d824ecdb3d424440dfa12ad5438d41334934dca225e`.
