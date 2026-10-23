# Independent audit of the round-4 Pell amalgamations

## Verdict and scope

The new arithmetic reductions are mathematically sound, subject to the explicitly inherited authenticated blank-machine compiler, signed Pell/rank lemmas, whole-tuple coefficient transfer, and K215 calibration. No new gap was found in their unbounded root-recovery arguments. The independently recommended integer form is the **sharp 24-variable, 165-operation, degree-2240** form, rather than the valid but dominated degree-2256 variant.

The audit covers the actual positive 12-variable circuits, the pair-ring integer 24-variable circuits with weights 3 and 2, the 25-variable small-weight circuit, and both ordinary/normalized 26-variable two-root circuits. It is not a proof of Con(ZFC), kernel certification, or a global-minimality result. In particular, these observations do not replace the unbounded compiler and arithmetic classification theorems by finite tests.

The source snapshot is `ae3007ca4467011e0e051c84acb4a1dd13971b0e`. Independently recomputed Git blob hashes of the local mathematical source files agree with the source ledger:

- `23-separating12/proofs/ODD_SCALE_27_PROOF.md`: `9db60b97a08f54b790f3b79540edc693e12d9ccb`.
- `20-root12/arithmetic/SMALL_WEIGHT_PROOF.md`: `a47ffb635dda271afe03804c534cf268be450c8c`.
- `20-root12/amalgamation/ROOT12_PROOF.md`: `abb6bb1519bffe77f7f2970f92464ed1f2c76be6`.
- `21-norm12/proofs/NORM12_PROOF.md`: `13508f1065385cef7914270bd81e8fff79888e3b`.

The old commit mentioned inside the odd-scale document is historical text; the audited retrieved blob is the one in the new snapshot.

## 1. Positive twelve-variable construction

Use the author's notation, especially `ell=EkY`, `A=1+ell(ell+k)`, `G=1+Delta*c²`, `I=i*c²`, `D=1+Delta*I²`, `Q=(Delta*I)²`, and `d=Q-1`. Distinguish the circuit register P from the geometric quantity `Pgeom=Dv²+b²`.

### Outer guard and pre-recovery bounds

The trace/product evaluator satisfies

`Trace=2x0`, `Knorm=x0²-4d²W²L²G`, where `x0=d(W²+L²G)`.

Therefore its final norm is `(ur+x0*vr)² modulo 4`. At a product zero the norm guard cannot be -1, so the norm vanishes and `Nk=Nt=epsilon`, with `epsilon=±1`. The inherited weak bootstrap explicitly permits these common signs and the boundary `Cw=0`. Positive h then yields `k=R+epsilon+hE>E`; this step must not be imported into the signed-integer reductions.

The only growth assumptions used by the new positive argument are available here: `q>=16`, `X>=q`, `Y>=q³`, `R<q⁴-2`, `R>1`, `c<2kY`, `a+2<2E`, `D<(a+2)²I²`, `c<I²`, `Y²>20R`, and `kY>8E`.

### Smaller weight and all complex branches

For `M=k(I²+T²)`, direct comparison gives

`2v sqrt(D)<8kEYIT<(1/2)MkY²`,

using `M>=2kIT` and `kY>8E`. Also `b<5RE²I²`, whence

`2b<10RE²I²<(1/2)MkY²`,

using `M>=kI²`, `k>E`, and `Y²>20R`. These estimates are strictly valid without recovered roots.

Separately, `sqrt(G)>(a+1)c` and `sqrt(A)<ell+k` give

`sqrt(G)-sqrt(A)>k(Y²+Y-1)>kY²`,

while `sqrt(A)>ell>kY²`. Thus the auxiliary root bound is smaller than both `M sqrt(A)` and the main/first-root gap.

The complete complex roots of the inner octic have the form `x=M tau+y`, where `tau²=A`, `f²=D`, and `d y²=Q(vf-b)²-1`. The two f branches are real, but y need not initially be real. For either branch, the absolute value of the right-hand side is strictly smaller than `Q(v sqrt(D)+b)²`; if it is negative its absolute value is at most 1, while the upper bound is greater than 1. Consequently every complex root satisfies

`|y|<2(v sqrt(D)+b)` and `|x|<M sqrt(G)`.

Moreover `M²A>4Pgeom` and `d>=Q/2` imply the sufficient strict inequality

`d M²A>2Q Pgeom`.

The stronger constant 4 is unnecessary. It follows that `C(x)=d(x²+M²A)-e>Q Pgeom+1>|Baux|sqrt(D)` for every real x, and in particular x=0 cannot be an inner root.

### Recovery and completeness

With `L=HM+1`, `W=b0+Ht`, an irrational g with `g²=G` would yield two inner roots `(W±Lg)/H`. Their distance is `2L sqrt(G)/H`, contradicting the universal bound `2M sqrt(G)`. Thus g is integral. Positivity of W also excludes the negative g branch.

The rational nonzero x then gives the rational formulas for f and tau with all denominators nonzero; their integral squares make both integers. The auxiliary root y is only rational at this stage. The Pell saturation lemma is required before claiming x integral: with `Q=S²`, integral `V=vf-b`, and `S²V²-(S²-1)y²=1`, that lemma gives integral y. Hence x is integral, and reduction of `W=Lg+Hx` modulo H gives `g=b0 modulo H`, since `L=1 modulo H`. Thus gamma is integral. Finally `g>(a+1)c` and `c>k>E>X` imply gamma>0.

The recovered f sign is handled by changing f,T simultaneously if needed; the exact inherited signed-quotient interface permits signed T without requiring odd i or square w. It must not be confused with the narrower odd-i/square-w integer theorem.

The correct positive completeness coordinate is

`t=M(tau+b0)+L gamma+y=gamma+M g+M tau+y>0`.

Using only `t=M tau+L gamma+y` would not match the new W; the final proof uses the correct formula.

### Norm identity and exact degree

The octic is rewritten as `[zeta²-AA*zeta+constant]²-coef*zeta`, with `zeta=d z²`. Modulo `zeta²-Trace*zeta+Knorm`, this becomes `ur+vr*zeta`. Its quadratic norm is exactly the implemented formula. This identity is valid for repeated roots and zero discriminants and involves no division.

The unique leaders give `deg(He)=134`, `deg(bt)=268`, `deg(ur)=536`. The other final terms have degrees at most 1064 and 1056, below `deg(ur²)=1072`. Therefore `N_top=H_top^16*U_top^8` is nonzero for every beta>0. Adding the nonzero index and transport leaders gives exact product degree 1081. The literal ledgers are 107 operations for the system and 111 for the product.

## 2. Signed 24-variable amalgamation

Six Pos substitutions, odd i, odd s, and square w use 21 unrestricted coordinates; h,T,t bring the total to 24. The Pos map is nonnegative and onto the positive integers by the three-square theorem on `4n-3`. The disjoint substitutions preserve nonzero highest homogeneous forms.

### Pre-bootstrap and degenerate cases

Before excluding w=0 or negative s, let `Z0=|Y|>=q³`. The signs of a,c,H equal that of Y. The inequalities `Delta>q⁴>R`, `|c|>2`, and nonzero odd i imply `D>Delta+|c|`, `Q>2`, and

`1<b=c+RD<Q`.

These statements are valid when w=0 and when T=0. In particular, negative c does not invalidate b's positivity.

Take `W=v²+D+2b`, `P=HW`, `K=P+1`. Every actual conjugate y in the totally real field generated by tau,g satisfies `|y|<W`: use `2|v|sqrt(D)<=v²+D`. For Baux=0, v=0 and `d y²=Qb²-1` gives the bound directly, without division by Baux.

The correct absolute-value estimate is `|K|>=|P|-1>3|P|/4`, not `|K|>|P|-1`; equality holds in the first comparison when P<0. This minor wording error was reported for correction and has no effect on the subsequent strict bounds.

At w=0, tau=±1 is already rational. The strict inequality `|K|sqrt(G)>|P|=|H|W` forces g rational. Saturation then yields integral y, and coprimality `gcd(K,H)=1` yields integral gamma. The main norm reduced modulo H gives 0=1, excluding w=0 without circular use of the positive-w separation.

At w>0, `sqrt(G)<(3/2)sqrt(A)` and `sqrt(A)>8` yield

`|K|sqrt(G)+|P|<(15/8)|P|sqrt(A)+|P|<2|P|sqrt(A)`.

Thus both weights 3P and **2P** separate tau, and then g, using actual field automorphisms. The argument does not assume independent quadratic extensions. Negative H,P,K are handled by absolute values throughout.

Once tau,g are integers, saturation gives integral y in both B branches. The identity `t=m W tau+K gamma+y`, with m=2 or 3, then makes gamma integral. If T=0, `1<b<Q` and integral y contradict `(Q-1)(y²-b²)=b²-1`; therefore the omitted f is recoverable. All source roots and affine congruences are now present before invoking the signed odd-scale theorem.

### Pair-ring norm and sharper exact degree

The inner identity is

`[(C-jroot)²-Zterm]*[(C+jroot)²-Zterm] = (C²-J-Zterm)²-4J*Zterm`,

with `jroot²=J`. Computing this in the g quadratic algebra, followed by `F0²-GF1²`, gives the implemented rank-four norm. Odd coefficients are even, so the norm is a square modulo four for all integer inputs.

For weight 3, the four highest linear coefficients are -3,3,-1,5, giving the valid exact norm degree 2240 and product degree 2256.

For weight **2**, three branches have leaders -2,2,4 times `K_top ell_top`. The fourth leading term cancels, but its next leader is exactly `2K_top k_top Y_top²`, of degree 95 rather than 99. Indeed `ac-ell=E eta+kY²+etaY` has unique highest part kY² of degree 16; `sqrt(G)-ac` has degree at most 9 and `sqrt(A)-ell` at most 2 in the formal homogeneous Laurent expansion. The residual H²e and H⁴Baux²D terms remain strictly lower even in this branch. Therefore

`N_top=2^20 d_top^8 K_top^16 ell_top^12 k_top^4 Y_top^8`,

of degree 2224. The outer degrees 12 and 4 give **2240**. This is a uniform nonvanishing argument, not merely a sampled line degree. Gate count stays 165.

## 3. Signed 25- and 26-variable forms

The retained main norm immediately excludes w=0 and supports a useful rank bootstrap before recovering any eliminated first root. Put `B0=|a+2|`. The main Pell rank cannot be 1 because |c|>1. At rank 2, `c=2(a+2)` for both signs of Y. The positive root gives `g-ac=H+4`, hence `X=4 modulo H`; the negative root gives `4X=-1 modulo H`. The strict bounds `16<=X<|H|` and `0<4X+1<|H|` exclude both. Thus rank is at least 3 and

`|c|>4(X|Y|)²-1`, `k>(7/2)X²|Y|`.

This argument works with negative H and does not assume positive h or already restored tau.

For 25 variables, all small-weight estimates extend with |Y| and |c|. With `M=I²+T²` and lambda=(16/15)^4, one obtains

`(Dv²+b²)/M² < lambda(1/4+4/49) A < (9/20)A`.

Together with `d>=9Q/10`, this gives the strict Caux domination needed to exclude t=0. The T=0 case reconstructs integral tau,y first, then contradicts the b<Q gap. The remaining rational formulas restore integral f,tau,y with no missing denominator branch. The unique leading norm term has degree 872; main/index/transport degrees 32,12,4 give exact degree **920**, at **131 operations**.

For 26 variables, ordinary strong gives `Q0=I²`, and normalized strong gives `Q0=Delta²I²`. The same rank bootstrap yields k>4X and `c²>2ell`, so

`1<A<4ell²<c⁴<=I²<=Q0`.

Consequently t=0 would imply `Q0(A-V²)=A-1`, impossible since `0<A-1<Q0`. Rational tau then has integral square and is integral; y=t-tau is integral. The ordinary negative strong unit is excluded by the explicit mod-four square-residue check, not an unwarranted positivity assertion.

Ordinary completeness needs the source multiplier `i_ordinary=Delta*i_normalized`; canonical Y is even, so Delta is odd and the required odd multiplier remains odd. This point is present in the new proof. The exact degrees are **214 ordinary** and **236 normalized**, both at **123 operations**. The ordinary alternative dominates the normalized one on these two metrics but invokes the corresponding ordinary strong-rank theorem.

## 4. Odd-scale and coefficient dependencies

The newly restored integer relations match the precise six-positive-port, odd-i, odd-s, square-w domain. The source negative-s proof was reviewed, including both main-root signs. The rank congruences recover p=R; the growth bound gives `|Y|>2^R`; the two signs yield `X+2^R=0 modulo H` or `X*2^R=1 modulo H`, each contradicted by its strict no-wrap bound. The sign of c is lost only in congruences explicitly squared, so no unsupported positive-c step is used.

Canonical odd-s completeness uses the exact population identity, not only a congruence of R: `popcount(R)=3t+2`, hence `v2(Y)=3t`, and `s=Y/q³` is odd. The shifted MF convention is essential. Algebraically the packing formula agrees with the circuit only when `MF_source=MF_native+beta`. Complete coherent tuples must be used.

The final logical equivalence remains inherited through the fixed authentic compiler and literal-machine calibration. These new arithmetic arguments do not independently establish those large source theorems.

## 5. Independent executable checks and packaging caveat

`pell_independent_checks.py` was newly authored for this audit and treats all received circuits solely as inert JSON. It uses a quotient-algebra multiplication-matrix determinant as the independent reference for the rank-four norm, rather than executing/importing either author's emitter. It validates DAG references, binary operation ledgers, every-gate/every-port liveness, 250 independent signed/zero identity assignments per file, 250 mod-four checks per file, and two exact finite-field affine line degrees. Ten circuits pass, including the three final integer comparison systems. The systems were also checked gate-by-gate against their corresponding audited product circuits; their residual degrees are (12,4,2224), (32,12,4,872), and (32,12,4,38,128), at 161,126,117 operations respectively. The file `pell_independent_checks.json` records frozen SHA-256 hashes and complete results.

`pell_bound_checks.py` adds 600 exact-integer positive-gap fixtures and 1920 signed weight-two fixtures, including negative s,H,P, both i signs, w=0, and T=0. No floating-point square roots are used. These tests supplement the preceding unbounded arguments and are not their substitutes.

Packaging note: the final release uses one shared compact-coefficient directory. All active positive, integer and nine-variable bindings resolve within the archive and their exact payload hashes are checked before replay.
