---
title: "Smaller explicit Diophantine forms for Con(ZFC)"
subtitle: "A pinned comparison and four complementary syntheses"
author: "Mathematical synthesis and independent arithmetic audits"
date: "23 October 2026"
---

# Executive conclusion

There is a genuine improvement, but not a single meaningful winner under every definition of “simplest.” The strongest recommendations are:

- For a short, directly readable equation: the new 12-positive-variable polynomial, with 111 binary arithmetic operations and exact degree 1081. It improves the earlier 139-operation, degree-1257 form on both measures, without adding variables.
- For few unrestricted integer unknowns: the new 24-integer polynomial, with 165 operations and degree 2240. The 25-integer and 26-integer alternatives have much lower degrees.
- For low degree and transparent equations: the new system of 22 quadratics in 31 positive variables, or its single quartic sum of squares. This removes one variable and one equation from the previous 32-variable quartic.
- For the fewest unknowns among the explicit constructions reviewed: a new specialization in nine nonnegative unknowns, with 1840 live binary operations and exact degree $120724\cdot5^{32}+366$. Its degree remains enormous, and most of its fixed coefficients are specified by bounded finite recipes rather than written out.

Each recommendation is a fixed ordinary integer polynomial, or a finite system of such polynomials, after the stated coefficient binding. All displayed auxiliary expressions are arithmetic registers unless explicitly listed as supplied variables. In particular, neither the norm notation nor an enormous fixed exponent hides extra quantified variables or an exponential Diophantine equation.

The logical conclusion is

$$\mathsf{ZFC}\vdash\bigl(\text{the specified equation has no solution in its stated domain}\bigr)
\longleftrightarrow\operatorname{Con}(\mathsf{ZFC}).$$

This is an ordinary mathematical reduction, intended and argued to be formalizable in ZFC, composed with the inherited blank-machine/compiler calibration. It is not a proof of consistency, an unconditional independence theorem, a global minimality result, or a newly kernel-checked end-to-end formalization. The executable audits certify finite arithmetic, identities, degree arguments and provenance at their documented boundaries; they do not certify the entire unbounded compiler theorem.

# Scope, pin and counting convention

The comparison uses the ProveIt repository at immutable commit

`ae3007ca4467011e0e051c84acb4a1dd13971b0e`

under `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`. It covers the new wave-3 packages 16--23 and compares their contributions against the earlier local Wang943 synthesis. The exact source URL, Git blob SHA-1, local SHA-256 and byte count for the reviewed source selection are recorded in the source ledger. The online entry point is the [pinned catalogue](https://github.com/VladimirReshetnikov/ProveIt/tree/ae3007ca4467011e0e051c84acb4a1dd13971b0e/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms).

One binary addition, subtraction or multiplication costs one operation, including multiplication by a fixed coefficient or by a small integer and including a squaring. Previously computed values may be reused. A fixed enormous integer is a leaf of degree zero, not a run-time integer-construction cost. In an equality-comparison system, comparisons are free; converting it to residuals or a sum of squares has an additional, separately stated cost. Thus an operation count is a straight-line-program measure, not a bit-complexity, file-size or proof-complexity measure.

The domain matters: $\mathbb N=\{0,1,\ldots\}$, $\mathbb Z_{>0}=\{1,2,\ldots\}$ and $\mathbb Z$ are not interchangeable for variable counts. Squaring or a three-variable positivity encoding changes the number of unknowns. Shifting a natural variable by one preserves existence but requires a new circuit count. We do not silently compare any of these encodings as if they were identical.

# What the eight packages contribute

| Package | Main reusable idea | Representative original result |
|:--|:--|:--|
|16 integer27 | Smaller separator; signed lifting | 13 positive, degree 515, 84 ops; 27 integers, degree 1004, 139 ops |
|17 primitive12 | Sixteen separated branches; rational Pell saturation | 12 positive, degree 2601, 167 ops |
|18 jones9 | Explicit Jones specialization; radical finalizer | 9 naturals, degree $161844\cdot5^{33}+484$, 20531 ops |
|19 wang943 | Compact coherent compiler; four-root saturation | 12 positive, degree 1257, 139 ops; 26 integers, degree 2465, 192 ops |
|20 root12 | Separate the main root outside the inner norm | 12 positive, degree 1145, 123 ops |
|21 norm12 | Nested quadratic norms and economical evaluation | 12 positive, degree 1353, 116 ops |
|22 monic12 | Monic merger; retained-coordinate system | 12 positive, degree 1529, 117 ops; 16 positive, 7 equations, degree 24, 59 ops |
|23 separating12 | Odd scales and low-degree integer lifting | 27 integers, degree 172, 116 ops; positive 12-variable alternative |

The table intentionally gives representative points, not an assertion that every variant was independently re-proved. Fifteen selected literal circuits across all eight packages were count- and liveness-audited. Mathematical source review was deeper for the ingredients actually used in the synthesis. The individual audit records distinguish independently reconstructed degrees from merely recorded source degrees.

Several earlier points remain useful. The old 67-operation single equation remains smaller in arithmetic-operation count than the new low-variable single equations. The 59-operation retained system remains the lowest operation count established here for that system family. The new work does not improve either of these operation-only benchmarks.

A particularly important correction is that package 18 is genuinely explicit: its nine-variable result is not merely an existence statement about a universal polynomial with an unspecified index. Its fixed leaves have finite bounded recipes. But that does not mean the recipes were evaluated into a complete expanded decimal coefficient list. Those two senses of explicitness must remain separate.

# The new comparison frontier

| Construction | Domain | Vars | Eqs | Degree | Binary ops |
|:--------------------------|:------------:|----------:|----------:|--------------------:|------------:|
| Small positive product | positive | 12 | 1 | 1081 | 111 |
| Small positive system | positive | 12 | 3 | 1072 max | 107 |
| Sharp pair norm | integers | 24 | 1 | 2240 | 165 |
| Sharp pair-norm system | integers | 24 | 3 | 2224 max | 161 |
| Small-weight norm | integers | 25 | 1 | 920 | 131 |
| Small-weight system | integers | 25 | 4 | 872 max | 126 |
| Ordinary two-root merger | integers | 26 | 1 | 214 | 123 |
| Ordinary two-root system | integers | 26 | 5 | 128 max | 117 |
| Quadratic system | positive | 31 | 22 | 2 max | 65 |
| Quartic sum of squares | positive | 31 | 1 | 4 | 130 |
| Tight Jones specialization | naturals | 9 | 1 | $120724\cdot5^{32}+366$ | 1840 |

The integer system equation counts follow the literal comparator outputs. The normalized 26-integer alternative has the same 123 operations but degree 236 and is therefore not preferred on these two criteria. The older unsharpened 24-integer separator has degree 2256 at the same 165 operations; it is retained only to expose the improvement and proof history.

Relative to the earlier local synthesis, the 12-positive polynomial saves 28 operations (20.1%) and lowers degree from 1257 to 1081 (14.0%). The new 26-integer ordinary version saves 69 operations (35.9%) and lowers degree from 2465 to 214 (91.3%). The 24-integer version instead prioritizes two fewer integer variables. The quartic saves one variable and one quadratic equation.

For nine variables, two distinct results must not be conflated:

1. Re-evaluating the *same original* package-18 polynomial by shared radix-five powers and sparse Horner form reduces its circuit from 20531 to 1704 operations, without changing its polynomial or degree.
2. The recommended new nine-variable polynomial additionally uses the 31-variable quartic and tighter unconditional companions. It has 1840 operations but a much smaller degree, approximately 14.9% of the original degree. This is not a same-polynomial rewrite.

Neither dominates the other on operation count and degree. Both have nine natural unknowns. The first has 348 fixed leaves; the new one has 404 because the new parent quartic yields 402 nonzero weighted coefficient recipes rather than 346. Fewer parent variables did not imply a sparser coefficient list.

# A readable recommended equation

The concise 12-positive-variable recommendation has supplied variables

$$J,F,\alpha,z,h,i,T,s,w,\eta,\zeta,t>0.$$

Bind the four fixed ports once and for all as described below. Define

$$\begin{aligned}
q&=\beta J+1,& C&=q-F-\alpha,&X&=wq,&Y&=sq^3,\\
E&=XY,&k&=\eta+\zeta,&c&=kY+\eta,&a&=E+Y,\\
H&=4a+3,&\Delta&=a^2+H,&\ell&=EkY,\\
A&=1+\ell(\ell+k),&G&=1+\Delta c^2,&b_0&=X+ac.
\end{aligned}$$

Further put

$$R=((q-1)(q-F)+\alpha)(q^2-1)+(M_C+qM_F)J.$$

$$\begin{aligned}
N_k&=k-hE-R,\\
N_t&=(K_0+w)C+q-F-z(q-1).
\end{aligned}$$

$$\begin{aligned}
I&=ic^2,&D&=1+\Delta I^2,\\
Q&=\Delta(D-1),&d&=Q-1,\\
v&=cT,&b&=c+RD,\\
P&=QDv^2,&U&=Qb^2,\\
M&=k(I^2+T^2),&L&=HM+1,\\
W&=b_0+Ht.&&
\end{aligned}$$

The following scalar evaluator contains no division, radicals or extra witnesses:

$$\begin{aligned}
n_0&=(HM)^2A,&d_n&=dn_0,\\
H_P&=H^2P,&H_U&=H^2U,&H_e&=H_P+H_U-H^2,\\
j_0&=4H_PH_U,&S_0&=2d(W^2+L^2G),\\
K_n&=d^2(W^2-L^2G)^2,&A_0&=2(d_n+H_e),\\
c_0&=(d_n-H_e)^2-j_0,&a_t&=S_0-A_0,\\
b_t&=c_0-K_n,&c_1&=16d_nj_0,\\
v_r&=a_t(a_tS_0+2b_t)-c_1,&u_r&=b_t^2-a_t^2K_n,\\
N&=u_r^2+S_0u_rv_r+K_nv_r^2.
\end{aligned}$$

The equation is simply

$$\boxed{\quad N_kN_t(1+N)-1=0.\quad}$$

Alternatively retain the three equations $N_k=N_t=1$, $N=0$. The 111-operation product and 107-operation system are completely expanded into literal binary arithmetic records in the supplied JSON. The displayed shared-expression arrangement is explanatory; the literal circuit is the authoritative operation ledger.

## Why this merger is safe

An eliminant can have unwanted roots unless its branch, denominator and integrality obligations are proved. Here the norm $N$ is a square modulo four, so the product equation forces $N=0$ and a common unit sign for $N_k,N_t$. The authenticated weak transport bounds apply before root recovery.

The smaller weight $M=k(I^2+T^2)$ controls every complex root of the inner polynomial strictly inside $|x|<M\sqrt G$. The outer coefficient $L=HM+1$ then forces $G$ to be a square: otherwise conjugation would create two roots farther apart than that bound allows. The selected main root is positive because $W>0$. Rational recovery of the remaining roots uses explicitly nonzero denominators. Rational square roots of integers are integral; the remaining rational auxiliary Pell coordinate is handled by the special saturation lemma, not by a false general claim about nonmonic quadratics.

The congruence $L\equiv1\pmod H$ restores the main-root affine coordinate, and a separate growth inequality proves that coordinate positive. Only then is the inherited signed quotient/compiler theorem applied. The complete argument, including bounds for complex branches and exact leading forms, is given in the positive proof appendix.

# Low degree without opaque eliminants

The 31-variable system is the most transparent new alternative. It deletes the old packing register $G$ from the 32-variable quartic using

$$G=q(q-F)-C,\qquad N=q(L+1),\qquad L=q^2-1.$$

The packing product is replaced by

$$LG=(q-F)(N-q)-CL.$$

This is quadratic in the retained coordinates, unlike the naive substitution. Their difference is exactly

$$(q-F)\bigl(q(L+1)-N\bigr),$$

which is zero by a retained equation. Conversely the unchanged transport relation implies $C>0$, so

$$G=(q-1)C+q\alpha>0.$$

Thus the deleted coordinate is recovered with its required sign. This is a bijection of positive solution tuples, not just an informal elimination. All 22 residuals are quadratic. Their sum of squares has degree exactly four because its $\tau^4$ coefficient is one. Replacing every positive input by a natural input plus one gives a normalized quartic: at the all-zero natural tuple, the fifth original residual is one independently of all fixed ports.

That normalized 31-witness polynomial is the input to the new Jones specialization. The parameter $\nu=31$ is the parent quartic's witness count. It is not the compiler radix exponent and is not the nine-variable output count.

# Integer domains and fewer positivity witnesses

Six source ports require positivity. Each uses its own three-integer surjection

$$\operatorname{Pos}(a,b,c)=1+a^2+b^2+c(c+1).$$

The other scale coordinates are encoded as $i=2r+1$, $s=2v+1$, $w=u^2$. This uses 21 unrestricted integer inputs before retained merger coordinates are added. It does not assume $s$ positive: the signed source theorem must exclude $s<0$, and the zero-scale case $w=0$ must be ruled out explicitly.

The 24-variable construction retains $h,T,t$ and merges both outer roots through a quadratic-algebra pair norm. A strict bound allows its separator to be reduced from $3HW$ to $2HW$. This causes a genuine leading-term cancellation in one formal branch, lowering the degree from 2256 to 2240 at unchanged operation cost. The proof separately handles a zero auxiliary coefficient, zero $w$, negative $H$, coincident quadratic extensions and integrality of the recovered affine coordinate.

The 25-variable construction also retains $\gamma$ and uses a smaller inner weight. Its degree is 920. The 26-variable construction additionally retains $f$ and merges only the first and auxiliary roots. Its ordinary strong relation gives degree 214 instead of 236. A proof that $1<A<Q_0$ excludes the otherwise problematic $t=0$ branch. All of these distinctions are substantive: discarding a boundary case or replacing a signed root by its absolute value inside an affine identity would not be valid.

# Nine variables: explicit, smaller, still enormous

The final polynomial has the nine nonnegative inputs

$$\epsilon,g_0,h_0,s_0,w_0,\phi,i_0,j_0,n.$$

The six shifts $g=g_0+1$, $h=h_0+1$, $s=s_0+1$, $w=w_0+1$, $i=i_0+1$, $j=j_0+1$ are part of the circuit. The other three inputs are not shifted.

Its construction has four layers:

1. Shift the 31-variable quartic to natural inputs and expand its degree-at-most-four coefficient data.
2. Form the explicitly bounded Jones index from 402 weighted coefficient records and the fixed bound $z_*=2^{45933757}$. The companion $y_*$ is a specified finite sum, not an unspecified recursively enumerable-set index.
3. Use shared fifth powers, complete-homogeneous recurrences and sparse Horner evaluation to avoid repeatedly building huge powers. All exponents in the polynomial evaluation are fixed nonnegative integers and are lowered to multiplication-only circuits.
4. Replace crude magnitude majorants with positive unconditional companions and apply the audited two-radical finalizer.

The evaluation identities can be stated exactly. Put $r=5^\nu$, $L=5^{\nu+1}$ and $p_j=B^{5^j}$. If $h_4$ is the complete homogeneous symmetric polynomial of degree four, the full baseline digit sum is

$$\sum_{|\alpha|\le4}B^{L-\sum_{j=0}^{\nu}\alpha_j5^j}
=B^r h_4\bigl(B^r,B^{r-5^0},B^{r-5^1},\ldots,B^{r-5^\nu}\bigr).$$

The first argument records the slack exponent $4-|\alpha|$. Starting with $h_0=1$ and $h_1=\cdots=h_4=0$, append an argument $v$ by updating $h_k\leftarrow h_k+vh_{k-1}$ in ascending order $k=1,2,3,4$. Suffix products give $B^{r-5^j}=\prod_{k=j}^{\nu-1}p_k^4$, so every exponent is nonnegative. The geometric sum is

$$\lambda=(1+q)(1+q^2)\prod_{j=0}^{\nu}(1+p_j+p_j^2+p_j^3+p_j^4),\qquad q=B^L.$$

For nonzero sparse correction exponents $E_1>\cdots>E_m$, sorted Horner evaluation starts with $A=c_1$, replaces $A$ by $AB^{E_{i-1}-E_i}+c_i$, and ends with $AB^{E_m}$. The fifth-power ladder and shared radix-five digit runs evaluate these fixed powers by multiplication only. These identities, rather than numerical coincidence, justify the circuit rewrite.

The finalizer has the recognizable form

$$\bigl[\Theta^2-\Omega^2(a_0+V_0^2a_1)\bigr]^2
-4\Omega^4V_0^2a_0a_1=0.$$

The accompanying proof establishes both the separated-radical recovery and the required positivity/divisibility implications, including the zero-sum branch. The complete formulas and the proof that the smaller companions dominate every relevant signed expression appear in the nine-variable appendix. The exact circuit, coefficient recipes and independent leading-term certificate are included.

The exact degree is

$$120724\cdot5^{32}+366
=2\,810\,824\,662\,446\,975\,708\,007\,812\,866.$$

A cancellation-aware symbolic leading-term audit finds the nonzero diagonal leader $2^{274}z_*^2$. Because the selected $z_*$ is positive, this proves the degree uniformly for the selected instance, not just as a sampled upper bound. No finite evaluator expands this astronomical-degree polynomial into all monomials.

# Exact coefficient binding and materialization

The selected backend for every new recommended construction is one *complete* compact Wang943 tuple. Set

$$B=2^{5^{10}},\qquad\beta=B-1,\qquad
K_0=K,\qquad M_C=M_C,\qquad M_F=M_{F,\mathrm{source}}.$$

The last port is the shifted source mask, not the native unshifted mask. Source metadata that records the original derivation tuple is preserved as provenance; the package's explicit whole-tuple binding governs the delivered instantiation. Changing only $\beta$ or mixing ports from different compilers would not be justified by these proofs.

The four unsigned little-endian integer payloads are fully materialized. Their total raw size is 5,312,269 bytes and their deterministic gzip total is 20,260 bytes. The binding contains the exact decompressed SHA-256 identities and bit lengths. The Jones bound $z_*$ is also materialized: 5,741,720 raw bytes, with a 5,613-byte deterministic gzip representation, with its own digest and exact power-of-two check.

The 402 weighted coefficients of the new nine-variable circuit and $y_*$ are fixed by bounded finite recipes. They are not individually materialized. Nor is the expanded final nine-variable coefficient list. The package supplies all data necessary to identify those integers exactly and evaluates their residues for actual-instance checks, without claiming to have printed or expanded them in full.

The important compression is mathematical and representational, not a claim that bit complexity became small. A tiny gzip file for a power of two can denote an enormous integer, while a finite recipe can denote an integer too large to materialize practically.

# What was verified, and what remains inherited

The new executable work uses only newly authored checkers and treats received files as inert data. No received Python program or Lean source was executed or imported, no proof environment was installed, and no public repository was modified.

The evidence separates four levels:

1. Exact finite algebra: sparse identities, norm identities, coefficient reconstruction, all-gate/all-input liveness, operation ledgers, exact symbolic leading terms, source hashes and materialized coefficient hashes.
2. Supplementary numerical diagnostics: signed boundary cases, modular evaluation at independent primes, synthetic radical witnesses and actual fixed-tuple residues. These are useful error detectors, not proofs of unbounded equivalences.
3. New ordinary proofs: all branch separation, sign restoration, rational saturation, zero-case exclusion, direct completeness maps, quartic elimination and smaller companion estimates in the appendices.
4. Inherited unbounded dependencies: the calibrated K215 refutation computation, native-window/blank compiler equivalence, complete Wang943 transfer, signed odd-scale rank/population arguments, and the applicable Jones specialization theorem.

The rational Pell saturation lemma is particularly important. For integer $m\ge2$, integer $V$ and rational $y$,

$$m^2V^2-(m^2-1)y^2=1\quad\Longrightarrow\quad y\in\mathbb Z.$$

Its proof uses the ordinary integer-coordinate Pell group and index divisibility. It is not the false assertion that every rational root of a nonmonic integer polynomial is integral. Repeated or square radicands likewise require actual automorphisms or universal norm identities, not an assumed full multiquadratic field degree.

The archive verifier checks an immutable file manifest before running checkers in a temporary copy, rejects Python optimized mode, and leaves the delivered tree unchanged. It verifies pinned local source bytes against their recorded Git blob and SHA-256 identities. Fresh isolated replay results are recorded separately. A passing replay does not silently upgrade the ordinary proofs into a proof-assistant certificate.

# Productive next steps

The best next work depends on which objective matters.

- For readability and proof assurance, formalize the new Pell saturation, root recovery and signed zero-case lemmas before attempting further aggressive eliminations. These are the high-risk boundaries, unlike routine norm expansion.
- For the 12-positive equation, search for a smaller shared scalar norm evaluator and weights that preserve the pre-recovery complex-root bounds. A cheaper norm formula without a valid bound is not an improvement.
- For low degree, seek another relation-aware register elimination in the quadratic system. The successful deletion used a retained relation; naive substitution alone missed it. Do not eliminate a positive port unless its recovery and strict sign are proved.
- For nine variables, compare the lower-degree 1840-operation polynomial with the 1704-operation same-polynomial rewrite according to the user's preferred metric. Continue sparse radix-five scheduling and companion simplification, but audit exact cancellation after every change.
- For fewer unrestricted integers, investigate additional signed or odd canonical coordinates only where both soundness and canonical completeness survive. More permissive signs can introduce spurious solutions.
- For much smaller constants, optimize the authenticated native compiler while preserving the complete four-port interface. Compiler radix compression does not by itself reduce the Jones witness parameter.

Several tempting shortcuts were rejected: inferring coefficient validity from portwise congruences, replacing the Jones parameter by the compiler radix exponent, omitting rational saturation, overlooking negative scales or zero merger coordinates, and claiming formal verification from source inspection alone.

# Reading the accompanying package

The top-level README identifies the selected circuits, proof files, coefficient binding and one-command verification. The report is available as PDF and editable TeX. The archive contains the exact circuit descriptions and fixed-coefficient recipes, pinned source data, ordinary proofs, newly authored checkers, their receipts and an immutable digest manifest. Provenance-only source files are not executable dependencies of the checker suite.

The appendices below contain the complete new mathematical reductions and the detailed comparison audit. Repeated local symbols are scoped to their own appendix. In particular, the quartic's positive transport coordinate, the Jones fixed index, the pair-norm register and the compiler radix are different objects even when earlier sources used similar letters.


# Appendix A. Complete positive-variable proof


## Result and logical scope

The three-equation circuit `positive12_system.json` has twelve strictly positive
supplied variables, 107 charged binary arithmetic operations (66 multiplications,
41 additions/subtractions), and residual degrees 7, 2, 1072. Its single-equation
product `positive12_product.json` has 111 operations (68 multiplications,
43 additions/subtractions) and exact total degree 1081.

This combines package 20's main-root/inner-root merger with package 21's congruence
carrier and scalar norm factorization, and adds a smaller separating weight and
a trace/product quadratic-remainder evaluator. It is strictly smaller in both
operation count and degree than the wave-3 12-variable degree winner
(20: degree 1145, 123 operations) and operation winner (21: degree 1353,
116 operations). It also improves the previous local twelve-variable form
(degree 1257, 139 operations). It is not a variable-count improvement and is
not claimed globally optimal. Package 18's explicit nine-variable construction
remains a separate, extremely high-degree choice.

The four fixed coefficients are the complete materialized compact Wang943 tuple
from package 19: B=2^(5^10), beta=B-1, K0=K, MC=MC, MF=MF_source. The last is the
shifted mask, not MF_native. The local `COEFFICIENT_BINDING.json` supplies every
payload hash and a finite recipe/source; no coefficient is unspecified and no
individual port is mixed with another compiler. All other displayed registers
below are computed expressions, not quantified variables.

The inherited compiler and literal K215 calibration imply, by ordinary
mathematics formalizable in ZFC,

    ZFC proves: (no positive solution) iff Con(ZFC).

This is an equivalence, not a proof of consistency or a new end-to-end
proof-assistant formalization. The finite checker below tests only the arithmetic
identities, counts, leading degrees, payloads and synthetic radical witnesses,
not the inherited unbounded compiler/calibration theorem.

## Definition

The twelve supplied positive integers are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,t.

Retain the common interface:

    q=beta*J+1, Cw=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1,
    ell=E*kY, A=1+ell*(ell+k), G=1+Delta*c^2, b0=X+a*c,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
    Nk=k-hE-R,
    Nt=(K0+w)*Cw+q-F-z*(q-1).

Define

    I=i*c^2, D=1+Delta*I^2, Q=Delta*(D-1)=(Delta*I)^2,
    d=Q-1, v=c*T, b=c+R*D,
    P=Q*D*v^2, U=Q*b^2, e=P+U-1, Baux=2*Q*v*b,
    M=k*(I^2+T^2), L=H*M+1, W=b0+H*t.

For a formal indeterminate x put

    C(x)=d*(x^2+M^2*A)-e,
    F(x)=[C(x)^2+D*Baux^2-4*d^2*x^2*M^2*A]^2
          -4*C(x)^2*D*Baux^2.

Write F_H(z)=H^8 F(z/H). The polynomial being enforced is

    N=F_H(W-L*sqrt(G))*F_H(W+L*sqrt(G)).

The radical notation is only a compact definition of an integer polynomial;
the following division-free scalar formula is its complete evaluator:

    n=(H*M)^2*A, dn=d*n,
    HP=H^2*P, HU=H^2*U, He=HP+HU-H^2=H^2*e,
    j=4*HP*HU=H^4*D*Baux^2,
    Trace=2*d*(W^2+L^2*G),
    Knorm=d^2*(W^2-L^2*G)^2,
    AA=2*(dn+He), constant=(dn-He)^2-j,
    at=Trace-AA, bt=constant-Knorm, coef=16*dn*j,
    vr=at*(at*Trace+2*bt)-coef,
    ur=bt^2-at^2*Knorm,
    N=ur^2+Trace*ur*vr+Knorm*vr^2.

The system and product are

    Nk=1, Nt=1, N=0;
    P12=Nk*Nt*(1+N)-1=0.

Each multiplication by 2,4,16 and every other binary operation is charged in
the emitted JSON. Scalar comparison is free in the system ledger.

## Why the evaluator is exactly the intended norm

The identity

    (C^2+j-K)^2-4*j*C^2=(C^2-K-j)^2-4*K*j

holds in any commutative ring. With z=H\*x it rewrites F_H(z) as

    [ (d*z^2)^2-AA*(d*z^2)+constant ]^2-coef*(d*z^2).

For z=W+/-L\*sqrt(G), put x_+/-=d\*z^2. Their sum and product are exactly
Trace and Knorm. Modulo x^2-Trace\*x+Knorm, the expression x^2-AA\*x+constant
is at\*x+bt. Squaring and subtracting coef\*x leaves ur+vr\*x. Its norm is
`ur^2+Trace*ur*vr+Knorm*vr^2,` proving the formula uniformly, including square,
zero or coincident quadratic specializations. There is no black-box resultant,
nonzero-discriminant assumption or extra witness.

## Product units and the bounds available before root recovery

Set x0=d\*(W^2+L^2\*G). Then Trace=2\*x0 and

    Knorm=x0^2-4*d^2*W^2*L^2*G.

Consequently N is congruent to (ur+x0\*vr)^2 modulo 4. Thus 1+N cannot be
-1. At a positive root of P12, each of its three integer factors is a unit,
so N=0 and Nk=Nt=epsilon for a common epsilon in {1,-1}.

The inherited weak transport/mask bootstrap, which permits both signs and the
boundary Cw=0, gives

    Cw>=0, q>=16, X>=q, Y>=q^3, E=XY,
    3q<R<q^4-2, k=R+epsilon+hE>E.

It follows without using any eliminated roots that

    kY<c<2kY, a+2<2E, D<(a+2)^2*I^2,
    c<I^2, R>1, Y^2>20R, kY>8E.

Every denominator used below is nonzero: H,M,d,Baux are positive; Q>1,
D>1 and A>1. The bounds come from the whole selected coefficient tuple's
common-interface theorem, not merely from residue tests of its four ports.

## The smaller separating weight

Put Aparam=a+2. First,

    sqrt(G)>(a+1)c,
    sqrt(A)<ell+k.

Since c>kY and a=E+Y,

    sqrt(G)-sqrt(A)>k*(Y^2+Y-1)>kY^2.

Also sqrt(A)>ell=EkY>kY^2, because X>1 and E=XY.

The new choice M=k(I^2+T^2) bounds both kinds of auxiliary terms cheaply.
Using I^2+T^2>=2IT and kY>8E,

    2*v*sqrt(D)<8*k*E*Y*I*T < (1/2)*M*k*Y^2.

Further c<I^2, D<4E^2 I^2 and RE^2>1 imply

    b=c+RD<5RE^2 I^2.

Since k>E and Y^2>20R,

    2b<10RE^2 I^2 < (1/2)*M*k*Y^2.

Therefore

    2*(v*sqrt(D)+b)<M*k*Y^2
        <min(M*sqrt(A), M*(sqrt(G)-sqrt(A))).             (1)

This sharpens both separation roles at once. In particular, with
P0=Dv^2+b^2 and e=QP0-1,

    M^2*A>4*(v*sqrt(D)+b)^2>4P0,
    d*M^2*A>2Q*P0,

because d=Q-1>=Q/2. Consequently for every real x,

    C(x)>Q*P0+1>Baux*sqrt(D)>0.                          (2)

No recovered square root, rationality, sign or integer quotient is used in
these estimates. They are weaker in one numerical constant than package 20's
old d M^2 A>4QP0 bound, but (2) is precisely what reconstruction requires.

## All complex roots and exclusion of spurious branches

The elementary factorization of F gives the complete root description

    x=M*tau+y,
    tau^2=A, f^2=D,
    d*y^2=e-Baux*f=Q*(v*f-b)^2-1.                        (3)

Indeed, factor F first using f^2=D and then using tau^2=A:

    [C(x)+Baux*f]^2=4*d^2*x^2*M^2*A,
    C(x)+Baux*f=2*d*x*M*tau.

Expanding the last equality gives (3), and conversely (3) gives F(x)=0.
Both factorizations are valid over the complex numbers without dividing.
The two f roots are real. For either of them and any complex y satisfying
(3), the absolute-value estimate gives

    |y|<2*(v*sqrt(D)+b).

For example `d|y|^2=|Q(vf-b)^2-1|<Q(v` sqrt(D)+b)^2 and Q/d<=2.
The strict inequality also covers a negative right side: its absolute value
is at most 1, while Q(v sqrt(D)+b)^2>1.

By (1), every complex root x of F obeys

    |x|<=M*sqrt(A)+|y|<M*sqrt(G).                       (4)

Moreover x=0 is not a root: (2) gives
`F(0)=[C(0)^2-D*Baux^2]^2>0.` This will justify the rational-recovery
formula's denominator rather than silently discarding a zero branch.

## Recover the main root and its congruence

If N=0, choose bmain=+sqrt(G) or -sqrt(G) with
F_H(W-L\*bmain)=0 and put x=(W-L\*bmain)/H. Thus F(x)=0.

If G is not an integer square, its two roots are irrational quadratic
conjugates, so both F_H(W-L\*sqrt(G)) and F_H(W+L\*sqrt(G)) vanish.
Their associated x roots have distance 2L sqrt(G)/H. By (4) the distance
is strictly less than 2M sqrt(G), contradicting L=HM+1. Thus G is a square
and bmain is an integer; x is rational.

The chosen bmain cannot be negative. Indeed W=b0+Ht>0, but then

    W=L*bmain+H*x < -L*sqrt(G)+HM*sqrt(G)<0

by (4). Therefore bmain>0. No unsupported absolute-value replacement of
an affine main-root expression has occurred.

## Recover the other roots and every denominator

For the rational real x just obtained, (2) and x!=0 justify

    Ux=C(x)^2+D*Baux^2-4*d^2*x^2*M^2*A,
    f=-Ux/(2*C(x)*Baux),
    tau=(C(x)+Baux*f)/(2*d*x*M),
    y=x-M*tau.

The equation F(x)=0 gives f^2=D. The squared identity in Section 13.6 gives
tau^2=A. These rational roots of integer squares are integers. Expansion
restores (3), so V=vf-b is an integer and

    Q*V^2-(Q-1)*y^2=1.

Here Q=S^2 with the integer S=Delta\*I>=2. The rational auxiliary Pell
saturation lemma below makes y an integer. Hence x=M\*tau+y is integral.
As W=b0+Ht=L\*bmain+Hx and L=1+HM, reduction modulo H gives
bmain=b0 modulo H. Therefore gamma=(bmain-b0)/H is an integer.

In fact gamma>0 without a signed-main-root extension: sqrt(Delta)>a+1,
bmain>0 and bmain^2=1+Delta c^2 give bmain>(a+1)c. Also
c>k>E>X, so bmain-ac-X>c-X>0.

### Rational auxiliary Pell saturation

If S>=2 and V are integers and rational y satisfies
S^2 V^2-(S^2-1)y^2=1, write S^2-1=d0\*b0^2 with squarefree d0>1.
The rational z=b0\*y is integral because a reduced denominator squared
would divide squarefree d0. Both (S,b0) and (|SV|,|z|) are nontrivial
positive integer-coordinate Pell solutions for d0. Write them as indices
m,n in the powers of the fundamental integer-coordinate Pell unit.
For its coordinates chi_j,psi_j, the identities modulo chi_m give
chi_(j+2m)=-chi_j and chi_(2m-j)=-chi_j. Reduce n modulo 2m and reflect
into 0<=r<=m. Since 1<=chi_r<chi_m for r<m, divisibility chi_m|chi_n
forces n to be an odd multiple of m. The addition formulas then imply
psi_m|psi_n. Thus b0 divides |z|, and y is integral. This uses the ordinary
integer Pell group, not the possibly larger half-integral unit group.

## Soundness and direct completeness

We have restored

    tau^2-ell*(ell+k)=1,
    (X+ac+gamma H)^2-Delta*c^2=1,
    f^2-Delta*i^2*c^4=1,
    Q*[c*(T*f-1)-R*f^2]^2-(Q-1)*y^2=1,
    Nk=Nt=epsilon.

The identity vf-b=c(Tf-1)-Rf^2 uses f^2=D. Gamma is positive; tau and y
can be replaced by their positive absolute values. If f<0, change f and T
simultaneously to their negatives, preserving Tf and every relevant equation.
The signed-quotient extension of the normalized blank interface allows this
signed T and common weak unit sign. It forces epsilon=+1 and recovers the
blank K215 computation, exactly as package 20's inherited package-09 theorem.
The mask/decoder does not depend on the harmless auxiliary sign choices.

Conversely start with any canonical positive normalized blank-compiler witness.
Keep all eleven retained coordinates and set

    t=gamma+M*bmain+M*tau+y>0.

Then W=L\*bmain+H(M\*tau+y), so its corresponding factor F_H(W-L\*bmain)
vanishes. Hence N=0 and Nk=Nt=1. This proves completeness directly,
without changing i, choosing a new Pell index or imposing a new divisibility
restriction. It proves equivalence in existence, not a bijection of witnesses.

## Exact degrees

Fixed coefficients have degree zero. The unchanged degrees are
`c=5,a=H=6,Delta=12,R=4,ell=11,A=G=22,I=11,D=34,Q=d=46,`
v=6,b=38,P=92,U=e=122. Our new degrees are

    M=23, L=29, W=11, n=80, dn=126,
    HP=104, HU=He=134, j=238,
    Trace=126, Knorm=252, AA=134, constant=268,
    at=134, bt=268, coef=364, vr=402, ur=536.

He has the nonzero highest form H_top^2 U_top. Because deg(He)>deg(dn),
constant and bt have top form He_top^2; because 536>520, ur has top
form He_top^4. In N the other two term degrees are at most 1064 and 1056,
strictly below deg(ur^2)=1072. Thus

    N_top=He_top^8=H_top^16*U_top^8

is nonzero, proving exact degree 1072 without a generic-specialization claim.
The nonzero Nk,Nt leading forms add 7+2, proving exact degree 1081 for P12.
All fixed positive beta slices have these degrees. The checker supplements
this proof with two independent finite-field univariate degree tests.

## Provenance and verification boundary

`SOURCE_PINS.json` records the immutable repository pin
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`, exact relevant blob IDs and local
SHA-256 hashes. The new proof/emitter/checker are locally authored; no received
program is executed, imported, installed or used to mutate the public repository.
The new-owned checker evaluates received circuit JSON only as inert arithmetic
records and verifies the new circuit against a separately implemented
multiquadratic conjugate product. Synthetic kernel witnesses do not claim to
encode an accepting ZFC-refutation computation.


# Appendix B. Complete integer-family proof


## Status, scope, and exact statements

This is a new ordinary mathematical reduction, formalizable in ZFC, from the authenticated blank-machine Pell interface. It is not a new Lean/Rocq proof, a proof of Con(ZFC), or a global minimality claim. For a single coherent authentic coefficient quartet, the displayed equations have integer solutions exactly when the calibrated blank K215 refutation machine halts. Therefore ZFC proves that their lack of integer solutions is equivalent to Con(ZFC).

The six guarded source ports are J,F,alpha,z,eta,zeta. Replace each with its own disjoint positive surjection

    Pos(a,b,c)=1+a²+b²+c(c+1).

Set i=2r+1, s=2v+1, w=u². These substitutions use 21 unrestricted integers and 47 binary gates. The three constructions retain, respectively:

- 24 integers: h,T,t.
- 25 integers: h,T,t,gamma.
- 26 integers: h,T,t,gamma,f.

Every retained coordinate is unrestricted. The selected source quartet must always be complete; MF means the shifted high-mask port. The original package-06 quartet is a safe direct binding for the proofs below. The compact Wang943 quartet from the previous round is also admissible through its whole-tuple compiler transfer and the native mask population identity used by the odd-scale theorem. No mixing of coefficient ports is permitted. The new catalogue's T4 choices require their own complete audited binding, not just replacement of beta.

Exact literal circuits and verified ledgers:

| Form | Vars | Degree | Ops | Mul | Add/sub |
|----------------------------------------|------:|------:|------:|------:|------:|
| Sharpened pair norm (Section 14.9) | 24 | 2240 | 165 | 96 | 69 |
| Threefold-separator comparison | 24 | 2256 | 165 | 96 | 69 |
| Small-weight norm | 25 | 920 | 131 | 70 | 61 |
| Ordinary two-root merger | 26 | 214 | 123 | 63 | 60 |
| Normalized two-root alternative | 26 | 236 | 123 | 64 | 59 |

All gates and all input ports are live. Comparisons are not arithmetic gates. Every abbreviation is expanded by the JSON straight-line circuits, which use only integer constants and binary +,-,\*.

## Common polynomials and signed pre-bootstrap

Define

    q=beta J+1, C=q-F-alpha, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a²+H=(a+2)²-1, P0=X+ac,
    ell=E kY=XkY², A=1+ell(ell+k), G=1+Delta c²,
    R=((q-1)(q-F)+alpha)(q²-1)+(MC+q MF)J,
    Nk=k-hE-R,
    Nt=(K0+w)C+q-F-z(q-1).

The authentic fixed coefficients satisfy beta>=15 and K0>=2 and the source mask bounds. If Nt is a unit, C<=-1 is impossible, since

    Nt=(K0+w)C+1-F-(z-1)(q-1)<=-2.

Thus C>=0. The authentic weak transport/mask bootstrap gives

    q>=16, q(q²-1)<R<q⁴-2.

These deductions require neither X>0 nor s>0. Since s is odd, Z0=|Y|>=q³. Since X>=0, |a|=(X+1)Z0>=q³. The signs of a,c,H are the sign of Y. Both signs satisfy

    k(Z0-1)<|c|<k(Z0+1), |c|>2, |H|>1,
    Delta>=(q³-1)(q³-3)>q⁴>R.

Also ell>=0 and A>=1, with A=1 exactly when X=0. In particular Delta is positive even for negative s and is 0 or 3 modulo four.

For the normalized strong quantities let

    I=i c², S=Delta I, D=1+Delta I², Q=S², d=Q-1,
    vaux=cT, b=c+RD,
    e=Q(D vaux²+b²)-1, Baux=2Q vaux b.

The nonzero odd i and |c|>2 give Q>2, D>Delta+|c|, and

    b>D-|c|>1,
    Q-b=(Delta-R)D-Delta-c>D-Delta-|c|>0.

Thus 1<b<Q, for either sign of s and including w=0 and T=0. This early strict interval replaces positive-only bounds in the older arguments.

## The 24-integer polynomial and optimized norm circuit

Put

    W=vaux²+D+2b, P=HW, K=P+1,
    uweight=3P, Z=Ht+K P0.

For temporary formal square roots tau²=A and g²=G define

    F(tau,g)=[d(Z-uweight tau-Kg)²-H²e]²-H⁴ Baux² D.

Let N be the product of F over the four formal signs of tau and g. No roots are supplied or existentially quantified in the actual equation:

    Nk Nt(1+N)-1=0.                                      (24)

Here is the lower-cost pair-ring evaluator. In the quadratic algebra with g²=G, let x=Z+Kg, x²=x0+x1 g, and set

    Cpair=d(x²+uweight² A)-H²e,
    Jpair=4d² uweight² A x²,
    Zterm=H⁴ Baux² D.

The inner norm over tau is the identity

    Fpair=(Cpair²-Jpair-Zterm)²-4 Jpair Zterm.

Write Fpair=F0+F1 g and output N=F0²-G F1². The circuit computes Zterm as 4H⁴ p z0, where p=QD vaux² and z0=Qb². Thus it never computes Baux as a separate intermediate. This is a polynomial identity, including all repeated-root and zero-Baux cases.

The odd coefficient F1 is even: x1=2ZK is even; every subsequent odd coefficient stays even under sums and products in this pair algebra. Hence N is a square modulo four. At a zero of (24), the three integer factors are units; 1+N cannot equal -1. Therefore N=0 and Nk=Nt=epsilon in {1,-1}.

### Every actual conjugate of the auxiliary root is bounded

Since A>=1 and G>1, a vanishing norm factor supplies real tau,g. Set

    y=(Z-uweight tau-Kg)/H.

If Baux is nonzero, f=(e-dy²)/Baux satisfies f²=D and

    dy²=e-Baux f=Q(vaux f-b)²-1.

Every actual conjugate f' is ±sqrt(D). All actual conjugates y' are real, since they lie in the totally real field Q(tau,g). Therefore

    |y'|<sqrt(2)(|vaux|sqrt(D)+b)
          <2(|vaux|sqrt(D)+b)<=vaux²+D+2b=W.

If Baux=0, then vaux=0 because Q and b are nonzero. Directly dy²=Qb²-1, which gives the same strict bound |y'|<2b<W. This case makes no division by Baux.

### The zero-w boundary is handled before separation

Write P=HW. Both signs of H are allowed. Since |P|>4,

    |K|>=|P|-1>3|P|/4, |K|<5|P|/4.

Also sqrt(G)>2, so |K|sqrt(G)>|P|=|H|W.

If w=0, then tau²=A=1, so tau is already rational. An automorphism changing g to -g in

    Z=uweight tau+Kg+Hy

would imply |K|sqrt(G)<=|H|W, a contradiction. Thus g is rational, hence an integer. Section 14.3.4 below proves y and gamma integral even here. Then the main equation g=P0+H gamma with X=0 reduces modulo H to 0=1, because g²-Delta c²=1 and Delta=a²+H. This contradicts |H|>1. Therefore w>0 and X>=q.

### Separation when w>0, including negative H and P

With X>=16 and Z0>=4096,

    |a+2|<(9/8)XZ0, |c|<(9/8)kZ0.

Thus

    sqrt(G)<|a+2||c|<(81/64)ell<(3/2)sqrt(A),
    sqrt(A)>8.

Consequently

    |K|sqrt(G)+|H|W
       <(15/8)|P|sqrt(A)+|P|
       <2|P|sqrt(A)<3|P|sqrt(A)=|uweight|sqrt(A).

Any actual automorphism flipping tau would contradict this inequality after subtracting its image of the displayed linear equation. Hence tau is rational, therefore an integer. A subsequent g flip contradicts |K|sqrt(G)>|H|W, so g is likewise an integer.

This argument uses only actual automorphisms. It makes no generic field-degree or root-independence assumption and covers square radicands and coincident quadratic extensions. Negative H,P,K require no special field argument because all separations use their absolute values.

### Rational auxiliary saturation and gamma integrality

Use the elementary saturation lemma:

    If m>=2 and V are integers and y is rational,
    m²V²-(m²-1)y²=1 implies y is an integer.

A full proof is inherited from round3/audit/RATIONAL_AUXILIARY_PELL_SATURATION.md and reproduced in upstream package 21. In brief, write y=a/b reduced. Then b² divides m²-1; both m and m|V| are integral x-coordinates on the Pell equation with coefficient (m²-1)/b². For its fundamental-unit sequence, x_j divides x_l only when l is an odd multiple of j. The corresponding y-coordinate divisibility forces b|a and b=1. The divisibility statement follows by reducing l modulo 2j and reflecting into 0<=r<=j, where 0<x_r<x_j for r<j.

Once tau,g are integral, y is rational. If Baux is nonzero, f is rational with integer square D and hence integral, so V=vaux f-b is an integer and the lemma applies with m=|S|. If Baux=0, apply it directly with V=-b. In both cases y is integral.

Define gamma=(g-P0)/H. The linear identity gives

    t=3W tau+K gamma+y.

Thus K gamma is integral, and H gamma is integral by definition. Because gcd(K,H)=1, gamma is integral.

Now T=0 would imply vaux=Baux=0 and

    (Q-1)(y²-b²)=b²-1>0.

Integral y then has |y|>=b+1. But Q-1>=b by 1<b<Q, so the left side is at least b(2b+1)>b²-1, contradiction. Therefore T and Baux are nonzero and the recovered f is well defined.

We have restored all normalized source relations with signed h,T,f,tau,y,gamma, odd i, square w, six positive guarded ports, and nonzero odd s. The odd-scale theorem discussed in Section 14.6 excludes s<0 and supplies the authentic blank compiler.

## The 25-integer small-weight reduction

Retain gamma and the main norm

    Nmain=(P0+H gamma)²-Delta c².

Use the same normalized strong and auxiliary definitions, but put

    M=I²+T²,
    Caux=d(t²+M²A)-e,
    U=Caux²+D Baux²-4d²t²M²A,
    N25=U²-D(2Caux Baux)².

The equation is

    Nmain Nk Nt(1+N25)-1=0.                           (25)

The main negative unit is excluded modulo four since Delta is 0 or 3 mod 4. Also N25 is a square modulo four. Thus Nmain=1, N25=0, and Nk=Nt are common units. The main equation excludes X=0 modulo H before any deleted root is restored.

### Main Pell rank at both signs of s

Let Z0=|Y|, E0=XZ0, B0=|a+2|. The main Pell classification gives |c|=psi_B0(p), |P0+H gamma|=chi_B0(p), p>=1. Since |c|>1, p cannot be 1.

If p=2, c=2(a+2), for either sign of Y. For the positive main root chi_B0(2),

    chi_B0(2)-ac=H+4,

so X=4 modulo H. But 16<=X<|H|, impossible. For the negative main root,

    4(-chi_B0(2)-ac)=-(4(a+2)-5)(4(a+2)+1)-1,

so 4X=-1 modulo H. Since 0<4X+1<|H|, this is likewise impossible. Therefore p>=3 and

    |c|>=4B0²-1>4E0²-1.

Together with |c|<k(Z0+1), this yields k>(7/2)X²Z0. In particular

    ell=XkZ0²>(7/2)E0³, A>ell².

The proof does not assume s>0, h>=0, or the existence of the eliminated first root.

### Signed small-weight domination

Let lambda=(16/15)^4. The elementary estimates B0<(16/15)E0, |c|<(16/15)kZ0, R+1<E0, D<B0²I², and |c|/I²<1 give

    D c²/I²<lambda A,
    b²/I⁴<(4lambda/49)A.

Because M²>=4I²T² and M²>=I⁴, including at T=0,

    (D vaux²+b²)/M²
       <lambda(1/4+4/49)A <(9/20)A.

    Since Q>=10, d>=9Q/10. Consequently

    dAM²>2Q(D vaux²+b²),
    Caux>Q(D vaux²+b²)+1>|Baux|sqrt(D).

If t=0, N25=(Caux²-D Baux²)²>0, contradiction. Thus t is nonzero. If T=0, then Baux=0 and N25=0 gives a rational root tau=Caux/(2dtM) with tau²=A, so tau is an integer. Then y=t-M tau is integral and satisfies the impossible gap equation from Section 14.3.4. Hence T and Baux are nonzero.

Now define

    f=-U/(2Caux Baux),
    tau=(Caux+Baux f)/(2dtM),
    y=t-M tau.

The resultant first gives f²=D, then tau²=A. Both rational roots are integers, and y is integral. Expanding yields dy²=e-Baux f and therefore the exact source auxiliary relation. The signed odd-scale compiler then applies as before.

## The 26-integer two-root equations

Retain gamma and f. Define

    Q0=Delta(f²-1), d0=Q0-1,
    V=c(Tf-1)-Rf², e0=Q0 V²-1,
    U0=d0(t²+A)-e0,
    N26=U0²-4d0²t²A.

For normalized strong use Ns=f²-Delta I²; for ordinary strong use Ns=1+I²-Q0. In either case the single equation is

    Nmain Nk Nt Ns(1+N26)-1=0.                         (26)

The main and normalized negative units are impossible modulo four. For ordinary strong, Ns=-1 would give I²-Delta(f²-1)=-2. If Delta=0 mod4 this is impossible; if Delta=3 mod4, checking square residues 0,1 also gives no residue 2. Thus Ns=1 for both versions. The norm guard is a square modulo four, so N26=0 and Nk=Nt are common units.

The main equation again excludes X=0 and supplies the rank p>=3 bound of Section 14.4.1. In the normalized version,

    Q0=Delta² i² c⁴>A,

directly from Delta>(X Z0)² and |c|>k(Z0-1), or from the stronger ordinary inequality below.

In the ordinary version Q0=I²=i²c⁴. By k>(7/2)X²Z0>4X and Z0>=4096,

    c²>k²(Z0-1)²>(k²Z0²)/2>2XkZ0²=2ell.

Also ell>k>=2, so

    A=1+ell²+ell k<4ell²<c⁴<=I²=Q0.

Thus 1<A<Q0 in both versions. If t=0, N26=0 forces d0 A=e0, or Q0(A-V²)=A-1. This contradicts 0<A-1<Q0. Therefore t is nonzero, and

    tau=U0/(2d0 t), y=t-tau

are rational with tau²=A, so tau and y are integers. Expanding gives d0 y²=e0. These exactly restore the first and auxiliary source norms. The ordinary or normalized signed odd-scale theorem applies. This proof handles the previously missing zero-t branch without demanding positive t or positive s.

## Excluding negative s and canonical completeness

The needed source theorem is pinned package 23/proofs/ODD_SCALE_27_PROOF.md. Its negative-s exclusion applies to both ordinary and normalized strong equations and to signed roots, h,T,gamma. The newly reconstructed equations meet all of those hypotheses.

For clarity, the exclusion does not merely assert that negative s is unnatural. With Z0=-Y, B0=(X+1)Z0-2 and c0=-c, first and main Pell classification, the signed auxiliary step-down congruences, and no-wrap bounds recover the main rank p=R and index R=2r0+1. The Pell growth ratio then gives Z0>2^R. The two possible main-root signs respectively imply X+2^R=0 modulo H or X2^R=1 modulo H. The strict inequalities

    0<X+2^R<|H|, 1<X2^R<XZ0<|H|

exclude both signs. Hence s>0. The same rank argument forces the common index/transport units to +1. The existing signed blank compiler now recovers the exact native tableau and calibrated refutation machine.

Conversely, a canonical accepting blank tableau has q=2^t, with t odd after the established powers-of-five padding; R is odd, so w=2^R/q is a square. The population identity of package 23 gives popcount(R)=3t+2. The half-binomial identity gives v2(Y)=popcount(R)-2=3t, so s=Y/q³ is positive and odd. The canonical normalized strong multiplier i is odd, as in package 14. No new divisibility condition on this multiplier is imposed.

For the ordinary 26-integer variant use i_ordinary=Delta i_normalized. Canonical Y is even, so a is even and Delta=a²+4a+3 is odd. Thus i_ordinary is still odd. All other canonical witnesses are unchanged.

Define the new free coordinate by

    t=3W tau+K gamma+y                  for (24),
    t=M tau+y                          for (25),
    t=tau+y                            for (26).

These integers make the respective norm vanish. All remaining source factors are one, all six positive ports have Pos representations, and both odd parameters and the square scale have the stated integer representations. This proves completeness without an extra Pell period, H-divisible multiplier, or positivity assumption on t.

## Uniform exact degree proofs

Use weight two on J,F,alpha,z,eta,zeta,w; weight one on i,s,h,T,t,gamma,f. The substitutions have precisely these leading weights. Let q0=beta J and k0=eta+zeta. Key degrees are

    a,H:11; c:9; ell:20; A,G:40; Delta:22;
    R:8; Nk:12; Nt:4; I:19; D:60; Q,d:82; b,W:68.

For (24), K,uweight have degree 79 and Z has degree 99. The four leading linear forms Z-uweight tau-Kg are scalar multiples -3,+3,-1,+5 of K_top ell_top. The H²e term has degree 240, below d times the linear square, of degree 280; H⁴Baux²D has degree 424, below the preceding square of degree 560. Therefore

    N_top=45⁴ d_top⁸(K_top ell_top)^16, deg N=2240.

The product degree is 2240+12+4=2256. After the actual substitutions, the coefficient of

    J_a^1578 h r^48 eta_a^224 u^194 v^209 z_a²

is +2^305 3^8 5^4 beta^789. It is nonzero uniformly for beta>0, and the exponent sum is2256. Thus the result is not merely an upper bound or a sampled generic degree.

For (25), M has degree 38, e has degree 218, and d M² A has degree 198. Thus the unique highest part of Caux is -Q_top b_top², U has degree 436 with top Caux_top², and N25 has degree 872 with top U_top². The competing subtracted term has degree 816. The main norm degree is32, not its naive bound40: the cancellation leaves highest term 8 gamma a_top² c_top. Hence the product degree is872+32+12+4=920. The coefficient of

    J_a^640 h gamma r^24 eta_a^98 u^70 v^84 z_a²

is +2^111 beta^320.

For (26), Q0,d0 have degree 24, V has degree 11, e0 has degree 46, and U0 has degree 64, uniquely from d0 A. Thus N26 has exact degree 128. The strong factor has degree 60 normalized or38 ordinary. Adding the main,index,transport degrees32,12,4 gives236 normalized or214 ordinary. The corresponding coefficients are

    [J_a^160 h gamma f⁴ r² eta_a^18 u^26 v^22 z_a²] = -2^27 beta^80,
    [J_a^144 h gamma f⁴ r² eta_a^18 u^22 v^20 z_a²] = +2^25 beta^72.

All displayed monomials use one coordinate from each relevant positive-surjection triple. These explicit nonzero coefficients prove exact degree for every authentic beta>0.

## Verification and limitations

`build_odd_scale_family.py` and `check_odd_scale_family.py` were newly written locally. Imported programs were not executed. Earlier emitted circuits were read as inert JSON. The checker independently evaluates the 24-variable norm by four-factor multiplication in a rank-four free algebra, not by replaying the optimized pair formula as its reference. Each circuit passed 120 signed integer formula comparisons, all-port/all-gate liveness, two exact modular degree/leading-coefficient checks, and guard parity. The common signed bounds were checked on 2160 finite cases, including w=0, T=0, negative s and both signs of i.

These finite checks support arithmetic identities and ledger accuracy; they do not replace the unbounded Pell classifications, rank step-down, population identity, compiler correctness, machine calibration, or rational saturation proofs. No actual accepting K215 computation is produced or asserted.

## A sharper 24-integer separator: degree 2240 at the same165 gates

The strict inequality already proved in Section 14.3.3 gives

    |K|sqrt(G)+|H|W<2|P|sqrt(A).

Therefore replacing uweight=3P by uweight=2P preserves every soundness argument, with t=2W tau+K gamma+y in completeness. The separately frozen circuit is `integer24_sharp_pair_norm165_degree2240.json`; the previous 3P circuit remains for comparison and provenance.

One leading formal branch now cancels, which genuinely lowers the exact degree rather than merely weakening an upper bound. This can be computed in the formal Laurent-series field obtained by scaling every actual integer input by a common indeterminate. Choose the square-root branches with leading terms ell and ac. These formal expansions satisfy

    sqrt(A)=ell+terms of weighted degree at most2,
    sqrt(G)=ac+terms of weighted degree at most9,
    ac-ell=kY²+eta E+eta Y.

The last expression has unique highest part k_top Y_top² of degree 16. The exceptional branch is

    Ht+K(P0+sqrt(G))-2P sqrt(A)
      =K[ac+X+sqrt(G)-2sqrt(A)]+2sqrt(A)+Ht.

Its unique top is 2K_top k_top Y_top², of degree 95. The other three linear branches have degree 99 and respective leading multiples -2,2,4 of K_top ell_top. In every branch the d times linear-square term still strictly dominates H²e, and its square strictly dominates H⁴Baux²D. Multiplying the four branch leaders gives

    N_top=2^20 d_top^8 K_top^16 ell_top^12 k_top^4 Y_top^8,
    deg N=2224.

This formal expansion is only a device to compute the leading polynomial form; the norm itself remains a literal integer polynomial with no division or algebraic-number input.

The product has exact degree 2224+12+4=2240. The coefficient of

    J_a^1570 h r^48 eta_a^224 u^186 v^209 z_a²

is +2^325 beta^785, nonzero for every beta>0. Independent exact modular evaluations confirm this degree and coefficient. The sharper form is the preferred24-integer entry; its165 gates still consist of 96 multiplications and 69 additions/subtractions.


# Appendix C. Complete quartic reduction


## Result and dependency boundary

The pinned package-18 quartic32 source at ProveIt commit
`ae3007ca4467011e0e051c84acb4a1dd13971b0e` has 32 positive witnesses and
23 quadratic equations. One packing register is unnecessary. The following
construction has 31 positive witnesses, 22 quadratic equations, and an exact
quartic sum of squares. Its fixed compiler ports are unchanged.

This is an exact algebraic, tuplewise reduction of that source. Composed with
its ordinary Pell/compiler proof and K215 calibration, ZFC proves that the
new polynomial has no positive solution if and only if Con(ZFC). This is not
an end-to-end proof-assistant certificate. No truth of Con(ZFC), consistency
of ZFC, or global minimality is assumed or established.

The source's literal JSON and its hashes are preserved in `SOURCE_LEDGER.json`.
No upstream code was executed. Our `build_arithmetic.py` is newly authored.

## Exact equations

All 31 coordinates are strictly positive integers:

    J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,
    N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta.

The four fixed ports beta, K0, MC and MF must be one complete authenticated
blank compiler tuple. MF is the shifted source mask. All coefficients remain
fixed integers, not quantified inputs. The following are affine abbreviations:

    q=beta J+1, k=eta+zeta, H=4a+3, C=q-F-alpha.

The 22 equations are:

    L=q^2-1,
    N=q(L+1),
    X=wq,
    a=E+sN,
    E=X(a-E),
    c=k(a-E)+eta,
    P=E(c-eta)+k,
    tau^2=P(P-k)+1,
    D=X+ac+gamma H,
    Delta=a^2+H,
    C2=c^2,
    D^2=Delta C2+1,
    k=jc-V+1+hE,
    jc-V=(q-F)(N-q)-CL+(MC+q MF)J,
    (K0+w)C+(q-F)-z(q-1)=1,
    F2=f^2,
    V=of-c,
    g=y^2-V^2,
    I=i C2,
    Baux=I^2,
    Baux=Delta(F2-1),
    y^2-Baux g=1.

Every displayed residual is quadratic after the four affine abbreviations
are expanded. Let r_1,...,r_22 be the left sides minus the right sides in this
order. The single polynomial is

    Q31 = r_1^2 + ... + r_22^2.

Its literal sparse data, including all coefficient-port exponents, are in
`quartic31.json`; `quartic31_expanded.json` contains the 306-term expanded
sum of squares. Because tau occurs only in r_8 and with term tau^2, the
coefficient of tau^4 in Q31 is exactly 1. The degree is therefore exactly 4
for every admissible tuple of fixed coefficients.

IMPORTANT: z here is the OLD positive transport coordinate, as in the pinned
package-18 quartic source. It is not the shifted z of package-22 retained59.
No tuple components or transport conventions have been spliced.

## Exact zero-set equivalence and sign obligations

The source has an additional positive variable G and the equations

    G=(q-1)(q-F)+alpha=q(q-F)-C,
    jc-V=LG+(MC+q MF)J.

The new packing expression obeys the polynomial identity

    L[q(q-F)-C] - [(q-F)(N-q)-CL]
      = (q-F)[q(L+1)-N].

Thus it agrees with LG whenever the retained N equation holds.

Forward direction: forget G from any positive source solution. The displayed
identity gives the new packing equation; every other equation is unchanged.

Reverse direction: a new positive solution has q>1. Its unchanged transport
identity gives

    (K0+w)C = F+(z-1)(q-1)>0.

Since K0+w>0, C>0. Define

    G=q(q-F)-C=(q-1)C+q alpha.

This is a strictly positive integer. Restoring this single coordinate now
satisfies both removed source equations, by the exact identity. All other
coordinates are untouched. The two maps are inverse: this is a bijection of
positive zero sets, not only an existence reduction.

No new negative-root or unit-sign branch is introduced. All original source
roots, quotient coordinates and equations remain. The only restored variable
is G, whose strict positivity was proved above. In particular alpha is NOT
eliminated or relaxed; all original outer bounds and native-window hypotheses
are inherited unchanged.

## Nonnegative normalization for the nine-variable compressor

Replace each of the 31 positive coordinates x by n_x+1. This preserves degree
4 and gives a polynomial over 31 nonnegative unknowns with the same existence
condition. At all positive coordinates equal to 1, the fifth residual is

    E-X(a-E)=1.

Hence the shifted polynomial is strictly positive at the all-zero tuple,
independently of the four fixed coefficients. This preserves the normalization
condition required by the pinned nine-variable compressor. Its witness-count
parameter can therefore be changed from 32 to 31; the nine-variable audit
separately verifies the resulting coefficient and degree arithmetic.

## Operation counts and reproduction

The explicit equality-comparison circuit in `quartic31_system.json` has
65 binary gates: 33 multiplications and 32 additions/subtractions. Equality
comparisons are free, exactly as in the source's operation convention. Every
multiplication by a coefficient or small integer is charged. Every gate,
witness and coefficient port is live.

The complete SOS circuit in `quartic31_circuit.json` has 130 gates:
55 multiplications and 75 additions/subtractions. Its 65 additional gates are
22 residual subtractions, 22 squares and 21 additions. These are explicit
upper bounds from literal evaluators, not operation-minimality claims.

Run `python3 build_arithmetic.py` in this directory. The script checks the
packing identity as a zero sparse polynomial, compares every unchanged
residual with the pinned source's literal sparse terms, verifies all 22 new
residual degrees and exact quartic degree, checks the tau^4 and normalization
certificates, verifies the comparison and residual circuits symbolically,
checks gate/input liveness, and performs 1000 signed integer evaluations of
the packing identity. These are algebraic audits, not a search for a solution
or a substitute for the inherited unbounded arithmetic/compiler proof.


# Appendix D. Complete nine-variable construction


## Result and scope

At the pinned ProveIt revision `ae3007ca4467011e0e051c84acb4a1dd13971b0e`, combine the Jones nine-witness reduction with the new 31-positive-variable, 22-quadratic parent and the complete compact943 compiler tuple. The resulting equation is an ordinary integer polynomial in exactly nine nonnegative integer unknowns. Its final circuit is `nu31/nine_compact_magnitude_tight.json`.

* Exact total degree: `120724 * 5^32 + 366 = 2810824662446975708007812866`.
* Live binary operations: 1,840 = 715 additions + 22 subtractions + 1,103 multiplications.
* Variable leaves: nine. Fixed leaves: 404 = 402 weighted coefficient constants, z, and y.
* The four underlying compiler integers are actual materialized integers, totaling 5,312,269 raw bytes or 20,260 deterministic-gzip bytes.
* The new index constant is the actual integer z=2^45933757. Its materialization occupies 5,741,720 raw bytes or 5,613 gzip bytes. Its SHA-256 is `d2b21c2c280cd06b3f233616ce4add5fd554f3d9178baa4ef7923826a3b1e100`.
* The 402 weighted coefficients and the much larger index y are bounded explicit recipes, not materialized integers in this package. No coefficient is an existential parameter.

This is an ordinary mathematical proof using the previously identified native/Pell compiler, literal K215 calibration, and Jones arithmetic theorems. The new algebra and finite audits are not a new end-to-end proof-assistant theorem. They neither decide consistency nor supply a halting/refutation witness.

## Coherent compiler binding and the parent quartic

The authoritative binding is the COMPLETE compact943 tuple, not the historical t-shape default metadata carried by the inert source:

    beta = B_native-1;
    K0 = K = DC+B_native*DR;
    MC = compact data mask;
    MF = MF_source = MF_native+B_native-1;
    B_native = 2^(5^10).

All four values must come from the same compact943 instance. `nu31/COMPACT_COEFFICIENT_BINDING.json` and the round-three compiler proof give the finite 943-tile recipe, exact masks, geometry, and verified bytes. In particular the verified interface includes the no-carry bounds, balanced mask populations, two-band rotation separation, unique anchor synchronization, mod-5 unit 2DC-DR=4, actual-rank dummy control, positive slack, and canonical odd/square-scale completeness. MF is never the unshifted native mask. The machine table and language are the same exact K215 blank-halt language, not a new machine-input parameter.

The old 32-variable source already uses exactly this abstract four-port arithmetic interface. The new parent removes its register G. Write, in this parent paragraph only,

    q=beta J+1, C=q-F-alpha, G=(q-1)(q-F)+alpha.

Its retained quadratic equation N=q(L_parent+1) implies

    G=q(q-F)-C;
    L_parent G=(q-F)(N-q)-C L_parent.

Thus the G definition and old packing equation are replaced by the single quadratic packing equation

    jc-V=(q-F)(N-q)-C L_parent+(MC+q MF)J.

Every other residual is unchanged. Conversely recover G from its displayed formula. G is positive: the literal retained transport equation gives

    (K0+w)C+(q-F)=1+z_parent(q-1)>=q.

If C<=0, the left side is at most q-F<q, a contradiction. Hence C>0, q-F=C+alpha>0, and G=(q-1)(q-F)+alpha>0. This establishes both directions on the required positive domain, with no change of the source quotient convention. The new system has 31 positive variables and 22 quadratic residuals r_j.

Define P31(x,n)=sum_j r_j(n+1)^2, independent of its dummy input x. The fifth residual is E\*X+E-a\*X and equals 1 when all positive coordinates equal 1. Therefore P31(x,0)>0 for every x, independently of the four compiler values. Its degree is exactly four since the coefficient of tau^4 is 1. The literal sparse parent is `../arithmetic/quartic31.json`; its SHA-256 before any nonalgebraic metadata editing is `1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.

The parent-to-K215 equivalence remains the imported arithmetic/compiler theorem, now transported by the exact G elimination. K215 blank halting is equivalent to finite syntactic ZFC refutability by the identified literal-machine calibration. Those ordinary arguments are formalizable in ZFC; this package does not claim their rechecking inside a newly built Lean/Rocq kernel.

The Jones parameter nu counts parent-quartic witness variables. It is now 31, not 9. The unrelated native fixed radix B_native=2^(5^10) cannot justify setting nu=9. A normalized quartic in nine witnesses and its admissible index would be needed for that substitution. No such reduction is claimed.

## Explicit index without an uninstantiated recursive-enumeration index

Set nu=31 and L=5^32. Expand P31 in the 32 coordinates (dummy x plus 31 witnesses). For alpha in N^32 with |alpha|<=4 let p_alpha be its ordinary coefficient and put

    c_alpha=(4-|alpha|)! * product(alpha_j!) * p_alpha;
    expo(alpha)=sum_(j=0)^31 alpha_j*5^j.

There are exactly 402 nonzero symbolic coefficient records, each explicitly a small polynomial in (beta,K0,MC,MF). They are listed in `nu31/COMPACT_CONSTANTS.json`. Unlisted c_alpha are zero. The independent expansion has 675 terms when the four ports are retained symbolically. All exponent powers in the records are ordinary fixed nonnegative integers.

The authentic port bit lengths, in this order, are

    (9765625,13201251,9765625,9765626).

For each record c_alpha=sum_t a_t product port_j^(e_tj), define the completely explicit integer upper bound

    H_alpha=sum_t |a_t| * 2^(sum_j e_tj * bitlength(port_j)).

The actual absolute coefficient is at most H_alpha. Exact finite integer arithmetic verifies, for every one of the 402 records,

    H_alpha+1 < 2^45933757.

The sparse powers-of-two certificate is `nu31/INDEX_BOUND_CERTIFICATE.json`; it does not require materializing any quartic coefficient. Set

    z=2^45933757;
    u=sum_(j=1)^31 (2z)^(5^j);
    y=sum_(|alpha|<=4) (z+c_alpha)(2z)^(L-expo(alpha));
    e(T)=sum_(|alpha|<=4) (z+c_alpha)T^(L-expo(alpha)).

The y sum has exactly binomial(36,4)=58,905 terms. All digits z+c_alpha lie strictly between 1 and 2z, and the exponent positions are distinct by base-five uniqueness. Hence y is a positive integer, 2(2z)^L <= y < (2z)^(L+1). In particular it has at most 45,933,758\*(5^32+1) binary digits. The unused u is explicit as well; it is not a polynomial leaf or unknown.

These definitions satisfy precisely `Jones1982.Index 31 P31 z u y`: z is a power of two, |c_alpha|+1<z, and u,y are the specified lpoly/epoly evaluations. P31 is normalized, has degree <=4, nu>=1, and the chosen input is x=1>0. These are exactly the hypotheses of `Jones1982.Nine.wset_iff_nine`, rather than a misuse of the public generic theorem whose convenience proof passes through a 58-variable quartic.

## The literal nine-coordinate equation

The nine unknowns are

    epsilon,g0,h0,s0,w0,phi,i0,j0,n in N.

Set g=g0+1, h=h0+1, s=s0+1, w=w0+1, i=i0+1, j=j0+1. Every symbol below is only a polynomial abbreviation. Define

    b=y+1+epsilon, B=b^5, q=B^L;
    ell=sum_(r=1)^31 B^(5^r), lambda=sum_(r=0)^(4L-1) B^r;
    e=e(B), theta=B-2z, N=q^16, Gcap=32b B^(5^31);

    R=[g+e q^3+ell q^5+
       (2(e-z lambda)(1+B+g)^4+lambda B+lambda B q^4)q^7](N^2-N)
      +[q^3-b ell+ell+theta lambda q^3+(B-2)q^8](N^2-1).

Continue with exactly the Jones ratio expressions:

    U=N^2 w, Y=N^2 s, M=R Y, P=2M^2 U;
    K=R+1+h(P-1), A=M(U+1), B1=2R+1, W1=bw;
    C=B1+W1+phi, J=4A-5, Q=3W1 C-2(W1^2-1);
    D=(A^2-1)C^2+1, E=i J D C^2, F=(A^2-1)E^2+1;
    G1=A+F(CD+1-A), H=B1+jC, I=(G1^2-1)H^2+1;
    a0=(P^2-1)K^2+1, a1=DFI;
    d=(JF)^2, c=(QF+J(H-C))^2;
    m=K^2 Gcap-4(C-KY)^2 Gcap-8gK^2.

The d,c here are respectively the divisor and dividend, not parent coordinates or coefficient records.

The new magnitude companions are

    deltaR=32 z lambda g^4 q^7 (N^2-N), Rbar=R+deltaR;
    Kbar=Rbar+1+h(P+1), Abar=Rbar Y(U+1);
    Cbar=2Rbar+1+bw+phi, Jbar=4Abar+5;
    Dbar=(Abar^2+1)Cbar^2+1, Ebar=i Jbar Dbar Cbar^2;
    Fbar=(Abar^2+1)Ebar^2+1;
    Gbar=Abar+Fbar(Cbar Dbar+1+Abar), Hbar=2Rbar+1+jCbar;
    V0=(P+1)Kbar+2;
    V1=((Abar+1)Cbar+1)((Abar+1)Ebar+1)((Gbar+1)Hbar+1)+1.

Finally define

    Omega=d(2m-1);
    Theta=dn+c-Omega(c+V0 V1);
    F9=(Theta^2-Omega^2(a0+V0^2 a1))^2-4 Omega^4 V0^2 a0 a1.

The single requested equation is F9=0. Every exponent in the entire display is fixed. There are no divisions, radicals, variable exponents, or additional quantified variables in the equation.

## Noncircular magnitude bounds, including negative packed ranks

All following inequalities hold on EVERY natural assignment of the nine inputs, before any zero or square condition is assumed. The admissible index gives b>=2, B>=4, B>2z, and e(B)>0. Since the exponents in ell are a subset of 0,...,L-1,

    ell <= (q-1)/(B-1), and b<=B-1, hence b ell<q.

Thus the entire right bracket in R is positive. Put u0=B+1. The elementary convexity inequality (u0+g)^4<=8(u0^4+g^4) holds for nonnegative u0,g. Also

    16z(B+1)^4 < 128 B^5 < B^9 <= B q^4,

using B>2z, B>=4, and L>=2. The positive lambda B q^4 term in the left bracket therefore absorbs 16z lambda(B+1)^4. Consequently

    R+16 z lambda g^4 q^7(N^2-N)>=0.

The added term is nonnegative, so Rbar=R+32 z lambda g^4 q^7(N^2-N) dominates both R and -R. Thus Rbar>=|R| without assuming R positive. This is the key improvement over simply replacing every minus sign by a plus sign.

P=2M^2U is nonnegative. The displayed companion formulas then give, successively,

    Kbar>=|K|, Abar>=|A|, Cbar>=|C|, Jbar>=|J|,
    Dbar>=|D|, Ebar>=|E|, Fbar>=|F|,
    Gbar>=|G1|, Hbar>=|H|.

These follow only from triangle inequalities and nonnegative products. For real a,b,

    sqrt(|(a^2-1)b^2+1|) <= (|a|+1)|b|+1.

Indeed the squared right side exceeds (a^2+1)b^2+1, which already bounds the absolute radicand. Therefore V0,V1>=2 and

    sqrt(|a0|)<=V0-1, sqrt(|a1|)<=V1-1.

Unlike the baseline all-integer majorant lemma, this improved weight lemma is asserted only on the natural input domain with the specified valid index. That is exactly the domain needed by the nine-witness equivalence. It never assumes the desired margin, divisibility, squarehood, or R positivity.

## Exact sign/root finalizer proof

J=4A-5 is a nonzero integer. Also F cannot vanish: if (A^2-1)E^2+1=0, then (1-A^2)E^2=1 forces A=0 and E=+/-1; but E=iJDC^2 is then divisible by 5, impossible. Hence d=(JF)^2>0 and c>=0, while Omega=d(2m-1) is nonzero at every integer assignment.

    Choose formal complex roots r0^2=a0,r1^2=a1. Direct multiplication yields

    F9=product_(sigma,tau in {-1,1}) [Theta-Omega(sigma r0+tau V0 r1)].

If F9=0, absorb the signs of a vanishing factor into r0,r1. Then s\*=Theta/Omega=r0+V0r1 is rational. If s\*!=0, the identity 2s\*r0=s\*^2+a0-V0^2 a1 makes both roots rational. If s\*=0, |r1|=|r0|/V0<1, so the integer |a1|<1, forcing a1=a0=0. In either case the roots are rational, hence integers since their squares are integers. This proof covers negative candidate radicands, zero roots, and repeated square classes.

Set Z=c+V0V1+r0+V0r1. The established root bounds give Z>=c+1>0. The vanishing factor reads

    dn+c=d(2m-1)Z.

It implies d divides c and m>0. Conversely, if a0,a1 are squares, d divides c, and m>0, choose their integer roots and define

    n=(2m-1)Z-c/d.

This is a nonnegative integer (indeed >=1), and its factor vanishes. Finally (JF)^2 divides (QF+J(H-C))^2 iff JF divides QF+J(H-C). Thus existential elimination of n gives EXACTLY the original two square tests, one divisibility test, and positive margin.

The source theorems `Nine.reduced_of_mem`, `Nine.mem_of_reduced`, `Nine.ratio_complete`, and `Nine.ratio_sound` retain their literal arithmetic expressions. Only the final weights and the witness n change. Therefore the new F9 has a natural zero iff P31 has one, iff the compact native compiler accepts a blank K215 computation, iff there is a finite ZFC refutation. Negating gives, provably by the stated ordinary mathematics in ZFC,

    (there is no natural nine-tuple with F9=0) iff Con(ZFC).

## Exact degree, not merely a naive upper bound

Write L=5^32. The dominant R term is +lambda B q^4 q^7 N^2, of degree 235L; the apparently large negative quartic term is lower degree. Selected ordinary degrees are

    R:235L; P:950L+3; K:950L+4; A:555L+2;
    D:1580L+4; E:2605L+7; F:6320L+18;
    G1:8135L+22; H:235L+1; I:16740L+46;
    a0:3800L+14; a1:24640L+68;
    d:13750L+40; c:13110L+40; m:2221L+11;
    V0:1900L+7; V1:12320L+34;
    Omega:15971L+51; Theta:30191L+92.

A naive degree calculation misses an important cancellation. Set eta_degree=20L+1. On the all-coordinates-equal-t specialization, R has leading coefficient 1, while deltaR has degree 215L-1 and leading coefficient 32z. Thus Rbar/R first differs by relative leading term 32z\*t^(-eta_degree).

Relative companion defects for A,C,J,H have multiplier 1, for D multiplier 4, E multiplier 7, F multiplier 16, and G1 multiplier 21. The three factors in V1 consequently have total relative defect (2+8+22)=32 times that first R defect. The Pell subtractions of 1 have smaller degree. Since the leading coefficient of a1 is 2^46,

    degree(V1^2-a1)=24620L+67;
    leading coefficient(V1^2-a1)=2^57 z.

For a fully polynomial certificate, expand differences of products by telescoping, e.g. `xbar^2-x^2=(xbar-x)(xbar+x),` rather than dividing polynomials. The independent auditor supplies that cancellation-free identity for every companion, the three factors, and V1^2-a1.

Put E0=dn+c-Omega c, so Theta=E0-Omega V0V1. Then

    Theta^2-Omega^2(a0+V0^2a1)
      =E0^2-2 E0 Omega V0V1
       +Omega^2 V0^2(V1^2-a1)-Omega^2 a0.

The third term alone has highest degree 60362L+183 and leading coefficient 2^137 z. The cross term has lower degree 59272L+183. The final subtracted norm term 4Omega^4V0^2a0a1 has degree 96124L+300, below twice 60362L+183. Thus

    degree F9 =120724L+366;
    leading coefficient F9(t,...,t)=2^274 z^2>0.

This nonzero leader proves exactness after the authentic fixed constants are substituted. The proof does not assume a Diophantine solution and does not treat fixed constants as variables.

## Circuit savings and verification boundaries

The sparse coefficient correction is evaluated by sorted-exponent Horner arithmetic. Powers share a radix-five ladder p_j=B^(5^j) and cached equal-digit runs. The baseline digit sum is

    B^(5^nu) h4(B^(5^nu), B^(5^nu-1), ..., B^(5^nu-5^nu)),

with ascending complete-homogeneous recurrence. Finally

    lambda=product_(j=0)^nu (1+p_j+p_j^2+p_j^3+p_j^4) * (1+q)*(1+q^2).

These are exact identities, with no divisions in the output circuit. They account for most of the operation-count improvement. Fixed exponentiation is fully expanded into binary multiplications, and squaring and scalar multiplication are charged. Shared reuse is free. The construction/materialization cost of fixed integer constants is not charged as variable arithmetic; all constants nevertheless have bounded definitions.

Independent diagnostics include exact rebuilding of all shifted and weighted coefficients, the strict index bound, all four compiler-byte hashes/bit lengths, literal 58,905-term index-baseline comparisons, 752 actual-instance named-node comparisons across four primes and four input tuples, 512 companion/root-bound assignments, and 576 constructed finalizer witnesses. The degree certificate also checks cancellation-free algebra independently. These are finite checks of the definitions, not an empirical proof of the unbounded semantic equivalence.


# Appendix E. Independent nine-variable audit


## Audited final candidate

File: `../nine/nu31/nine_compact_magnitude_tight.json`.

- Nine nonnegative supplied unknowns.
- 1,840 live binary operations:715 additions,22 subtractions,1,103 multiplications.
- 404 fixed leaves:402 explicitly defined weighted coefficients, plus z_star and y_star.
- Exact `degree:120724*5^32+366=2810824662446975708007812866.`
- Uniform all-unknowns=t leading `coefficient:2^274*z_star^2,` nonzero because z_star is a positive power of 2.
- Parent quartic:31 positive witnesses,22 quadratic residuals; after positive shifts,675 symbolic terms and 402 weighted coefficient records.

Independent source-to-coefficient and degree ledger: `NU31_INDEPENDENT_AUDIT.json`.
Independent semantic check of the quartic elimination: `QUARTIC31_INDEPENDENT_REVIEW.json`.
The compact compiler tuple transfer is a separately audited prerequisite.

## The reduced quartic is an exact positive zero-set equivalence

I independently matched all 21 unchanged residuals against package 18's pinned32-variable source after deleting its G coordinate. Only its old residuals14 and 15 are affected. The replacement is justified by

`L[q(q-F)-C]-[(q-F)(N-q)-CL]=(q-F)[q(L+1)-N].`

On every new positive solution, unchanged transport gives

    (K0+w)C=F+(z-1)(q-1)>0.

Therefore C>0 and the restored integer `G=q(q-F)-C=(q-1)C+q*alpha` is strictly positive. The forward and reverse coordinate maps are inverses. This is a bijection of positive zero sets, not a heuristic elimination that drops a sign constraint. The old transport coordinate z is retained unchanged.

The normalization residual remains E-X(a-E), which equals1 when all positive variables equal1. Shifting31 coordinates by+1 therefore supplies the exact Normalized hypothesis for the nine-variable compressor at nu=31. The fixed dummy input remains1. The change nu32->31 is justified by this witness reduction; it is unrelated to the backend compiler's radix exponent.

## Tight unconditional majorant for the packed R

In the Jones notation, let g=g0+1, B=b^5, q=B^L, N=q^16, lambda=sum_{r<4L}B^r, and ell=sum_{j=1}^nu B^(5^j). The admissible index and natural domain imply B>2\*z_star, B>=4, L>=2, e>0 and theta=B-2\*z_star>0.

Set

`T0=16*z_star*lambda*g^4*q^7*(N^2-N),`
    deltaR=2*T0,
    Rbar=R+deltaR.

Then Rbar>=|R| without assuming the final equation has a solution.

For the proof, (u+g)^4<=8(u^4+g^4) for nonnegative u,g. Thus the negative piece `-2*z_star*lambda*(B+1+g)^4` of R's first bracket is bounded below by `-16*z_star*lambda*((B+1)^4+g^4).` Adding T0 cancels the g^4 part. The positive lambda\*B\*q^4 term absorbs the other part because

    B*q^4 >= B^9 > 128*B^5 > 16*z_star*(B+1)^4.

The middle inequality follows from B>=4; the final strict inequality follows from 2\*z_star<B and B+1<2B. Every remaining first-bracket term is nonnegative.

For the second bracket, ell is a subsum of 1+B+...+B^(L-1), and b<=B-1. Hence b\*ell<q, so q^3-b\*ell>0. Its other terms are nonnegative. Thus R+T0>=0. As T0>=0, R+2\*T0>=|R|.

All subsequent magnitude companions follow by triangle inequality. With bars as in the construction,

    |A|<=Abar, |C|<=Cbar, |J|<=Jbar, |D|<=Dbar,
    |E|<=Ebar, |F|<=Fbar, |Gp|<=Gbar, |H|<=Hbar,
    |K|<=Kbar.

P is nonnegative even when R is negative, since P=2(RY)^2U and U>0. This justifies Kbar=Rbar+1+h(P+1).

For arbitrary real a,b,

`sqrt(|(a^2-1)b^2+1|)<=(|a|+1)|b|+1.`

Indeed, the radicand's absolute value is at most(a^2+1)b^2+1, and the proposed square exceeds this by 2|a|b^2+2(|a|+1)|b|. Consequently

    V0=(P+1)Kbar+2,
`V1=[(Abar+1)Cbar+1][(Abar+1)Ebar+1][(Gbar+1)Hbar+1]+1`

satisfy sqrt(|a0|)<=V0-1 and sqrt(|a1|)<=V1-1 before any semantic conclusion. V0,V1>=2. The same four-factor finalizer proof applies on every natural assignment. It does not need these particular bounds to hold on all unrestricted integer assignments.

## Exact degree despite leading cancellation

Put L=5^32 and eta=20L+1. The base leading degrees are unchanged as functions of L. In particular degR=235L, degdeltaR=215L-1, and the diagonal leading coefficient of deltaR is32\*z_star.

The important top-degree cancellation is real: V1^2 and a1 have the same leading term. Merely adding gate degrees would overestimate the final degree. The independent audit resolves it using exact telescoping identities rather than dropping a canceled term without justification.

Let deltaA=Abar-A, deltaC=Cbar-C, and similarly for J,D,E,F,Gp,H. Their polynomial identities are

- `deltaA=deltaR*Y*(U+1),` deltaC=2\*deltaR, deltaJ=4\*deltaA+10.
- `deltaD=deltaA*(Abar+A)*Cbar^2+A^2*deltaC*(Cbar+C)+Cbar^2+C^2.`
- `deltaE=i[deltaJ*Dbar*Cbar^2+J*deltaD*Cbar^2+J*D*deltaC*(Cbar+C)].`
- `deltaF=deltaA*(Abar+A)*Ebar^2+A^2*deltaE*(Ebar+E)+Ebar^2+E^2.`
- `deltaG=deltaA+deltaF*(Cbar*Dbar+1+Abar)+F[deltaC*Dbar+C*deltaD+Abar+A].`
- `deltaH=2*deltaR+j*deltaC.`

Define Ibar=(Gbar^2+1)Hbar^2+1 only for the audit. Then

`deltaI=deltaG*(Gbar+Gp)*Hbar^2+Gp^2*deltaH*(Hbar+H)+Hbar^2+H^2.`

Put M1=(Abar+1)Cbar+1, M2=(Abar+1)Ebar+1, M3=(Gbar+1)Hbar+1. The differences M1^2-D, M2^2-F, M3^2-I equal respectively

`deltaD+2*Abar*Cbar^2+2*(Abar+1)*Cbar,`
`deltaF+2*Abar*Ebar^2+2*(Abar+1)*Ebar,`
`deltaI+2*Gbar*Hbar^2+2*(Gbar+1)*Hbar.`

Using these expressions in

`V1^2-a1=(M1^2-D)M2^2M3^2+D(M2^2-F)M3^2+DF(M3^2-I)+2M1M2M3+1`

gives a cancellation-free certificate of exact degree 24620L+67 and diagonal leading coefficient 2^57\*z_star.

Write Omega=W and E0=dn+c-Omega\*c, so Theta=E0-Omega\*V0\*V1. The finalizer's inner bracket becomes

`E0^2-2E0*Omega*V0*V1+Omega^2*V0^2*(V1^2-a1)-Omega^2*a0.`

The third term is uniquely highest, of degree 60362L+183 and diagonal leading coefficient 2^137\*z_star. Squaring dominates the final subtracted norm term (degree 96124L+300), so the final polynomial has exact degree 120724L+366 and leading coefficient 2^274\*z_star^2.

Every step of this certificate was independently checked with symbolic fixed leaves. The exact multivariate degree upper bound follows from the displayed polynomial identities; the nonzero diagonal leader gives the matching lower bound. Finite modular tests additionally checked all companion-difference and finalizer identities but are not substituted for the algebraic proof.

A draft value+334 was incorrect and was corrected before finalization: reducing degdeltaR by 16 reduces the inner degree by 16 and the final degree by 32, changing+398 to+366, not to+334.

## Circuit simplification is exact and division-free

The fresh generic circuit builder is `generic_jones_circuit.py`. It is newly authored and never imports received repository Python. It is parameterized by nu and the finite coefficient records.

It evaluates the sparse correction polynomial by sorted-exponent Horner recurrence and shared powers p_j=B^(5^j). Products for consecutive equal radix-five digit runs are cached. The complete homogeneous baseline uses suffix products B^(5^nu-5^j).

The geometric sum also factors exactly:

    lambda = `product_{j=0}^nu(1+p_j+p_j^2+p_j^3+p_j^4)*(1+q)*(1+q^2).`

This follows by repeated geometric-series factorization for powers of 5, then `S_(4L)=S_L(1+q+q^2+q^3).` No division, variable exponent or hidden unknown is introduced.

As a control, the nu32 baseline rebuilt from scratch has 1,704 operations and exactly matches every named value of package 18's20,531-operation circuit on 64 random coefficient/input trials, while an independent symbolic leading audit proves its unchanged exact degree. The nu31 coefficient support is somewhat denser, so its baseline costs1,800 operations; adding the tighter magnitude companions gives the final1,840-operation circuit.

## Scope and conclusion

The algebraic simplification, index construction, quartic reduction, root majorants and exact-degree certificate have been independently audited here. The inherited K215 and native-window/Pell compiler remain ordinary mathematical dependencies; no proof-assistant endpoint was rebuilt. The result is an equivalence formalizable in ZFC, not a proof of ZFC consistency and not a global optimality theorem.


# Appendix F. Independent Pell and signed-domain audit


## Verdict and scope

The new arithmetic reductions are mathematically sound, subject to the explicitly inherited authenticated blank-machine compiler, signed Pell/rank lemmas, whole-tuple coefficient transfer, and K215 calibration. No new gap was found in their unbounded root-recovery arguments. The independently recommended integer form is the **sharp 24-variable, 165-operation, degree-2240** form, rather than the valid but dominated degree-2256 variant.

The audit covers the actual positive 12-variable circuits, the pair-ring integer 24-variable circuits with weights 3 and 2, the 25-variable small-weight circuit, and both ordinary/normalized 26-variable two-root circuits. It is not a proof of Con(ZFC), kernel certification, or a global-minimality result. In particular, these observations do not replace the unbounded compiler and arithmetic classification theorems by finite tests.

The source snapshot is `ae3007ca4467011e0e051c84acb4a1dd13971b0e`. Independently recomputed Git blob hashes of the local mathematical source files agree with the source ledger:

- `23-separating12/proofs/ODD_SCALE_27_PROOF.md`: `9db60b97a08f54b790f3b79540edc693e12d9ccb`.
- `20-root12/arithmetic/SMALL_WEIGHT_PROOF.md`: `a47ffb635dda271afe03804c534cf268be450c8c`.
- `20-root12/amalgamation/ROOT12_PROOF.md`: `abb6bb1519bffe77f7f2970f92464ed1f2c76be6`.
- `21-norm12/proofs/NORM12_PROOF.md`: `13508f1065385cef7914270bd81e8fff79888e3b`.

The old commit mentioned inside the odd-scale document is historical text; the audited retrieved blob is the one in the new snapshot.

## Positive twelve-variable construction

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

## Signed 24-variable amalgamation

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

## Signed 25- and 26-variable forms

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

## Odd-scale and coefficient dependencies

The newly restored integer relations match the precise six-positive-port, odd-i, odd-s, square-w domain. The source negative-s proof was reviewed, including both main-root signs. The rank congruences recover p=R; the growth bound gives `|Y|>2^R`; the two signs yield `X+2^R=0 modulo H` or `X*2^R=1 modulo H`, each contradicted by its strict no-wrap bound. The sign of c is lost only in congruences explicitly squared, so no unsupported positive-c step is used.

Canonical odd-s completeness uses the exact population identity, not only a congruence of R: `popcount(R)=3t+2`, hence `v2(Y)=3t`, and `s=Y/q³` is odd. The shifted MF convention is essential. Algebraically the packing formula agrees with the circuit only when `MF_source=MF_native+beta`. Complete coherent tuples must be used.

The final logical equivalence remains inherited through the fixed authentic compiler and literal-machine calibration. These new arithmetic arguments do not independently establish those large source theorems.

## Independent executable checks and packaging caveat

`pell_independent_checks.py` was newly authored for this audit and treats all received circuits solely as inert JSON. It uses a quotient-algebra multiplication-matrix determinant as the independent reference for the rank-four norm, rather than executing/importing either author's emitter. It validates DAG references, binary operation ledgers, every-gate/every-port liveness, 250 independent signed/zero identity assignments per file, 250 mod-four checks per file, and two exact finite-field affine line degrees. Ten circuits pass, including the three final integer comparison systems. The systems were also checked gate-by-gate against their corresponding audited product circuits; their residual degrees are (12,4,2224), (32,12,4,872), and (32,12,4,38,128), at 161,126,117 operations respectively. The file `pell_independent_checks.json` records frozen SHA-256 hashes and complete results.

`pell_bound_checks.py` adds 600 exact-integer positive-gap fixtures and 1920 signed weight-two fixtures, including negative s,H,P, both i signs, w=0, and T=0. No floating-point square roots are used. These tests supplement the preceding unbounded arguments and are not their substitutes.

Packaging note: the final release uses one shared compact-coefficient directory. All active positive, integer and nine-variable bindings resolve within the archive and their exact payload hashes are checked before replay.


# Appendix G. Retained-system tradeoff and rejected shortcuts


The pinned package-22 source really has 16 positive witnesses, 7 equations,
59 binary gates (33 multiplications, 26 additions/subtractions), and residual
degrees 22,18,24,7,2,22,6. Its stated degree 24 is correct.

Replace its positive auxiliary root y by V+e, where V=of-c and e is a new
positive coordinate in place of y. Every other formula and equation is left
unchanged. Computing V+e costs one addition and its square reuses the original
y-square gate. The emitted `retained16_gap_system60.json` has 60 gates,
33 multiplications and 27 additions/subtractions, and exact residual degrees
22,18,20,7,2,22,6. Its maximum degree is 22.

For soundness, restore y=V+e. The strong equation makes A0=(ic^2)^2>1.
The auxiliary norm A0 V^2-(A0-1)y^2=1 excludes y=0. Replacing y by |y|
therefore gives a positive source root while leaving every equation intact;
no positivity of V is required for this direction. For canonical positive
source witnesses, V>1 and y>0, and

    (A0-1)(y^2-V^2)=V^2-1>0.

Consequently y>V and e=y-V is positive, proving completeness. This is an
existence equivalence, not a claim that all original positive tuples have
positive gap. The exact auxiliary leading degree drops from 24 to 20 through

    A0[V^2-(V+e)^2]+(V+e)^2
      = (V+e)^2-A0 e(2V+e).

The system's degree 22 is still attained by the unchanged first norm and
ordinary strong equation.

Comparison must use the actual existing data: package 12 already has a
15-positive-variable, 6-equation, 61-gate, degree 22 system
`ordinary_gap_system61.json`. Thus our 16-variable 60/22 point saves just one
gate in exchange for one additional variable and equation. The main result of
this lane is the separate 31-variable quartic, not a claimed new <59-gate
frontier.

## Explored but not promoted

- No rigorously equivalent system with fewer than 59 gates was established.
  Simple factorization and affine shears mostly redistribute, rather than
  remove, charged operations.
- A first-root gap tau=L+t costs one more addition and lowers that residual
  to degree 12, but the strong equation remains degree 22. It offers no better
  maximum-degree/operation point here.
- Eliminating alpha through G=q(q-F)-C can keep certain transport expressions
      quadratic using X=wq, but discards a required positivity restriction. It was
  rejected rather than treating inferred bounds as automatic.
- Weakening c^2 divisibility to c in the strong Pell equation does not preserve
  the needed conclusion c|m from the available rank proof. It was not used.
- Direct coordinate elimination can miss useful relations between remaining
  equations. The successful G deletion instead uses N=q(L+1) to reduce the
  apparent cubic product GL to two quadratic products.

These are scoped research observations, not lower bounds or minimality claims.
