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
