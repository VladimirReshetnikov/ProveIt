# Independent mathematical audit of the sparse-support constructions

This note concerns the explicitly materialized coefficient tuple and the polynomial circuits derived from ProveIt snapshot `124c07c0b77a9e20e84676514d8b1ff78536ea3f`. It separates the newly checked mathematical transformations, the finite artifact checks, and the inherited compiler theorem. It does not claim that a finite test establishes consistency or establishes a universal compiler theorem.

## 1. The new extraction lemma

Let

\[
p_j(\mathbf n)=\sum_{|\alpha|\le2}a_{j,\alpha}\mathbf n^\alpha,
\qquad 1\le j\le r,
\]

be fixed quadratic polynomials in nonnegative coordinates. Let \(\mathcal A\) be the union of their supports. Choose positive integer weights \(w_1,\ldots,w_s\), let \(w_0=0\), and put \(W=\max_iw_i\). For a degree-at-most-two multi-index, put \(e(\alpha)=\sum_i\alpha_iw_i\).

**Sufficient condition.** For each \(\alpha\in\mathcal A\), the only degree-at-most-two multi-index \(\gamma\) satisfying \(e(\gamma)=e(\alpha)\) is \(\gamma=\alpha\).

The quantifier over \(\gamma\) includes absent monomials. It is insufficient merely to separate the members of \(\mathcal A\) from one another. On the other hand, collisions between two absent monomials are harmless.

Choose target positions \(h_j\ge2W\) spaced by \(2W+1\), and define

\[
D(Z)=\sum_{j,\alpha\in\operatorname{supp}(p_j)}
 (2-|\alpha|)!\prod_i\alpha_i!\;a_{j,\alpha}
 Z^{h_j-e(\alpha)}.
\]

Then every exponent is nonnegative, and

\[
[Z^{h_j}](1+\sum_i n_iZ^{w_i})^2D(Z)=2p_j(\mathbf n).
\tag{1}
\]

**Proof.** The coefficient of \(Z^{e(\alpha)}\) in the square is exactly

\[
\frac{2!}{(2-|\alpha|)!\prod_i\alpha_i!}\mathbf n^\alpha
\]

for each supported \(\alpha\), by the sufficient condition. This cancels the factorial in the encoded coefficient. The encoded support of row \(j\) is contained in \([h_j-2W,h_j]\). These intervals are disjoint. After multiplication by the square, its support is contained in \([h_j-2W,h_j+2W]\), which contains no other target. Thus each target receives only its own row. This proves (1).

If all encoded coefficients have absolute value at most \(M\), every coefficient of the product in (1) has absolute value at most

\[
M(1+\sum_i n_i)^2.
\tag{2}
\]

Indeed, the encoded coefficients occupy distinct positions, and the coefficients of the square are nonnegative with sum \((1+\sum_i n_i)^2\). Collisions among absent monomials change neither assertion.

### Concrete finite check

The shifted parent has 31 coordinates, 22 rows, 136 encoded coefficient records, and 71 distinct supported monomials: the constant, all 31 linear monomials, and 39 quadratic monomials. There are \(32\cdot33/2=528\) padded degree-at-most-two monomials.

Both supplied vectors satisfy the sufficient condition:

\[
\begin{aligned}
w^{220}={}&(24,89,95,146,205,155,147,197,203,78,29,148,47,208,25,217,\\
&129,169,30,215,220,219,135,166,27,133,32,200,43,204,152),\\
w^{239}={}&(237,231,223,221,233,193,195,215,120,190,226,142,125,151,148,169,\\
&214,134,140,121,126,172,128,196,238,191,239,192,197,184,205).
\end{aligned}
\]

The first has 308 distinct padded pair sums; the second has 249. Each of the 71 supported pair sums has exactly one preimage among all 528 pairs. In addition to these checks, the independent audit checks every one of the \(136\cdot528=71,808\) coefficient-record/monomial combinations against every target set, both for the final target offset and for the historical unshifted convention. Both final constructions use the shifted convention. Thus the audit does not infer absence of cross-row contamination only from a search score.

The source matrix is bound to the exact parent JSON with SHA-256

`ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48`.

No minimality of either weight vector is asserted. The novelty relative to the pinned supplied constructions is the weakening from full Sidon separation to separation only at the supported monomials.

## 2. The constant-scaled quadratic base for nine unknowns

The nine-unknown proof may use the following mixed domain during its derivation:

\[
\epsilon,\phi,n\ge0,\qquad g,h,s,w,i,j>0.
\]

The exported positive and natural variants are obtained by the indicated successor substitutions; all nine variables really do belong to the stated uniform domain in each exported circuit.

The inherited exact coefficients satisfy \(|c_{j,\alpha}|<M\), where

\[
M=2^{2134927},\qquad \beta=4096M=2^{2134939}.
\]

Set

\[
b=\epsilon+2,\qquad B=\beta b^2.
\tag{3}
\]

This replaces the inherited choice \(b=\beta+\epsilon, B=b^3\). It preserves the needed numerical estimates for every \(b\ge2\):

\[
B-1>M,\qquad 4b<B,\qquad M(32b)^2=B/4,
\qquad32Mb^2=B/128.
\tag{4}
\]

For digits \(0\le n_i<b\), (2) and (4) imply a strict coefficient bound below \(B/2\), so the centered-digit carry test is unchanged. Under the broader range \(0<g<4bB^W\), the last estimate in (4) gives the same bound on the upper packed word. The leading encoded coefficient is 2, and all other coefficients have magnitude below \(M<B-1\); hence \(D(B)>0\), independently of the size of \(g\).

The completeness direction can still choose \(b\) to be any sufficiently large power of two, since \(\epsilon=b-2\ge0\). The soundness direction recovers that \(b\) is a power of two from the unchanged Jones ratio certificate; then \(B=\beta b^2\) is also a power of two. None of the premises of `NineRatio.ratio_sound` or `NineRatio.ratio_complete` imposes the old special form \(b\ge\beta\) or \(B=b^3\). Their size hypotheses concern \(R,N,b,G\) and are preserved by (4).

For clarity, the packed source uses

\[
\begin{aligned}
K_c&=h_{22}+2W,&N_0&=B^{W+1},&N_1&=4B^{K_c+1},&N&=N_0N_1,\\
\ell&=\sum_iB^{w_i},&M_c&=N_0-1-(b-1)\ell,\\
Q_c&=(B-2)\sum_jB^{h_j},&T_c&=M_c+Q_cN_0,\\
J_c&=2(1+g)^2D(B)+B\sum_{k=0}^{K_c}B^k,&S_c&=g+J_cN_0,\\
R&=(N-1)((S_c+T_c+1)N+T_c+1),&G_c&=32bB^W.
\end{aligned}
\]

Under the broad bound on \(g\), one has \(0\le S_c,T_c<N\). When \(N=2^e\), the exact identity

\[
\operatorname{popcount}(R)
=2e+\operatorname{popcount}(S_c+T_c)
-\operatorname{popcount}(S_c)-\operatorname{popcount}(T_c)
\]

and Legendre's formula show

\[
N^2\mid\binom{2R}{R}
\quad\Longleftrightarrow\quad
S_c\text{ and }T_c\text{ have no binary carry}.
\]

The lower mask recovers exactly the selected digits; the upper mask tests exactly the centered coefficients at the target positions. Equation (1) therefore tests all 22 rows. This explicitly identifies the part of the inherited proof affected by the new weights and base.

### Removal of an empty initial position

The original nine-source target convention is \(h_j=j(2W+1)\). The delivered nine-source circuits use the improved convention

\[
h_j=j(2W+1)-1=2W+(j-1)(2W+1)
\tag{5}
\]

which starts at the least position justified by the generic degree bound. It removes one factor \(B\) from \(D(B)\), lowers \(K_c\) and the exponent of \(N\) by one, and changes no source or ratio hypothesis. The next section includes a parameter \(\sigma\in\{0,1\}\) to cover both conventions: \(h_j=j(2W+1)-1+\sigma\). The delivered circuits have \(\sigma=0\) and `target_offset=-1` in their source metadata. This final refinement reduces each nine-variable degree by 2,304 and each supplied nine-variable evaluator by three binary operations.

## 3. The nine-variable finalizer and its exact degree

This is inherited from package 45; it is not a new square-merging claim. Its soundness has no hidden assumption that the square roots are independent.

Using the ordinary ratio registers \(P,K,A,C,J,Q,D,E,F,G,H,I\), put

\[
\begin{aligned}
a_0&=(P^2-1)K^2+1,&a_1&=DFI,\\
u&=JF,&v&=QF+J(H-C),\\
m_0&=K^2G_c-4(C-KY)^2G_c-8gK^2,\\
V_0&=PK,&V_1&=(AC)(AE)(GH),&M_d&=Q+H,\\
\Omega&=um_0,\\
\Theta&=u(n+M_d)+v-\Omega(2M_d+V_0V_1).
\end{aligned}
\]

The final polynomial is

\[
F_9=(\Theta^2-\Omega^2(a_0+V_0^2a_1))^2
-4\Omega^4V_0^2a_0a_1.
\tag{6}
\]

On the permitted domain the ratio registers give

\[
0<a_0<V_0^2,\qquad0<a_1<V_1^2,
\qquad0<v/u<M_d-1.
\tag{7}
\]

For example, \(V_0^2-a_0=K^2-1>0\), while

\[
(AC)^2-D=C^2-1,\quad(AE)^2-F=E^2-1,\quad(GH)^2-I=H^2-1
\]

are strictly positive. Also \(Q>0\), \(J,F>0\), and
\(v/u=Q/J+(H-C)/F<Q+H-1\).

If \(m_0=0\), then \(\Omega=0\) and \(\Theta/u=n+M_d+v/u>0\), so (6) cannot vanish. Otherwise a vanishing norm gives

\[
z=\Theta/\Omega=\pm\sqrt{a_0}\pm V_0\sqrt{a_1}.
\]

The rational number \(z\) cannot be zero: that would force \(a_0=V_0^2a_1\ge V_0^2\), contradicting (7). Hence

\[
r_0=\frac{z^2+a_0-V_0^2a_1}{2z},\qquad
r_1=\frac{z-r_0}{V_0}
\]

are rational square roots of the integer radicands, and consequently are integers. Their absolute values are at most \(V_i-1\). Thus

\[
Z=2M_d+V_0V_1+r_0+V_0r_1\ge2M_d+1>0.
\]

The equality \(n+M_d+v/u=m_0Z\) forces \(m_0>0\) and \(u\mid v\). Conversely, if the two radicands are squares, \(u\mid v\), and \(m_0>0\), choose their signed integer roots and set \(n=m_0Z-M_d-v/u\ge0\). This makes (6) zero. This proves exactly the conjunction required by the ratio bridge, including strict positivity of its margin.

### Exact degree, including cancellation

Write

\[
p=47W+23+\sigma,\qquad t=2p,\qquad\lambda=\beta^p.
\]

Then \(\deg N=t\), \(\deg R=3t\), and their diagonal leading coefficients are \(4\lambda\) and \(16\lambda^3\). The decisive degrees in the inherited ledger are

| Register | Degree |
|---|---:|
| \(a_0\) | \(48t+14\) |
| \(a_1\) | \(312t+68\) |
| \(u\) | \(87t+20\) |
| \(m_0\) | \(28t+2W+11\) |
| \(\Omega\) | \(115t+2W+31\) |
| \(V_0\) | \(24t+7\) |
| \(V_1\) | \(156t+34\) |

The direct expression has leading cancellations. They must not be ignored by a maximum-and-sum degree calculation. Set

\[
\begin{aligned}
\Delta_V=V_1^2-a_1={}&(C^2-1)(AE)^2(GH)^2\\
&+D(E^2-1)(GH)^2+DF(H^2-1).
\end{aligned}
\tag{8}
\]

This telescoping identity is exact. Its first two summands have equal top degree \(298t+64\) and equal positive diagonal leading coefficients \(2^{518}\lambda^{298}\). Thus the total leading coefficient of \(\Delta_V\) is \(2^{519}\lambda^{298}\), with no cancellation.

Put \(E_0=u(n+M_d)+v-2\Omega M_d\). The inner expression in (6) becomes

\[
E_0^2-2E_0\Omega V_0V_1+\Omega^2V_0^2\Delta_V-\Omega^2a_0.
\tag{9}
\]

The third term has the unique largest degree \(576t+4W+140\), with diagonal leading coefficient \(2^{1025}\lambda^{576}\beta^{2W}\). Squaring it dominates the final subtraction in (6). Therefore

\[
\boxed{\deg F_9=1152t+8W+280
=108296W+53272+2304\sigma.}
\tag{10}
\]

Its diagonal leading coefficient is the positive integer

\[
\boxed{2^{2050}\beta^{1152p+4W}.}
\tag{11}
\]

For the final \(\sigma=0\) variants, the exact degrees are 23,878,392 at \(W=220\) and 25,936,016 at \(W=239\). The supplied positive evaluators use 670 and 651 binary arithmetic operations, respectively; their natural counterparts use 674 and 655. The extra four operations implement the uniform change of domain.

The supplied certificate circuits use (8) and (9) explicitly. Their nonzero leading residues prove attainment of (10); the shorter evaluation circuits use (6). A finite modular comparison alone would not prove equality of two circuits, so the release should retain the exact algebraic identities (8) and (9) as the reason these certificates apply.

## 4. Transfer to ten unrestricted integers

The signed-ten construction retains package 40's source conventions

\[
b=1+3f,\quad B=2^{2140030}b^2,
\quad h_j=2W+(j-1)(2W+1),\quad C_b=bB^W.
\]

The even exponent in the fixed base coefficient is retained. The bridge uses \(C_b=2^c b^d\) with \(c=2140030W\) even and \(d=2W+1\) odd. Both parity properties remain valid for the new vectors. Under the reverse hypotheses, \(b\) is a nonzero square and \(f\ne0\), hence \(b\ge4\). The full source bounds hold for every integer \(0\le g<2C_b\), before recovery of a power-of-two base. This ordering is essential to the application of Sun's reverse Lucas certificate.

The new extraction lemma proves the only previously full-Sidon-dependent step of that source. The source's positivity, masks, range estimates, binomial-divisibility equivalence, and cofinal completeness witnesses therefore transfer without modification. In particular, positive witnesses use \(b=4^q\), so \((b-1)/3\) is an integer and \(b\) is both a square and a power of two.

The retained finalizer uses three square radicands and the following inherited devices:

1. The intersective quintic \((v^3-v-1)(v^2+23)\), homogenized at the odd nonzero modulus \(S=2A-5\), merges \(S\mid T\) with a nonzero multiplier. It has roots modulo every positive integer but no rational root. At an odd prime other than 23, either the cubic has a simple root or its irreducible cubic Frobenius permutation is even, making its discriminant \(-23\) a square. At 23 the cubic root 3 is simple. At 2, \(-23\equiv1\pmod8\) is a 2-adic square. Lifting and CRT give every modulus. The reverse homogeneous divisibility implication follows from the strictly smaller valuation of its leading term if \(S\nmid T\). This quintic was already present in the pinned packages and is not a new contribution here.
2. The radicand \(r_0=b(1+(3O-4)b^2z^2)\) merges that \(b\) is a square and \(O>0\), once \(z\ne0\). The two factors are coprime. Their product being a square makes \(b\) a signed square; \(b\equiv1\pmod3\) excludes a negative square. The second factor cannot be zero and is negative if \(O\le0\). Conversely, positive bridge witnesses have \(O\ge g\ge b\ge4\), and Pell's equation with nonsquare positive parameter \(3O-4\equiv2\pmod3\) supplies the needed \(z\), after taking a unit power whose second coordinate is divisible by \(b\).
3. The weights \(v_1=r_0\), \(v_2=v_1(P_n^2+K^2+3)\) satisfy

\[
|v_1|>\sqrt{|r_0|},\qquad
|v_2|>\sqrt{|r_0|}+|v_1|\sqrt{|r_1|}.
\]

Here \(|r_0|>1\) whenever \(z\ne0\), and \(\sqrt{|r_1|}\le P_n^2+K^2+2\). If a weighted signed sum of the three square roots is rational, a multiquadratic-field automorphism changing the highest changed term would change that term by more than all earlier terms combined. Therefore every radicand is a nonnegative integer square. This argument permits dependent square classes and negative intermediate radicands; complex absolute values give the same strict inequality.

For center \(Z\) and radicands \(a_0,a_1,a_2\), the final polynomial is

\[
V=Z^2+a_2-a_0-a_1,
\qquad F_{10}=(V^2+4Z^2a_2-4a_0a_1)^2-16V^2Z^2a_2.
\]

It is exactly the product of the eight signed-root factors. The nonzero quintic excludes the zero multiplier case, after which the separation argument gives all three squares and the required divisibility. The converse uses the Pell step, followed by the full residue-class interpolation assertion in Sun's 2026 Theorem 4.1, followed by the norm root. The order matters: first choose the Pell value of \(z\), then a suitable modulus \(\xi\) divisible by \(z\), then the residue class for the final interpolation.

With \(p=47W+23\), the source degrees are \(d_X=6p,d_Y=4p,d_C=2W+1\). The exact degrees at the final norm are

\[
\begin{aligned}
\deg Z&=5d_X+10d_Y+30,\\
\deg a_0&=14d_X+28d_Y+3d_C+57,\\
\deg a_1&=26d_X+48d_Y+6d_C+98,\\
\deg a_2&=114d_X+224d_Y+6d_C+440.
\end{aligned}
\]

The last strictly dominates the other radicands and \(Z^2\). The highest homogeneous part of the final polynomial is therefore the fourth power of that of \(a_2\), giving

\[
\boxed{\deg F_{10}=297088W+147144.}
\]

For \(W=220,239\), respectively, this is 65,506,504 and 71,151,176. An independent computation on the actual exported DAGs attains these bounds modulo two primes. Modulo 1,000,000,007, the respective diagonal leading residues are 489390939 and 862326449.

## 5. Inherited semantics and the ZFC statement

The starting point of the new algebra is the inherited ordinary mathematical theorem that the fixed positive parent system, with the complete `wang943-mixed-121x8801` tuple, has a zero exactly when the K215 machine halts, and that this halting condition is equivalent to the existence of a formal ZFC refutation. The parent coefficient tuple is retained as a whole; it is not assembled from incompatible versions.

The exact sources inspected include package 31's `QUARTIC31_SOURCE_PROOF.md`, `FIXED_BLANK_67_PROOF.md`, `PELL_LEMMA_AUDIT.md`, `ORDINARY_BLANK_PROOF.md`, `BLANK_HELICAL_PROOF.md`, and the complete coefficient adapter. The central issues addressed there include reverse-sign recovery in the Pell argument, zero-residue exceptional cases, helical-to-rectangular soundness, cofinal independent padding, and the unbounded rank congruence needed for the native coefficient tuple. These are mathematical arguments beyond any finite audit. Inspection found no specific additional gap that would turn the new sparse transfer into a conjecture, but it is not an independent reconstruction of the entire inherited compiler proof.

The source transformations, Pell/Lucas identities, finite-field facts, unique factorization, and finite multiquadratic extensions used above are ordinary mathematics formalizable in ZFC. Consequently, composing the new equivalences with that inherited theorem gives, for each delivered domain \(D\),

\[
\mathrm{ZFC}\vdash
\bigl[(\exists\mathbf x\in D)F(\mathbf x)=0\bigr]
\longleftrightarrow
\bigl[\exists p\,\operatorname{Prf}_{\mathrm{ZFC}}(p,\bot)\bigr].
\]

Classical negation gives the requested equivalence of no zero with \(\operatorname{Con}(\mathrm{ZFC})\). This does not assert that ZFC proves either side. It does not use the consistency of ZFC as a premise.

### Proof-assistant boundary

At the pinned snapshot, ProveIt also contains the unconditional Lean endpoint `DiophantineConsistency.zfcNinePolynomial_noZero_iff_conZFC`. Its fixed nine-variable polynomial is selected noncomputably by classical choice from the MRDP/Jones construction. It is not the coefficient-exporting construction in this release. The exported short-circuit certificates prove exact local polynomial equivalences to the historical parent; the project status still distinguishes those results from an end-to-end checked explicit compiler and an exported object-language ZFC derivation.

Thus the delivered equations have the ordinary mathematical proof dependency just described. This release must not label them as newly end-to-end Lean-certified, and it must not conflate the noncomputable nine-slot existential theorem with an explicit coefficient file. Conversely, absence of a proof-assistant transcription does not by itself make the ordinary mathematical theorem conditional.

## 6. Reproducible finite audit

`audit_exported_circuits.py` reads JSON and exact coefficient bytes only; it imports no release module and executes no release code. Its checks remain active with `python -O`. It verifies:

- the pinned parent hash and all four native coefficient payload hashes;
- signed exact coefficient payloads against their complete integer recipes;
- the numerical coefficient bound used in the quadratic-base source;
- supported-monomial isolation and all cross-target record/monomial combinations;
- allowed polynomial gate types, acyclicity, complete reachability, declared variable sets, fixed-leaf binding, and exact binary-operation counts;
- the exact-degree leading coefficients of the nine-variable cancellation-resolved forms, including their closed-form value (11), modulo two primes;
- the exact-degree leading coefficients of the ten-integer exported evaluators modulo two primes;
- the ten-variable coefficient records against every shifted source row.

Its JSON output is `independent_export_certificate.json`. This evidence concerns finite algebra and artifacts. No part of it is a test for whether the parent system has a zero, and no search for solutions was needed.

## Primary source locations

All repository references below use the pinned snapshot above:

- `Computability/DiophantineConsistency/con-zfc-diophantine-forms/31-sun10/` — complete fixed parent, coefficient adapter, native compiler sources, inherited finalizer.
- `Computability/DiophantineConsistency/con-zfc-diophantine-forms/40-packing10/` — quadratic multitarget signed-ten source, full source and finalizer proof, exact degree.
- `Computability/DiophantineConsistency/con-zfc-diophantine-forms/45-multioutput/nine/MULTITARGET_NINE_PROOF.md` — positive nine-variable source, ratio finalizer, cancellation-resolved degree ledger.
- `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean` — parametric soundness and completeness interface for the unchanged nine-variable ratio tail.
- `Computability/DiophantineConsistency/Lean/DiophantineConsistency/ZFC.lean`, `STATUS.md`, and `COMPILER.md` — distinction between the existential formal endpoint and explicit coefficient/compiler certification.
- Zhi-Wei Sun, *Ten unknowns for Hilbert's tenth problem over the integers*, arXiv:2609.01594v2, especially Theorem 4.1 and Propositions 6.1–6.2: <https://arxiv.org/html/2609.01594v2>.

