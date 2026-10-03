# Parametric exact degree of the weak-cone native Grill polynomial

Research date: 2026-10-03. This is a new algebraic theorem and verification packet. No frozen source, earlier report, or release packet is modified.

## 1. Results and exact scope

Let a fixed nonempty Grill run table have length m and g distinct run exponents. Put

- s = 2m
- N = s+g+5
- alpha = 3N

For the precise weak-cone source template in the pinned `native_history.py`, let U be its returned four-factor unit and let R_0,...,R_9 be its ten retained comparison differences. If X and every supplied native witness are independent degree-one indeterminates, then

**deg U = 21 alpha - 4 = 63N - 4**

**max_j deg R_j = 4 alpha + 10 = 12N + 10**

**deg [U(1 + sum_j R_j^2) - 1] = 29 alpha + 16 = 87N + 16**

These statements hold for every table admitted by the existing emitter: m>=1 and each exponent an exact integer in [0,2^32-1]. At the level of the displayed polynomial formulas, the same proof holds for every finite table of fixed nonnegative integer exponents. The latter is a mathematical extension of the template, not a claim that the unchanged emitter accepts values outside uint32.

No history equation, positivity condition, Boolean-selector equation, halting assumption, or universality theorem is used to compute these degrees. Fixed exponents and fixed integer recipes have degree zero. The theorem is about the exact polynomial, not its restriction to valid histories and not a minimum over other equivalent representations.

The family includes m=g=1, allzero tables, repeated exponents, and tables having no positive exponent. No nonzero appendant is needed.

### Safe gluing theorem

Keep this native polynomial unchanged, including its independent degree-one X and native witness coordinates. Let C_1,...,C_r be any finite list of integer polynomials in the same polynomial ring or a polynomial-ring extension by additional independent coordinates. The C's may share coordinates with the native part. Define D = max(0,deg C_1,...,deg C_r), ignoring zero polynomials. Then

**deg [U(1 + sum_j R_j^2 + sum_l C_l^2) - 1]
= 21 alpha - 4 + 2 max(4 alpha + 10,D).**

Here D must be an exact maximum, not merely a syntactic upper bound. No uniqueness of the maximum residual is needed. This is an algebraic gluing statement; it does not by itself establish that a particular loader is a correct input compiler for a particular Grill table.

### Exact loader degree

For the source layout in `input_loaders.py`, retain the canonical recoder at width 32 and let the unrestricted recoder have any fixed width k>=4. Keep all runtime coordinates independent and degree one and retain every comparison. The fixed scalar constants are those in the source, except that the unrestricted width and its fixed radix constants may be parameterized consistently. Then

**D_loader(k) = max(34,k+1).**

The native width equality has degree 2, so including it does not increase that maximum. Thus this algebraic composition has exact degree

**63N - 4 + 2 max(12N+10,34,k+1).**

In particular, whenever a separately validated matching compiler has k=m>=4, the native residual always dominates, and the complete composition has degree **87N+16**. This implication does not assert semantic correctness for arbitrary pairs of run tables and loaders, or a new universal compiler theorem.

For the existing frozen width k=397488, D_loader=397489. If that loader is attached algebraically to an arbitrary native table, the formula becomes 63N-4+2 max(12N+10,397489). It is loader-dominated for N<=33123 and native-dominated for N>=33124. Such mismatched attachments are only an algebraic test family; no input-compilation interpretation is asserted for them.

### Arity corollaries for these exact source layouts

The raw native builder introduces W_native=s+g+23=N+18 positive witnesses, excluding its supplied X port. Therefore its complete ten-residual polynomial satisfies

**degree = 87 W_native - 1550.**

The two-recoder loader layout introduces 106 existential coordinates and six external coordinates, with its X witness reused as the native input. Thus W_total=(N+18)+106=N+124. Whenever the native residual dominates, in particular under the separately justified matching k=m>=4 condition, the complete composition satisfies

**degree = 87 W_total - 10772.**

The six external coordinates are excluded from W_total. These are algebraic rewritings of this family's exact ledger counts, not intrinsic degree-versus-arity lower bounds, and not claims about different encodings or eliminated witnesses.

## 2. Why the program values do not change the leading lanes

Write V for Vfinal, h_U for H_U, h_V for H_V, and S_i for the supplied Shat coordinates. Let

L = X+Z0,  J_1 = sum_{i=0}^{s-1} S_i,
p = K L V J_1,

where K=2^max(3,ceil(log2(s+4)),2 max(n_i)+2) is a fixed positive integer. Since s>=2, J_1 is a nonzero linear form. The native definitions are

P0=L, Uf=LV+X,
D=Uf+phase_initial+height_slack,
B=KD, J=J_1-s, P=(B-1)J+1.

Their exact degrees are 1,2,2,2,1,3, respectively, and P_top=p. Neither zero exponents nor repeated exponents can remove a factor of p.

For rep(r)=1+P+...+P^(r-1), r>=1, the exact degree is 3(r-1). For a pack of independent supplied hats minus constants, the final coefficient is a nonzero degree-one polynomial, so a pack of length r has degree 3(r-1)+1. The same observation applies to a group pack: its final group is nonempty by definition, hence its odd-selector sum is nonzero.

The native S lane has S_top=P_top^(s-1) S_(s-1) and degree 3s-2. The T lane is h_U+P h_V, so T_top=p h_V and deg T=4. In

Z = Zb + P^g S + P^(g+s) T,

the three degree bounds are 3g-2, 3(g+s)-2, and 3(g+s)+4. The third is uniquely highest, even when g=1 or m=1. Therefore

Z_top = p^(N-4) h_V,  deg Z = alpha-11.

The highest lane in each of H and M is its input-width lane:

H_top = M_top = p^(N-1) L,
deg H = deg M = alpha-2.

For example, the immediately lower radix lane has degree 3(N-3)+2=alpha-7; the RM lane has degree 3(N-5)+6=alpha-9. The top lane remains present for m=g=1. The unused U exception classes are already absent in this precise source; their absence introduces no additional case or suppressed top coefficient.

Finally, scale=P^N, so q=16 scale has degree alpha and leading form Q=16p^N.

## 3. Parametric unit calculation

Use the exact frozen 67-row kernel. Let

b=2 odd_half,  kappa=eta+zeta,
w=and__w, f=and__f, i=and__i,
gamma=and__ga, tau=and__tau_gap.

All are independent supplied coordinates except the displayed nonzero linear forms b and kappa. Let u=wn2, c=R10a and a=R12. The source gives

u_top=wQ,             deg u=alpha+1,
c_top=kappa b Q,      deg c=alpha+2,
a_top=w b Q^2,        deg a=2alpha+2.

The first norm factor is exactly

R15=(u+ac+gamma d)^2-(a^2+d)c^2,  d=4a+3.

The unrestricted polynomial identity

R15=u^2+2uac+2u gamma d+2ac gamma d+gamma^2 d^2-dc^2

cancels the identical a^2 c^2 terms. The six displayed terms have degree bounds

2alpha+2, 4alpha+5, 3alpha+4, 5alpha+7, 4alpha+6, 4alpha+6.

Since alpha>=24, the fourth is uniquely highest. Thus

(R15)_top=8 gamma w^2 b^3 kappa Q^5,
deg R15=5alpha+7.

Let Z_* = p^(N-4)h_V. The remaining factor leading forms follow directly from the actual kernel:

(R16)_top = w^2 b^2 f^2 Q^4,
(bs_packed)_top = 16 Q^3 Z_*,
(H17)_top = -32 Q^3 Z_*,
(P17)_top = 1024 w^2 b^2 f^2 Q^10 Z_*^2,
(first_unit)_top = 4 w b^2 kappa (tau-kappa) Q^3,
(bs_q)_top = Q.

Their four unit-factor degrees are

- R15: 5alpha+7
- P17: 12alpha-16
- first_unit: 3alpha+5
- bs_q: alpha

The coordinate independence makes tau-kappa a nonzero polynomial. None of the factor leading forms is zero. Multiplication in an integer polynomial ring adds exact degrees, proving deg U=21alpha-4.

The input-group exponent values occur in fixed scalar coefficients and in lower linear transport expressions. The leading expressions above use only K, s, g and the nonempty free-coordinate lanes. In particular d(0)=0 merely removes a lower affine-offset term in nextV; it cannot change any leading unit factor.

## 4. All ten native residual degrees, including the one-phase case

The exact residual degrees in source order are

1. Global bound: 3
2. U transport: 5
3. V transport: 4
4. Phase: 1 if m=1, and 3 if m>1
5. bs_X_bound - wn2: 4alpha-11
6. R10b - R11: 4alpha-11
7. ic22 - R16: 4alpha+10
8. H17 - aux_u_rhs: 4alpha-11
9. input_A - padded_A: alpha-2
10. input_B - padded_B: alpha-2

For the first three, the uniquely largest terms are respectively -P, -P Uf and -P V. For m=1 the phase residual is literally phase_initial-1. For m>1 its degree-three part is -K L V times the nonzero triangular selector form sum_{i=1}^{m-1}(m-i)(S_(2i)+S_(2i+1)). Thus the phase collapse is real, but never affects the maximum.

For residual 7, ic22=(i c^2)^2 has degree 4alpha+10, whereas R16 has degree 4alpha+6. Therefore its leading form is i^2 c_top^4, and it is uniquely highest among the ten native residuals. The native sum-of-squares factor has degree 8alpha+20. This proves the native degree formula.

Multiplying the leading forms yields the complete highest homogeneous part

**F_top = 2^138 p^(29N-8) gamma w^5 odd_half^15
(eta+zeta)^10 f^2 i^4 (tau-eta-zeta) h_V^2.**

Its total degree is 3(29N-8)+40=87N+16. This also proves nonvanishing without needing to reason about any lower term.

On the diagonal where every supplied coordinate equals t, its exact leading coefficient is

**-2^148 (2 K s)^(29N-8),**

a nonzero negative integer for every admitted table. Thus even this fixed ray witnesses the exact degree for the entire raw family. A chosen modulus can divide the coefficient for some tables; a zero modular residue alone would be inconclusive, not a counterexample.

## 5. Sum-of-squares gluing without a unique maximum

If T_1,...,T_v are integer polynomials and d=max deg T_j>0, the degree-2d homogeneous part of sum T_j^2 is the sum of the squares of their degree-d homogeneous parts. At least one is nonzero. A finite sum of squares of real polynomials is identically zero only when every summand is identically zero: evaluating at every real point makes each squared value zero. Hence the top sum cannot vanish.

Consequently deg(1+sum T_j^2)=2d. Apply this to every native and loader residual together. Since U is nonzero with positive degree, its product with that factor has the sum of the degrees, and subtracting one cannot affect its top part. This proves the gluing theorem even when multiple residuals attain the maximum, or when their leading forms have opposite signs.

This argument relies on integer (or real) coefficients and actual squares with positive unit weights. It is not valid in an arbitrary coefficient ring, for signed differences of squares, or if residual identities are imposed before taking the degree.

## 6. Direct loader-source degree proof

### The generic k-wide 34-comparison recoder

The generic source replaces the original prefix by Q=q^k and B=2^(k-1)Q, k>=4. All recoder witnesses are independent degree-one coordinates. The input/output ports in the present uses are either affine degree-one inputs or the fixed integer one.

A degree pass through all 127 unchanged remaining rows of the frozen receipt gives the following comparison upper bounds in source order, with w=k:

(w+1,w+1,1,w+1,w,14,3,1,5,4,2,4,6,10,2,1,2,w,
 7,2,1,3,20,4,1,7,6,3,4,6,10,2,2,1).

For constant-one input/output ports the penultimate bound is 1 rather than 2; the maximum is unchanged. Every bound is at most max(k+1,20).

Two source-verified leading forms attain the candidate maxima:

- repunit_P-P = (2^(k-1)q^k-1)J+1-P has leading form 2^(k-1)q^k J and exact degree k+1
- and__L9-and__R9 has leading form 2^24 and__w^2 and__k^2 and__s^4 q^6 P^6 and exact degree 20

Thus the generic recoder has exact maximum residual degree max(k+1,20). This explicitly retains the fixed Pell/AND baseline when k is small. For example k=4 gives 20, not 5.

### The two recoders and seven outer loader comparisons

The canonical recoder has width 32, hence exact maximum 33. Its input x+1 and supplied spread output have degree one. The ordinary-frame comparison also contains the term

-(2^32-1) p_e s_e canonical_q^32,

with exact degree 34, uniquely highest in that comparison. Its nonzero fixed coefficient is retained. The other frame terms have degrees at most 33,2,1. Therefore degree 34 is attained without relying on a generic upper bound.

The unrestricted k-wide recoder has both ports fixed to one and exact maximum max(k+1,20). The seven outer loader comparison bounds in their own order are

1, 34, k+1, k, 1, k, 2.

They correspond to the canonical length guard, ordinary frame, exponent quotient, exponent gap, ell=N_loader+1, unary scale, and exact unary queue. The use of N_loader here is unrelated to the native lane count N.

The unrestricted first comparison already attains k+1. The frame comparison attains 34. Taking every source comparison together proves D_loader(k)=max(34,k+1).

The final native width comparison is X+Z0=L_e T. Its degree is exactly 2 for the independent supplied L_e and T, and it never dominates.

The script `check_loader_degrees.py` authenticates the source hashes, checks every raw recoder row using degree pairs a*k+b valid for all k>=4, authenticates the attaining source motifs, and checks twelve representative widths including 4,19,32,33,34,397488 and 2^32-1. It does not import, compile or execute the producer. The seven outer formulas are explicitly transcribed and proved above; the script labels that proof boundary rather than claiming to execute their Python source.

## 7. A sharp interface warning, and a controlled extension

The degree-one supplied-X hypothesis cannot be dropped silently. If X is substituted by y^2 for a fresh coordinate y, already the one-phase table [0] has native degree **936**, rather than 712. The independent checker verifies this on the same raw small DAG using X=t^2 and every other supplied coordinate=t, and also by complete univariate coefficient expansion with no special R15 rewrite.

More generally, substitute X by a nonzero polynomial h in fresh coordinates, independent of all native witnesses, with exact degree delta>=1. Put d=delta+2 and alpha=dN. The same source proof gives

P_top=K (P0)_top V J_1, deg P=d,
Z_top=P_top^(N-4)h_V, deg Z=alpha-4d+1,
deg H=deg M=alpha-2.

The kernel calculation is unchanged except for the Z degree. It gives

deg U=21alpha+20-8d,
max deg R_j=4alpha+10,
**deg F_native=d(29N-8)+40.**

The highest homogeneous formula in Section 4 remains valid with the new P_top. Its factors are nonzero because h uses fresh coordinates. At delta=1 this reduces to the main theorem; at delta=2,N=8 it gives 936. For an arbitrary h the all-ones diagonal can vanish, so the symbolic product proof, rather than an automatic diagonal test, is the general nonvanishing argument.

Two further direct tests cover fresh polynomial inputs. For the table [0], h=y^3+yz+7 has exact degree 1160. For h=y^2-z^2, the ray y=2t,z=t certifies exact degree 936; the all-ones ray y=z=t drops to degree 712 and cannot certify the total degree. The complete coefficient expansions agree with the pinned receipt in both tests.

Other coordinate identifications can also change the degree. For instance imposing tau=eta+zeta annihilates the displayed highest form of first_unit. Such substitutions are outside the free-coordinate theorem. A loader implemented by additional residual equations preserves the theorem's polynomial-ring setting; solving those equations and substituting their solutions need not preserve it.

## 8. Verification and source integrity

The independent directory contains newly written, data-only checks. Its raw checker matches all 67 kernel rows and the actual finalizers in all four frozen small DAGs and the full universal DAG, uses the exact unrestricted R15 identity, and certifies upper bounds plus nonzero diagonal leading coefficients. Its second checker fully expands the small diagonal polynomials modulo 17, uses no R15 special rule, and compares every coefficient against the corresponding pinned receipt. Additional clean-room formula cases include allzero tables and maximum uint32 exponents.

Verified native fixture values:

- [0]: m=1,g=1,N=8, exact degree 712
- [1]: m=1,g=1,N=8, exact degree 712
- [0,1,1]: m=3,g=2,N=13, exact degree 1147
- [2,0,1]: m=3,g=3,N=14, exact degree 1234
- [0] with X=y^2: exact degree 936

The full frozen program has m=397488,g=2030,N=797011 and gives exact degree 69339973. This is a regression against the already established full theorem, not the new result by itself. The independent full pass reproduces diagonal leading residues 3 modulo 17 and 53942795 modulo 1000000007.

The finite checks are implementation regressions. Sections 2-7 are the parametric proof. The main new results are the arbitrary-table theorem, the unrestricted residual-gluing rule, the exact small-width recoder/loader maxima, and the explicit free-X boundary.

Primary source SHA-256 pins:

- native_history.py: d6f88f09f5ffd48747b60bd53b98814431bcc5515cd16431438e2768a7f67340
- native_history_proof.md: 714274c3f7a9009f0526bcdf4f854396670d6e8f1e2f58fd15cc737779145747
- native_unit_kernel.json: 2d88343037c08fe8b073f67dca531ee73309c0735c1d98a23c20b9ddb1eb08ae
- input_loaders.py: 597a028e3a64e8ed97502f0b5e66411f293cdda0c9c1d7ebc470f9c38c897c14
- input_recoder130_receipt.json: 175c498990a8e63de7a91d1e3d321ef90a19f129f305074f0c6de10967d0a182

All are read as local data. No upstream Python is executed. This packet has not been published or inserted into any frozen report.
