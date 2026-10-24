# Ordinary correctness review: direct C222 quartic, round 12

Reviewed 2026-10-23. I found no unbounded arithmetic or calculus-equivalence gap in the recommended direct construction. The ordinary argument composes a fixed numerical proof calculus with a finite flow certificate, one beta-coded accumulator, a bounded-quantifier CRT certificate, explicit arithmetic representations, and circuit flattening. It does not depend on K215 execution, Wang-tableau calibration, a native coefficient tuple, or Jones's universal polynomial.

The reviewed archive is `docs/incoming/ConZFC_Direct_Centered_Round12_2026-10-24.zip`, SHA-256 `6752a2a80355b0b0dccddddd03afa672174a1fc05753d799297df3945f85c0ce`. Extracted root: `/tmp/dioph-wave12-arrivals-43ac596e36/con-zfc-direct-and-centered-round12`.

The recommended literal has **27,916 unrestricted integer variables, exact degree four, 758,275 nonzero monomials**, and maximum absolute coefficient **320,307,372,009,918**. The natural companion has **16,036 nonnegative variables**, including 3,960 semantic inputs and 12,076 retained nonlinear wires. This is a fully materialized alternative with moderate literal coefficients; it is not a low-variable or global simplicity record.

Lean formalization is paused. This review reads the pinned Lean source interfaces but performs no Lean build or edit. A mathematical proof formalizable in ZFC is distinct from an emitted object-language ZFC derivation or a new kernel proof of the entire Python-generated polynomial.

## The source is the actual numerical calculus

The source is C222, with truth label 0 and falsity label 1. Its numerical constructors use four times Cantor pairing:

\[
\operatorname{Imp}(a,b)=2(a+b)(a+b+1)+4b,
\]

with relation, universal-quantifier, and equality offsets 1, 2, and 3. The twelve padded single-conclusion branches are truth, `rho1` through `rho6`, `growG`, `rho8`, the bundle, modus ponens, and generalization. These are the constructors in pinned `KCode222.lean`; the additional truth branch supplies code 0, and unused premise slots are padded by 0.

The bundle's side condition is encoded by

\[
((c-a)(c-b))^2=(d+1)^2,\qquad d\in\mathbb N.
\]

This holds exactly when `c!=a` and `c!=b`. The forward implication is immediate; conversely choose `d=|(c-a)(c-b)|-1`. Neither difference is assumed positive. The shared constructor wires have nonnegative polynomial definitions and are topologically ordered. Sharing their scratch coordinates between disjunction branches is sound: the selected branch sets its own canonical wire values, while the other branches are not required to vanish.

The fixed Horn relation is a product of twelve branch sums of squares. Hence over naturals it vanishes exactly when one of the specified numerical rules holds. Its seventeen private coordinates are four base parameters plus thirteen shared scratch wires; the three labels `p,q,v` are additional local coordinates. The JSON field `quadratic_residuals` is historical: the bundle retains quartic residuals. The total local Horn product has degree 50, which causes no problem before circuit flattening.

The exact logical endpoints are actual unconditional declarations in the pinned source:

```text
KEndpoint.c222_iff_zf_refutation :
  KCode222.C222 Code254.F ↔ BProv ZFax_s [] Form.fBot

ConstructibleChoice.zf_refutation_iff_zfc_refutation :
  BProv ZFax_s [] Form.fBot ↔ BProv ZFCax_s [] Form.fBot
```

The first theorem's hypotheses do not mention a machine or simulator. The second is the constructible-choice equiconsistency transport. Their source pin is `9a33342a03d19cf5b061b2083c6b5d3f27f752ed`. The stored source SHA-256 values, byte lengths, and provided Git blob hashes authenticate. These interfaces concern the actual externally represented syntactic refutation predicate, rather than a newly defined surrogate for consistency.

The ordinary derivations use first-order completeness, finite proof transformations, and the constructible model of ZFC from a model of ZF. These are mathematical arguments available in ZFC. Referring to those declarations does not by itself make the new Python compilation a Lean theorem, nor produce a sealed internal-ZFC proof file.

## Unordered flow really implies derivability

For finitely many rule instances, require at every positive label `j`:

\[
\#\{i:c_i=j\}=[j=1]+\#\{i:p_i=j\}+\#\{i:q_i=j\}.
\]

A proof tree gives these balances by counting parent/child occurrences. Conversely take the closure of the supported valid rules from truth 0 and the supported axioms. If 1 were not in this closure, sum the balance coordinates outside it. For any single-conclusion rule with a conclusion outside the closure, at least one premise is also outside. Thus its contribution, conclusion count minus premise counts, is at most zero. A conclusion inside contributes zero or a negative number. The target contributes +1, contradicting the balance.

Only finitely many labels occur, so this is a finite sum, even though the calculus itself has infinitely many instances. Cycles, self-loops, repeated premises, and truth padding cause no exception. The argument does require nonnegative rule multiplicities and one conclusion per rule; both requirements are present.

## Fixed binary height and the accumulator

For `N` instances with all labels at most the independently chosen natural `m`, let

\[
A(X)=\prod_{i<N}(1+c_iX),\qquad
B(X)=(1+X)\prod_{i<N}(1+p_iX)(1+q_iX).
\]

Their coefficients are nonnegative. Therefore each coefficient of `A-B` has absolute value at most

\[
\max(A(1),B(1))\le2(m+1)^{2N}\le2^{2mN+1}=M_0.
\]

The last inequality uses `m+1<=2^m`, including `m=0`. Set `M=M0+1`. If `A(M)=B(M)`, the least nonzero coefficient of `A-B` would be divisible by `M`: divide the evaluation by the corresponding power of `M` and reduce modulo `M`. Its absolute value is smaller than `M`, an impossibility. Thus `A=B` as polynomials. Multiplicities of the distinct rational roots `-1/j` for positive `j` give exactly the flow balances; zero labels contribute only the factor 1.

The one accumulator has

\[
S_0=M+1,\quad S_N=1,\quad
S_{i+1}(1+c_iM)=S_i(1+p_iM)(1+q_iM).
\]

All factors are positive, and induction from `S0>0` makes each accumulator positive, so cancellation and telescoping are valid. Conversely expand a finite proof tree in open-obligation order; let `Si` be the product of the factors for its current open obligations. Every transition and both endpoints hold integrally.

The order of choices is essential and correct: choose the finite proof, its labels, `N,m`, then `M0,M`, then the accumulator, and finally its beta encoding and the later witness bound `U`. **The label bound m is not U.** The latter also bounds remainders and quotients depending on `M`, so identifying them could introduce an impossible circular bound.

The common beta code uses positive moduli `1+(i+1)y`, even when `y=0`. For completeness choose `y` larger than all trace entries and divisible by `N!`. The moduli for indices 0 through N are pairwise coprime, and CRT supplies their residues. Endpoint division rows encode `beta(x,y,0)=M0+2` and `beta(x,y,N)=1`. For `N=0` those endpoints alone are inconsistent over naturals; the bounded universal block may correctly remain vacuous.

## The uniform CRT compiler is valid for this source

The local row has twenty labels/Horn coordinates, two beta triples, and three label-bound slacks: **29 natural witnesses**. Its signed polynomial is split into nonnegative-coefficient natural arithmetic expressions `e-f`. The external parameters `N,x,y,m,M0` are fixed while applying the bounded-row theorem. The index is bounded by N; each local witness is bounded by the independent existential U.

Put

\[
T=(e(N,U,\ldots,U)+f(N,U,\ldots,U)+N)!,\qquad
D_j=1+(j+1)T,\qquad B=\prod_{j<N}D_j.
\]

Require a falling-factorial divisibility certificate for each encoded coordinate, the encoded-index divisibility, and the encoded row congruence. For soundness choose a prime divisor p of `D_j`, for an arbitrary `j<N`. Since `gcd(D_j,T)=1`, the prime is coprime to T and therefore exceeds the factorial argument. From

\[
B\mid (U+1)!\binom{a_i}{U+1}
=\prod_{t=0}^{U}(a_i\mathbin{\dot-}t)
\]

it divides one factor. If that factor has index t, the decoded coordinate `min(a_i,t)` is at most U and is congruent to `a_i` modulo p. This handles truncated natural subtraction correctly; one must not assume `a_i>=t`. Index cancellation gives the encoded index congruent to j modulo p. Polynomial congruence then yields `e(j,w)=f(j,w) mod p`. Monotonicity bounds both nonnegative values by the factorial argument, strictly below p, so they are equal.

For completeness choose U above all finitely many selected row coordinates **before** forming T. The moduli are pairwise coprime because T is divisible by every positive index difference below N. CRT supplies the encoded coordinate columns and index. The row equalities imply the required congruences and falling-factorial divisibilities. Recomputing T and B for this common U is necessary; increasing U in an already selected certificate is not justified.

The implementation's product formula

\[
Q=(1+(N+1)T)^N+2,\qquad
B=(T^NN!\binom{Q+N}{N})\bmod(TQ-1)
\]

is the pinned encoded-moduli product theorem. Its divisor is positive since `T>=1,Q>=3`. At `N=0` it correctly returns 1. The global circuit binds the actual local-source e/f at both the upper environment `[N,x,y,m,M0,N,U,...,U]` and the encoded environment, rather than using a free placeholder row polynomial.

## Primitive graph branches do not introduce hidden restrictions

Every primitive graph is a fixed finite existential polynomial certificate.

- Division/remainder uses `n=qd+r` and `d=r+s+1`, which enforces the required positive divisor and exact ordinary quotient/remainder.
- Congruence uses `a+mu=b+mv`. Two natural multiples encode either sign of the difference, including modulus zero.
- The Pell-coordinate certificate includes `a>1`, `n<=y`, its explicit zero-index branch, and the finite Matiyasevich conditions. Its exact formula matches the pinned representation theorem.
- Power includes `k=0,m=1` and the positive-exponent zero-base branch. The general positive-base branch contains the Pell certificate, the natural truncated-difference graph, and every required inequality/congruence. Crucially, its inequalities and Pell side conditions are inside disjunction products: inactive branches impose no positivity assumption on an arbitrary power base or exponent.
- The binomial digit identity uses `q=2^n+1`, so all binomial coefficients are smaller than q. It includes `k>n` and `n=0`.
- The factorial ceiling quotient uses a positive binomial denominator. Its predecessor witness `C-1` is therefore natural, also for `n=0`.

All conjunction polynomials are sums of nonnegative squares or sums/products already known to be nonnegative. Thus zero tests correctly express conjunction and branch selection. The compiler's signed-pair operations preserve the difference exactly while keeping each side a natural arithmetic DAG. The 108 power, 108 Pell, 33 binomial, three factorial, and 72 division/remainder calls are instantiated graphs, not primitive oracles left in the final equation.

The unbounded correctness of the finite Pell and factorial/product representations is supplied by the explicitly pinned theorems and their mathematical proofs. Finite boundary tests alone would not establish it. The archived independent auditors check every actual emitted Pell/power/division interface, every binomial/factorial composition, and the full local/global source binding by exact algebra or tree equality.

## Flattening and the integer domain

Before affine elimination, each natural arithmetic gate receives a fresh wire and a linear or quadratic defining residual. As a triangular system, it has exactly one wire extension for any semantic input assignment. The final equality residuals and all gate residuals are squared and summed; a zero enforces every gate and every arithmetic certificate.

Eliminating addition and scalar-product wires substitutes nonnegative affine forms. A genuinely nonlinear multiplication receives a new retained wire; its operands are affine in previously retained wires and semantic inputs. Hence every resulting residual still has degree at most two, and the omitted wires restore uniquely. Every coefficient in an affine substitution is nonnegative, so the natural-domain existential interpretation is preserved.

Only the 3,960 semantic inputs need nonnegativity guards when allowing unrestricted integers. For each such x add

\[
x-a^2-b^2-c(c+1)=0.
\]

This expression is nonnegative for all integer a,b,c, and represents every natural x: Legendre's theorem represents `4x+1` by three squares, exactly one odd and two even, which gives the displayed formula after dividing by four. The remaining 12,076 internal wires are forced nonnegative by topological induction from those guarded inputs, using the positive affine forms and multiplication equations. Applying nonnegativity guards to every wire would be redundant.

The dimension is therefore `16036+3*3960=27916`. All residuals are at most quadratic, so the integer polynomial has degree at most four. A fresh guard auxiliary has a fourth-power coefficient 1 in its squared residual and appears nowhere else, also establishing exact degree four independently of generic gate degree bounds. The literal polynomial is fully collected and contains no remaining bounded quantifier, variable exponent, factorial, binomial, remainder, choice of coefficient, or unspecified compiler output.

## Review checks and exact scope

The root review runs the allowlisted authored builders and full independent replay in scratch; I did not execute inherited reference programs or duplicate that full reconstruction. I read the local compiler, affine reducer, source-binding/interface auditors, and the pinned source/calibration declarations. The new independent `tools/review_direct_c222_round12.py`:

- authenticates the actual ZIP, ten arithmetic sources, fifteen calculus/arithmetic source copies with provided Git blob hashes, and the complete fixed Horn JSON;
- checks the twelve branch names/coordinate interface and unconditional calibration declarations;
- checks every multiset of at most three abstract single-conclusion rules on labels 0,1,2 against the finite flow implication, including cyclic and repeated-premise cases;
- checks the fixed binary height bound on all ordered tuples of at most three rule instances with label bounds 0,1,2;
- constructs an exact toy beta trace and a two-column uniform CRT certificate, including the product-as-remainder identity;
- scans every term of the full integer polynomial for valid integer coefficients, canonical distinct quartic monomials, exact metrics, and liveness of all 27,916 variables.

These abstract controls are not purported C222 proofs of falsity. They support the reviewed generic lemmas; the unbounded argument is given above. The JSON receipt records the precise counts. Normal and `-O` runs use explicit checks, not Python `assert` statements.

Under the named ordinary source and representation theorems, the complete chain establishes

\[
\exists\boldsymbol x\in\mathbb Z^{27916},\ Q(\boldsymbol x)=0
\quad\longleftrightarrow\quad
\operatorname{BProv}(\mathrm{ZFCax_s},[],\bot).
\]

Negating gives the stated ordinary ZFC-formalizable consistency equivalence. No new native calibration assumption is needed. The remaining formalization boundary is the new literal compiler/flow/CRT/materialization chain and its internal-ZFC proof, not an unnamed simulator hypothesis.

