# Independent semantic audit of the direct Horn compiler

This audit separates the mathematical equivalence theorem from exact finite artifact checks. It imports neither the builder nor its checker. All reported polynomial comparisons are exact integer identities, not random evaluations. No Lean/Rocq compilation was performed by this audit.

## 1. Fixed source and logical calibration

The source is the twelve-rule numerical C222 calculus, with target1, truth label0 and two padded premise slots. Its implication constructor is I(a,b)=2(a+b)(a+b+1)+4b, with relation/all/equality offsets1,2,3. These are exactly Code254's four times Cantor-pairing codes. `KCode222.lean` gives the eight rho/growG axiom families, bundle, modus ponens, generalization and truth. The bundle's arithmetic side condition is ((c-a)(c-b))²=(d+1)² with naturald, equivalent to c≠a and c≠b. This includes all signed possibilities for the differences; no positive-difference premise is silently added.

`check_horn.py` independently transcribes all constructor formulas from Code254/KCode222 and matches every residual of every branch. It also verifies that all surviving constructor wires are topologically defined nonnegative polynomials. Thus each branch has exactly its stated rule instances, in both directions. Products of branch sums of squares implement disjunction because every branch is nonnegative. Sharing scratch variables across alternative branches is harmless: a selected branch has its canonical natural wire values; unselected branches need not vanish. The seventeen private Horn coordinates include four base parameters and thirteen common scratch coordinates; p,q,v are three additional local coordinates.

The source is machine-independent, although it was originally used by several Turing machines. The exact logical bridge is `KEndpoint.c222_iff_zf_refutation`, followed by `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Neither machine simulation nor a Jones universal polynomial is needed for this composition. Source bytes are pinned to9a33342a03d19cf5b061b2083c6b5d3f27f752ed. Selected source Git blobs were independently authenticated in SOURCE_PINS.json.

These Lean declarations concern the externally represented syntactic derivability predicate. The current output does not become a new kernel proof merely by referring to them. The ordinary mathematical derivations used here, including finite arithmetic, first-order completeness, constructible-choice equiconsistency and finite proof transformations, are formalizable in ZFC. The claimed result is that ordinary mathematical ZFC proves the biconditional with syntacticCon(ZFC), not that a sealed object-language proof file has been emitted.

## 2. Why unordered proof certificates are sound

For each finite single-conclusion Horn rule r, let its balance vector be e_conclusion minus the premise vectors, ignoring zero labels. A finite proof tree gives a nonnegative sum of rule vectors equal to e_1. Conversely suppose such a sum exists and letD be the finite closure of the finitely supported rules from their axioms. If1 were outsideD, sum the balance coordinates outsideD. Every rule contributes at most0: an outside conclusion requires at least one outside premise. The target contributes1, contradiction. This argument handles repeated premises, cycles and self-loops. It would fail for multiple-conclusion rules or signed rule multiplicities; neither is present here.

Use linear weights1+jM. If all rule labels are at mostm and there areN rules, define

 A(X)=product(1+c_i X), B(X)=(1+X) product(1+p_i X)(1+q_i X).

Both have nonnegative coefficients, A(1)≤(m+1)^N, B(1)≤2(m+1)^(2N). The fixed-base variant chooses M0=2^(2mN+1), M=M0+1. The elementary inequality m+1≤2^m holds for every naturalm, including0. Hence every coefficient of A-B has absolute value≤M0<M. If A(M)=B(M), a least nonzero coefficient would be divisible byM yet have absolute value<M, impossible. Thus A=B. Comparing multiplicities at the distinct rational roots−1/j yields precisely the positive-label balance equations; label0 contributes the constant factor1.

The accumulator starts S0=M+1, ends SN=1 and obeys

 S_(i+1)(1+c_i M)=S_i(1+p_i M)(1+q_i M).

All factors and every S_i are positive, so telescoping gives A(M)=B(M). Conversely, list expansions of a finite proof tree and let S_i be the product of weights of currently open obligations. Choosem from the finite labels first, thenM, thenS. This ordering avoids circular bounds. The separate CRT witness boundU must NOT be used as m, becauseU also bounds accumulator/remainder/quotient coordinates depending onM. N=0 is rejected by the two contradictory endpoint conditions.

The earlier height-stream variant instead supplies R0=2, R_(i+1)=R_i((1+p_i)(1+q_i)+c_i), M=R_N+1 and an additional beta stream. Its proof is valid but its polynomial is larger.

## 3. Beta coding and the one bounded family

All beta moduli are1+(i+1)y, therefore positive even at y=0. Quotient, remainder and slack rows enforce n=qd+r and d=r+s+1; these are exactly ordinary Euclidean division with0≤r<d. The two endpoints and each adjacent step use the same code and radix. For any finite accumulator trace choose y greater than all entries and divisible byN!; the finitely many moduli are pairwise coprime, so CRT gives a code. This is a completeness proof, not an extra quantified factorial block.

The fixed-base local row has29 natural witnesses:20 Horn coordinates, six adjacent beta quotient/remainder/slack coordinates, and three independent label-bound slacks. Its five outer parameters are N,x,y,m,M0. The local polynomial is a product of twelve Horn sums of squares plus the sum of the beta, label-bound and update squares. Splitting signed polynomial operations into two nonnegative natural-expression DAGs e,f gives exactly e=f iff that row vanishes.

`check_source_binding.py` compares the entire literal local source to this schema, then checks both global source instantiations exactly, including variable order. It verifies upper evaluation at indexN with all29 witnessesU, encoded evaluation at one encoded index and29 encoded coordinates, and every endpoint.

## 4. Uniform-bound CRT elimination

For fixed outer parameters take T=(e(N,U,...,U)+f(N,U,...,U)+N)!, soT≥1. Let

 Q=(1+(N+1)T)^N+2,
 B=(T^N N! binomial(Q+N,N)) mod(TQ−1).

The pinned CRT product theorem identifies B with product_(k<N)(1+(k+1)T). The divisorTQ−1 is positive becauseQ≥3 andT≥1. For every encoded witnessa_j require B|(U+1)! binomial(a_j,U+1). Require B|1+(index+1)T and e(index,a)≡f(index,a) moduloB. These are the exact bounded-forall certificate of the pinned representation, with every coordinate-bound equal toU.

Soundness follows directly by instantiating that theorem with the constant boundvector. For completeness chooseU greater than every coordinate of the finitely many selected row witnesses, then repeat the CRT construction using this larger common bound. Do not merely substitute a largerU into an already chosen certificate: itsT andB must be recomputed. At N=0, B=1 and the bounded certificate is vacuous, as required; the outer endpoints still reject a nonexistent zero-step proof.

The standard soundness proof chooses a prime divisor of one modulus, whose coprimality withT forces it above the factorial argument. The falling-factorial congruence yields a bounded representative of every encoded coordinate, and the encoded-index congruence recovers the chosen index. Monotonicity of the two natural polynomials places their values below the prime, turning congruence into equality. Truncated falling factorials use min(a,j), not an unwarranted assumptiona≥j. This detail is explicit in BoundedForallCertificate.lean.

## 5. Arithmetic primitives are genuinely polynomial

The literal circuit contains no variable-exponent, factorial, binomial, remainder or bounded-universal operation. These are all replaced by fixed finite natural existential certificates:

- Pell coordinates use the finite Matiyasev criterion, with explicit a>1,n≤y and a zero-index branch. Exact emitted identities match PellRepresentation.lean.
- Power has both exponent-zero and base-zero branches. The general branch uses the finite Pell certificate, an explicit graph of truncated a−n, congruences and a Pell norm. All guards have natural slack witnesses. Unselected branches impose no false side conditions because their full nonnegative residuals are under disjunction products.
- Binomial uses q=2^n+1 and the k-th base-q digit of(q+1)^n, including k>n.
- Factorial uses r=(n+2)^(n+2) and the ceiling quotient ((r+1)^n+binomial(r+n,n)−1)/binomial(r+n,n). Its denominator is positive, includingn=0; its predecessor is therefore a genuine natural witness.
- Congruence uses two nonnegative multiples, a+mq0=b+mq1, valid for every natural modulus, including0.

`check_interfaces.py` verifies every emitted Pell, power and division polynomial by exact sparse-ring equality against independent formulas. `check_composition.py` separately checks every binomial/factorial composition. The unbounded correctness theorems are the named arithmetic identities and pinned Pell/CRT results, not the finite diagnostics.

## 6. Flattening, affine elimination and unrestricted integers

Each addition/multiplication node has a natural wire, and all equalities become quadratic residuals. Their sum of squares is a single quartic. Exact expansion of every row and the complete sparse polynomial is checked by check_structure.py; exact degree4 is established from the expanded nonzero degree-four support, not just an upper bound.

Affine elimination substitutes all addition and scalar-multiplication wires while retaining every genuinely nonlinear product wire. Every substituted expression is a nonnegative affine form in earlier wires. Thus natural-input assignments extend uniquely; on any zero, the reconstructed circuit satisfies all original equations. check_affine.py checks every map, every resulting residual and the complete expanded polynomial.

For the unrestricted-integer variant, only the original semantic inputs need nonnegativity guards. Use x=a²+b²+c(c+1). This is nonnegative for all integers and represents every naturalx:4x+1 is1 or5 modulo8, so Legendre's three-square theorem represents it; exactly one square is odd and the other two even. Dividing by4 gives the displayed form. All gate wires are then automatically nonnegative by topological induction through the positive affine forms and multiplication equations. Applying three-square guards also to every wire would be redundant.

## Audit conclusion

No semantic gap was found in the baseline or fixed-base architecture. The conclusion remains a mathematical proof plus independently checked exact artifacts, not a new Lean/Rocq certificate. Claims of smallest degree, fewest variables, globally minimal description or historical novelty would be unjustified. The genuine architectural difference is a completed fixed polynomial compiled directly from proof rules with small ordinary coefficients, without simulating a Turing machine or instantiating Jones' universal expression.

## Frozen final metrics and reproducibility

The recommended fixed-base affine quartic has16,036 natural variables,700,865 expanded monomials and12,366 quadratic residuals. Its integer version has27,916 unrestricted variables and758,275 monomials. There are3,960 semantic inputs and12,076 retained nonlinear wires. All emitted constants are ordinary explicit integers, with no huge native coefficient ports. See the source summaries for exact coefficient maxima. Normal and optimized independent checks pass; all six targeted corruptions are rejected. REPLAY_COMMANDS.json specifies relative-path commands, standard-library only. FINAL_AUDIT.json pins all current recommended JSON files. Rebuilding omitted expanded artifacts before running these commands is permitted; compare against the frozen hashes.
