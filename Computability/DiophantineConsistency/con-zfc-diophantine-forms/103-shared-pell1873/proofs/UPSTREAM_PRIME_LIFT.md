# Factorial-free CRT without a factorial-size bound

Ordinary arithmetic research, 2026-10-23. Lean formalization is paused. The new construction preserves the incoming shared-direct source and its named C222/ZFC calibration. It changes only the completeness proof of the range certificate and two source expressions before the existing arithmetic compiler. No native-machine premise is introduced.

## A stronger bounded-row certificate

Let E,F be fixed polynomials with nonnegative integer coefficients in an index k, external natural parameters z, and d row coordinates. Fix natural N,z and coordinate bounds `u=(u1,...,ud)`. Define

\[
H=E(N,z,u)+F(N,z,u)+N,\quad T=H!,\quad
D_i=1+(i+1)T,\quad B=\prod_{i<N}D_i.
\]

Then the bounded family

\[
\forall i<N\;\exists w\in\mathbb N^d,
\quad w_j\le u_j\ (1\le j\le d),\quad E(i,z,w)=F(i,z,w)
\]

is equivalent to existence of natural encoded columns A_j and an encoded index C satisfying

\[
B\mid\binom{A_j}{u_j+1}\quad(1\le j\le d),\qquad
B\mid1+(C+1)T,\qquad E(C,z,A)\equiv F(C,z,A)\pmod B.
\]

The columns may additionally be required to satisfy `A_j>u_j`, and hence to be positive. There is **no** hypothesis `H>=u_j+1` or `gcd(B,(u_j+1)!)=1`.

### Soundness

For N=0 there is nothing to prove. Otherwise fix i<N and choose a prime p dividing D_i. Since `gcd(D_i,T)=1`, the prime does not divide H!, so `p>H`. Because `D_i|B`, the range condition and the integer identity

\[
(u_j+1)!\binom{A_j}{u_j+1}
=\prod_{r=0}^{u_j}(A_j-r)
\]

show that p divides a factor. Choose its index `w_j` in `[0,u_j]`; then `A_j=w_j mod p`. This uses signed integer differences in the proof; when `A_j<=u_j`, the factor with index A_j is zero, and the identity is still valid. No cancellation of the factorial is needed for this implication.

Comparing the index divisibility with `D_i=0 mod p` and cancelling T modulo p gives `C=i mod p`. Thus the encoded row congruence implies `E(i,z,w)=F(i,z,w) mod p`. Nonnegative coefficients and the coordinate/index bounds give both values at most H, strictly below p; hence they are equal.

### Completeness by lifting the CRT moduli

Take one bounded row witness `w^(i)` for each i<N. The D_i are pairwise coprime: a common divisor of D_i,D_l is coprime to T and divides `l-i`, while every positive difference at most N divides H! because `H>=N`.

Fix one coordinate j and put `R_j=(u_j+1)!`. For each i let

\[
R_{ij}=\prod_{p\mid D_i}p^{v_p(R_j)},\qquad
M_{ij}=D_iR_{ij}.
\]

The product defining R_ij uses the finitely many prime divisors of D_i. It is a **proof construction only**, not a new operation or coordinate in the final equation. Its properties are

\[
R_{ij}\mid R_j,\quad
\gcd(D_i,R_j/R_{ij})=1,
\quad\text{every prime of }R_{ij}\text{ divides }D_i.
\]

Therefore the moduli `M_ij`, for fixed j and varying i, remain pairwise coprime. CRT supplies a natural column A_j with

\[
A_j\equiv w_j^{(i)}\pmod{M_{ij}}\quad(i<N).
\]

If `P_j=product_i M_ij`, adding a sufficiently large multiple of P_j makes `A_j>u_j`. This operation preserves every strengthened congruence. In particular, it makes the parameterization `A_j=alpha_j+1` available without imposing a new restriction on the decoded witnesses.

The falling-factorial numerator contains `A_j-w_j^(i)` as a factor. It is consequently divisible by `D_iR_ij`. Using the exact factorial identity and cancelling the positive R_ij gives

\[
D_i\mid (R_j/R_{ij})\binom{A_j}{u_j+1}.
\]

Coprimality now yields `D_i | choose(A_j,u_j+1)`. Pairwise coprimality of the D_i yields divisibility by B.

Independently choose C by CRT with `C=i mod D_i`. Each strengthened column congruence also holds modulo D_i, so the valid rows give the evaluation congruence modulo every D_i and hence modulo B. The index divisibility follows by the same CRT. All coordinate constructions and the index construction are compatible: they are independent CRT problems, and each strengthened column period is a multiple of B.

For N=0 take arbitrary positive columns and any C; B=1 and every condition is automatic. This completes both directions.

### Why a plain B shift is insufficient

After removing factorial coprimality one must not merely add B to a column and assume its binomial stays divisible by B. For example `D=B=3,u=2,A=1` gives `choose(1,3)=0`, while `choose(4,3)=4` is not divisible by 3. The strengthened period is 9 in this example; `choose(10,3)=120` is divisible by 3. The proof above chooses positive representatives modulo the lifted moduli from the outset.

## Composition with the completed direct source

The parent is `ConZFC_Shared_Certificates_2026-10-24.zip`, SHA-256 `61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1`. It already uses the sharp carrier `M=M0+1=(m+1)^t`, with `t=t0+1` and `m=m0+1`, and thirteen local coordinates.

Keep the formula-label bounds equal to m. Bound the other ten coordinates by the independent natural U, instead of `V=m+U`. Choose U above those finitely many private witnesses in completeness. Apply the new theorem with

\[
u=(m,m,m,U,\ldots,U),\qquad
H=E(t,z,u)+F(t,z,u)+t.
\]

The exact two source edits are recorded in `SOURCE_PINS.json` and generated from the authenticated archive. The entire numerical calculus, row predicates, all arithmetic graphs, source instantiations, and exporter are otherwise unchanged. Existence is preserved, not necessarily the value of a previously chosen CRT certificate: changing the bounds requires recomputing H,T,B and the lifted encodings.

There is no circular witness bound. Choose a finite C222 proof, its label bound m, carrier, accumulator trace, beta sequence code, and finite local witnesses first. Choose U next; then H,T,D_i and the lifted column encodings. H is independent of the encoded columns and C. All choices are finite natural-number constructions available in ZFC.

The positive-power specialization remains justified. In particular `H>=t>=1`, so factorials at H and t retain positive arguments; every range-binomial upper argument A_j is positive by the lifted choice, and its lower argument `u_j+1` is positive even if U=0. The other power bases/exponents have their unchanged positivity induction. The exact seventeen-constraint, 27-auxiliary positive-power certificate remains unchanged.

The incoming C222-to-ZF and constructible-choice refutation equivalences remain the semantic endpoints. Thus the new natural polynomial has a zero exactly when the same syntactic ZFC refutation predicate holds. Negating yields the ordinary ZFC-formalizable no-zero consistency equivalence. There is no new Lean compiler theorem or encoded internal-ZFC derivation in this candidate.

## Exact materialized comparison

| Variant | Natural variables | Quadratic rows | Quartic monomials | Coefficient height |
|---|---:|---:|---:|---:|
| Incoming affine elimination | 3,614 | 2,954 | 15,996 | 127,778,545 |
| **Prime lift, affine elimination** | **3,609** | **2,949** | **15,752** | **127,285,349** |
| Incoming retained affine wires | 6,183 | 5,523 | 17,430 | 1,993 |
| **Prime lift, retained affine wires** | **6,180** | **5,520** | **17,421** | **1,992** |

Both new polynomials have exact degree four. Both retain five outer and 1,665 other semantic coordinates, 55 power graphs, sixteen binomial graphs, and two factorial graphs. The savings are actual gate variables/rows, rather than a claim based on local witness counts. The original incoming files and earlier candidates remain unchanged. These are improvements against the received literal builds, not claims of global optimality or historical priority.

## Reproduction and checks

From the repository root:

```sh
python3 Computability/DiophantineConsistency/tools/build_shared_crt_prime_lift.py --check
python3 -O Computability/DiophantineConsistency/tools/build_shared_crt_prime_lift.py --check
python3 Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/check.py
python3 -O Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/check.py
```

The generator reads the pinned ZIP, copies only the inspected direct source/arithmetic/audit files, makes exactly the two stated replacements, and regenerates both complete residual and collected polynomial files. `--check` uses temporary staging and compares every generated byte. The main independent checker imports neither builder nor generator: it checks source/ZIP identities, full sum-of-squares expansion and metrics, and strengthened-CRT controls. It separately runs the pinned upstream arithmetic/positive-call/affine-restoration auditor and exact power-constraint auditor on the patched source. The semantic argument is the universal theorem above, not these finite controls.
