# Shared-direct certificate review

Reviewed 2026-10-23. The direct component of `ConZFC_Shared_Certificates_2026-10-24.zip` is sound on its stated ordinary mathematical dependencies. Archive SHA-256: `61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1`. This review covers the direct construction, not its coordinate-family integer proposals. Lean formalization remains paused.

The delivered literal measurements check exactly:

| Natural-domain build | Variables | Quadratic residuals | Exact degree | Expanded terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Affine elimination | 3,614 | 2,954 | 4 | 15,996 | 127,778,545 |
| Retained affine wires | 6,183 | 5,523 | 4 | 17,430 | 1,993 |

Both complete expanded polynomials are supplied, with ordinary literal coefficients. The direct route uses the actual numerical C222 rules and the unconditional C222/ZF-refutation and constructible-choice ZF/ZFC-refutation theorems. It needs neither K215 execution nor native/Jones calibration. As in the preceding direct-C222 review, the new compilation is an ordinary proof formalizable in ZFC, not a new kernel-checked end-to-end theorem or an emitted internal-ZFC derivation.

## Shared CRT cancellation

The source uses nonnegative-coefficient polynomial sides E,F and heterogeneous row bounds u_j. Set

\[
H=E(N,z,u)+F(N,z,u)+N+V+1,\qquad T=H!,\qquad
D_i=1+(i+1)T,\qquad B=\prod_{i<N}D_i,
\]

with `u_j<=V`. The certificate requires `B|choose(A_j,u_j+1)`, the encoded-index divisibility, and the encoded row congruence.

The factorial-free range condition is valid. In soundness, a prime dividing D_i is coprime to T, so it exceeds H. Multiplying a binomial by `(u_j+1)!` gives its falling-factorial numerator; a prime divisor supplies a representative in `[0,u_j]`. Polynomial congruence and the monotone E/F upper bound turn the encoded row into equality. The argument decodes modulo a prime divisor, not a generally composite D_i. It does not incorrectly infer `A_j mod D_i<=u_j`.

In completeness, CRT first makes the falling numerator divisible by B. Here the explicit extra `V+1` gives `(u_j+1)!|T`. Since `gcd(B,T)=1`, the factorial can be cancelled, yielding the required binomial divisibility. Omitting the size bound from *this* cancellation proof would be unjustified. A separate stronger prime-power-lift proof, described below, can remove it.

The product B is replaced by the existing positive-modulus remainder identity. For N=0 it returns the empty product 1; the bounded-row theorem is vacuous. For the actual accumulator construction the endpoints exclude N=0. No circular choice of an encoding bound or carrier is used.

## Source and carrier

The builder removes the thirteen shared Horn-wire coordinates branch by branch. Each eliminated wire has a triangular nonnegative polynomial definition. This is existential elimination across a finite disjunction, not an assertion that one wire tuple simultaneously makes all branches vanish. The exact source auditor verifies all 56 branch-specific wire definitions and 34 remaining branch residuals.

The direct numerical-calculus implementation computes the same nested Code254/KCode222 constructors by arithmetic DAGs. Its compositional sparse-polynomial audit matches all branch formulas and the bundle disequality guard exactly. Its further 900 modular comparisons are diagnostics, rather than the proof of the constructor identities.

Heterogeneous CRT bounds replace the three local label-bound slacks: the labels p,q,v use bound m; the four schema coordinates and six beta/accumulator coordinates use `V=m+U`. This leaves thirteen local coordinates. The local row still forces both exact consecutive beta digits from one common code/radix, and its update gives the accumulator transition.

The construction already uses the sharp bounded-factor carrier from `direct-flow-large-carrier`: `M=M0+1=(m+1)^t`. Thus composing that earlier carrier lead adds no further change here. For `m,t>=1`, equal affine-product evaluations first bound the *actual* degree of the premise product by t. Its coefficient sum is then at most `(m+1)^t=M`, so every individual coefficient is strictly below M; least-nonzero-coefficient reduction proves polynomial identity and flow balance. Nonnegative flow for valid single-conclusion rules implies derivability by the finite nonderivable-label cut argument.

Parameterizations `t=t0+1` and `m=m0+1` lose no proof certificate. A zero-length path contradicts the endpoints; a zero label bound makes every update preserve the accumulator and also contradicts them. A finite proof tree supplies the converse, with the carrier chosen before the trace, beta encoding, and the independent CRT witness bound.

## Positive power specialization

Every encoded column is parameterized as `A_j=alpha_j+1`. In the received certificate, adding a multiple of B preserves its congruences and binomial divisibility because the same factorial is invertible modulo B. This shift changes the encoded columns, not the decoded row witnesses; a decoded truth label can still be zero.

These shifts and the ordered call-site positivity induction license **all 55** positive-base, positive-exponent power calls. Factorials are called at positive t,H; coordinate binomials have positive upper argument A_j and positive lower argument `u_j+1`. The inventory does not assume an arbitrary schema, quotient, or slack witness is positive.

The 27-auxiliary power graph is the exact positive specialization of the pinned finite Pell criterion. Its Pell ordinate Y satisfies `Y>=k>=1`, so the zero-index exception is absent. `V=Y^2(d+1)` is precisely the nonzero multiple condition, and all signed congruence quotients use a difference of two naturals. The final norm gives

\[
A^2=1+W^3(W+2)Z^2,
\]

where `A>=2` and `W>=n>=1`. Hence `Z>=1` and `A>W>=n`. This proves the missing subtraction fact before replacing the truncated expression `A dotminus n` by ordinary `A-n` in the rearranged congruence. The graph retains its output bound and every other Pell-index condition. The separate exact power auditor substitutes 61 definitional gates and matches all seventeen remaining constraints.

The smaller binomial graph combines division and base-digit extraction, with explicit bounds on both the low remainder and digit. The factorial graph is the corresponding ceiling quotient with a positive binomial denominator. Every power/binomial/factorial operation is expanded into finite ordinary quadratic rows before issuing the polynomial.

## Affine restoration and exact artifacts

The exporter removes 2,569 monic affine gate variables with nonnegative triangular restoration. Its support cap of four terms controls size, not correctness. Projection and restoration preserve natural zeros, and substituting affine expressions in quadratic rows preserves the degree bound. The retained-wire variant trades more variables for coefficient height 1,993.

The independent affine checker reconstructs these substitutions from the original rows and final variable names, without trusting the exporter's substitution map. It then compares the complete transformed row multiset. Exact expansion of every squared residual agrees with each supplied collected quartic, and every declared variable is live. Exact degree four follows from the actual nonzero quartic support.

## Replays and independent receipt

After inspecting their execution surfaces, I copied only the direct component to scratch and ran these authored scripts normally and under `-O`: two builder variants, the full equation checker on both variants, `audit_calculus.py`, `audit_power_graph.py`, `audit_literal.py`, and `audit_source.py`. All sixteen stages passed. The two rebuilt `equation.json`, `expanded_polynomial.json`, and `BUILD.json` triples were byte-identical to the delivered files. No inherited/reference program, coordinate-family replay, Lean, TeX, network, or package installation was invoked.

The receipt `/tmp/proofs62ff-shared-direct-replay/REPLAY.json` is embedded in the new review JSON. `tools/review_shared_certificates_direct.py` imports no intake code. It authenticates the actual ZIP and thirteen immediate inherited source/Git-blob identities, checking the six explicitly recorded additional trailing-LF bytes rather than silently normalizing text. It independently expands both complete quadratic systems and checks their exact quartics, dimensions, coefficient maxima, and variable liveness. Normal and optimized runs agree apart from their optimization flag.

## A local refinement enabled by this review

The new separate `candidates/shared-crt-prime-lift` strengthens the CRT completeness proof. For each coordinate, lift D_i by the full prime-power part of `(u_j+1)!` supported on D_i. These lifted moduli remain pairwise coprime. They give factorial-free binomial divisibility even when the factorial is not coprime to B, allowing independent private bound U and `H=E+F+t`. Positive columns must be chosen modulo the lifted periods; a plain `+B` shift can fail.

The complete theorem, choice order, positive-power licenses, and exact two-line source transformation are in that candidate's `PROOF.md`. Its measured affine build is 3,609 natural variables, 2,949 rows, 15,752 quartic terms, and coefficient height 127,285,349. Its retained-wire companion is 6,180 variables, 5,520 rows, 17,421 terms, and height 1,992. Both retain exact degree four. The received archive and its valid 3,614/6,183-variable equations are unchanged.

The review finds a complete ordinary semantic chain under the named C222 and Pell characterization theorems. Finite algebra audits support literal fidelity; they do not turn the new compiler into a Lean proof or discharge the separate internal-ZFC proof-production obligation.

