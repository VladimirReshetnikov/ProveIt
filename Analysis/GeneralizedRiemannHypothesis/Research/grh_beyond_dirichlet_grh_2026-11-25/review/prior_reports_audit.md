# Comparative audit of the five incoming GRH-transfer reports

Prepared from the archives downloaded from `VladimirReshetnikov/ProveIt/docs/incoming` on 25 November 2026 (Pacific date). All five reports examine upstream revision `72fead102f663d5c7a407964a13dc0cf9d977207`. This is an audit of what the reports already claim and prove, not an independent certification of every numerical classification in them.

## Executive conclusions

1. A new report should not repeat the generic determinant comparison, Landau one-sided pole criterion, the conductor-23 cubic target, the cuberoot-of-2 target, or arbitrary finite-Galois split-prime criteria as new work. These are already thoroughly developed.
2. The two broad source-audit reports explicitly separate source inspection from a full Lean rebuild. Only `grh_transfer_analysis.zip` records a checked small standalone Lean supplement; that supplement verifies elementary real inequalities and a finite-product implication, not the arithmetic input to a new L-function theorem.
3. The reports contain substantial claimed deductions beyond a list of standard GRH consequences: exact classifications, refined bounds, prime-race asymptotics, and explicit nonabelian equivalences. They do not prove the new nonabelian prime estimates. Neither the reports nor the short upstream repository establish Artin/Hecke GRH in general, BSD, Vandiver, or arbitrary K-group vanishing.
4. A full-text search of the manuscripts, README files and supplemental Lean files finds **no treatment of bounded-order torsion specialization, formal-power-series specialization, simultaneous determinantal minima, or Fitting-ideal specialization**. The only literal `Fitting` match outside an embedded upstream source is an attribution-list entry naming an upstream algebra file. The proposed power-series/Fitting contribution is distinct from the five prior reports.

## Comparison table

| Archive | Main manuscript | Established content already present | Open bridge / limitations | Relation to the current request |
|---|---|---|---|---|
| `grh-lean-transfers.zip` | `grh-lean-transfers/grh-transfers/report.tex`, with nine section files | CM field finiteness over all levels and characters at fixed weight and degree; genus-field containment for even-weight trivial-character CM forms; unconditional 18 cubic and asserted 26 quintic coefficient-field classifications; prime-degree >=7 bijection with imaginary quadratic fields of class number that prime; simultaneous weighted races; complete S3 splitting-weight detector | Does not prove the one-sided cubic prime estimate; quintic and prime-degree classification arguments are paper proofs, not Lean checked; no priority claim | Arithmetic classifications are genuine additional deductions in the report, but largely use existing CM/class-number inputs. Generic cubic detector and congruence obstruction already covered |
| `grh-transfer.zip` | `grh-transfer/grh-transfer/report.tex` | Claimed exhaustive 229 abelian fields satisfying Zhao's sufficient zero-sum condition B_K<2; arbitrary-field conditional frontier n<=8, |D_K|<193,000,000; many short xy+yz+zx representations and simultaneous variants; arbitrary Galois split-prime one-sided criterion; finite Kummer tests; exact upper limsup of smoothed split-prime error without linear independence | Nonabelian tests remain equivalent reformulations; no proof of target upper bound. Numerical classification uses paper interval arguments and supplied code; not independently validated by this audit | Particularly important overlap: arbitrary finite-Galois zero detection and sharp exponent -1/2 already done |
| `grh_transfer_analysis.zip` | `grh_transfer_analysis/grh_transfer_analysis/report/grh_transfer_analysis.tex` | Detailed source audit; sharp rank/index-sensitive determinant comparison and completion-cost corollary; generic power-saving bookkeeping; Landau criterion; positive principal-class selector for K=Q(sqrt(-23)); seven checked elementary Lean transfer lemmas | Main arithmetic bound for principal ideals of K remains open. Does not build upstream proof locally; does not prove general Hecke GRH | Exact determinant tradeoff is already present, even with a standalone compiled elementary supplement |
| `grh_transfer_analysis_2026-11-25.zip` | `grh_transfer_analysis_2026-11-25/grh_transfer_report/report.tex` | Detailed source audit; covolume comparison; local-twist/global-height interface; generic Landau theorem; sparse auxiliary-family selection with explicit exponent; positive S3 tensor detector; careful K-theory/Vandiver scope and witness quantifiers | Both nonabelian arithmetic bound and appropriate zero-avoiding twist family are unproved. Lean wrappers explicitly uncompiled | Best predecessor for reusable internal methods; caution against repeating sparse-twist selection or the known K-theory obstructions |
| `grh_transfers.zip` | `grh_transfers/grh_transfers/grh_transfers.tex` | Exponent-six class-group partial classification (all omega<=6 or cofactor<=10^8; covers all 432 known examples); precise remaining windows for t=7,8; all-real-x mod-4 weighted race positivity; cubic -23 eventual-sign equivalence; log-concavity of positive eta products and a zero-free band | General exponent-six classification remains open; cubic race sign not established; mathematical proofs and finite certificates, no new Lean checking | Useful arithmetic continuation exists, but this is mainly an elaboration of GRH consequences and analytic reformulations |

All manuscript paths above are relative to `/workspace/scratch/2e716f350570/sources/prior_reports/`.

## Exact overlaps to avoid

### 1. Rank, denominator and completion tradeoffs

`grh_transfer_analysis/.../report/grh_transfer_analysis.tex`, Section 4, Proposition “Determinant amplification,” already assumes

\[
D,m,\theta>0,\quad \theta D\le n\le D,\quad M,B,I\ge0,
\]
\[
V\le n(M-mR+A),\quad \delta\le DI,\quad D(M-B)\le V+2\delta,
\]

and proves the sharp conclusion

\[
R\le\frac{A+(B+2I)/\theta}{m}.
\]

It explicitly allows arbitrary real A and delta. Its “Completion cost” corollary replaces the lower bound by

\[
D(M-B_0)-(D-n)K\le V+2\delta
\]

and, for n>=(1-eta)D, gives

\[
R\le\frac{A+(B_0+2I+\eta K)/(1-\eta)}{m}.
\]

The same section states m>=c X^mu with a subpower numerator implies R(X)<=O_epsilon(X^(-mu+epsilon)), hence zero-free Re(s)>1-mu given the analytic hypotheses. The accompanying `lean/Transfer.lean` proves `sharp_determinant_sandwich`, `power_scale`, and elementary variants. A new determinant statement needs additional mathematical structure, not reparameterization.

The dated report's version retains the negative term -(D/n-1)M before discarding it. It separately explains `TwistedLattice.covolume_add_index_nonneg`: one favorable twist per p-adic embedding is allowed only when determinant ratios share the stipulated global height control and compatible integral structures.

### 2. Sparse auxiliary families

The dated report, Section 6, gives the explicit threshold

\[
\eta=(\beta-1/2)/18,\qquad \limsup_{X\to\infty} S(X)/X^{1-\eta}=\infty.
\]

If the arithmetic remainder estimate holds for each d in such a set S, a quadratic-twist zero-density bound selects a good witness at any prescribed finite height. The constants and onset may depend on d. Divergence of sum_{d in S}(log d)/d suffices. Thus merely weakening “all twists” to “many twists” has already been done.

### 3. Arbitrary finite-Galois zero detection

`grh-transfer/report.tex`, Section 6, treats every finite Galois M/Q of degree n. With P_M its completely split rational primes,

\[
R_M(x)=\sum_{p\in P_M,p\le x}\log p(1/p-1/x)-\frac{\log x}{n}-c_M,
\]

it proves

\[
\mathrm{RH}(\zeta_M)\iff\sup_{x\ge2}\sqrt{x}\,R_M(x)<\infty.
\]

It also treats an abelian E subset M and the prime set P_E minus P_M, removes the centering constant using a dyadic increment, and specializes to the splitting field Q(zeta_ell, 2^(1/ell)); the relevant primes are those where X^ell-2 is irreducible. Those criteria do not supply the one-sided estimate.

The exact endpoint theorem in the same section is

\[
\limsup_{x\to\infty}\sqrt{x}R_M(x)
=2b_M+\frac{1}{n}\sum_\rho\frac1{1/4+(\Im\rho)^2},
\quad b_M=\#\{g\in G:g^2=1\}/|G|,
\]

under field RH, while the limsup is +infinity if RH fails. It uses simultaneous approximation of finitely many zero ordinates, so does not assume their linear independence.

### 4. S3 detectors and congruence obstruction

`grh-lean-transfers/.../cubic.tex` takes the three Frobenius weights (u,v,z), defines

\[
A=(u+3v+2z)/6,\quad B=(u-3v+2z)/6,\quad C=(u-z)/3,
\]

and decomposes the weight as A+B sign+C tau. The C=0 part is Dirichlet-controlled. For C!=0 the correctly oriented one-sided remainder estimate is equivalent to RH of Q(cuberoot(2)). It proves, for every fixed modulus q and arbitrary congruence weight a,

\[
\lim\frac1{\pi(x)}\sum_{p\le x}|\tau(g_p)-a(p\bmod q)|^2
=1+\frac1{\varphi(q)}\sum_a|a|^2.
\]

The analogous -23 trace obstruction appears in `grh_transfers`. A general conditional-expectation formulation would extend this, but is likely an elementary representation-theoretic corollary and should be presented as such.

The dated report develops a different positive detector: rho tensor rho* = 1+epsilon+rho for the standard S3 representation, with prime-power coefficients |tr rho(Frob^k)|^2(1-chi_d(p)^k). Both the nonabelian arithmetic upper bound and matching zero-avoiding auxiliary twists remain hypotheses.

### 5. Cubic ideal-class selector

`grh_transfer_analysis` uses K=Q(sqrt(-23)), its Hilbert class field H and the cubic field x^3-x-1. Its principal-ideal coefficient series is -(1/3) zeta_H'/zeta_H. Positive real residues make auxiliary twist zero avoidance unnecessary for this particular analytic criterion. The actual upper bound remains unproved. The same report correctly observes that inert rational primes of K give principal prime ideals of norm p^2, while the nontrivial ideal-class information is at split primes. The source's existing quadratic inert-prime divisibility detector therefore does not directly supply this statistic, and d=23 is not an admissible source parameter (q0>=18480 divides 2(d+1)).

## Important scope corrections and exclusions

- The endpoint called GRH in the source means all **Dirichlet** L-functions. No report has proved that every occurrence of a Hecke L-value inside a norm identity upgrades the endpoint to arbitrary Hecke/Artin/automorphic GRH.
- The source's `Lib`/`New` directory division is organizational, not a novelty certificate. Several reports explicitly say this.
- A no-`sorry` lexical audit is not a Lean elaboration or kernel replay. Full upstream independent verification is attributed to external records in all five reports. The small standalone Lean file in the undated analysis verifies conditional algebraic bookkeeping only.
- The K-theory report correctly distinguishes the short source's `shaOdd` cocycle model from a usual Tate–Shafarevich group; no comparison theorem is established there. A length bound outside finitely many exceptional primes is not universal vanishing.
- Even classes may disappear from a denominator estimate without vanishing. That does not prove Vandiver.
- The generic Selmer twisting interface requires a nontrivial inertia scalar away from ell with zeta_*^2-1 a unit. A nonzero pure Tate twist is unramified there, so zeta_*=1 and the hypothesis fails. This rules out direct substitution; it does not rule out a separate ramification-and-descent construction.
- Pointwise witnesses require products before gcds: (for all q exists j: ell divides A_qj) iff ell divides gcd_q product_j A_qj. Taking a separate gcd for every branch loses the existential quantifier. The dated report's example (2,3) and (3,2) already documents this.
- Finite enumeration of idoneal numbers through 10,000 does not prove completeness beyond the range. The dated report states this correctly; other global classification claims rely on published analytic bounds/censuses in addition to finite checks.
- The CM quintic and higher-prime classifications explicitly disclaim publication priority and are not presented as new applications of the interior theta-lift argument. Their proofs predominantly use earlier algebraic CM theory and unconditional class-number results. Reusing them as evidence of a new analytic transfer would misdescribe their dependence.
- None of the prior manuscripts certifies a new resolved general open conjecture by transferring the difficult arithmetic heart of the source to a genuinely new L-function family. Their strongest nonabelian outcomes are precise equivalent formulations and bridge specifications.

## Viable new work not contained in the reports

### A. Bounded torsion specialization and formal families

No manuscript treats the source's degree-independent torsion-polynomial specialization theorem, or its passage to integral power series and simultaneous determinantal minima. This is the strongest distinct direction currently proposed by the source-audit agent. For rigor:

1. Confirm evaluations are at zeta_i-1, whose valuations are positive, rather than arbitrary torsion units.
2. Fix a finite torsion grid before truncating; use a uniform positive coordinate valuation to bound all tails.
3. The truncation must preserve coefficient minimum/low-valuation witnesses and must have tail valuation strictly larger than the demanded threshold.
4. If one wants several polynomials/minors or their first m torsion powers simultaneously, the finite obstruction family must be included before choosing the torsion order. A root-of-unity of order p^h may acquire lower order after taking p-divisible powers, so that quantifier must be tracked.
5. For Fitting ideals, a specialization minimum over minors is not automatically every individual minor's minimum. A good minor per determinantal size suffices to bound each ideal, while all other minors give the opposite inequality; this asymmetry may materially reduce the required family.

The result would be a proved reusable local algebra statement. Application to a named global conjecture still requires the corresponding module/presentation and arithmetic bridge. Novelty should be limited to “new in this analysis relative to the five prior reports” absent a literature comparison.

### B. Smaller genus subfields for exponent-six fields

The last report explicitly leaves this question. If genus conditions are relaxed along a subgroup generated by ramified ideal classes, a splitting prime can be corrected by a product R of those ramified ideals so [pR] belongs to Cl(K)^2. For class-group exponent six, p^3 R is principal after removing a rational factor from R^3, yielding |D|<=4 N(R) p^3. Relaxing k independent genus conditions drops the degree of the auxiliary abelian field by 2^k; the sixth power in a square-root prime bound offers a factor 64 per condition, traded against N(R). This is an exact promising inequality, but any explicit classification beyond the reported ranges needs checked constants, genus-rank hypotheses and a new enumeration argument. It is less aligned with the user's exclusion of standard GRH consequences than A.

### C. Collective residue separation

The prior reports select one auxiliary function zero-free in a box. A genuinely collective criterion could permit several auxiliary functions with positive weights, proving noncancellation by a matrix/positive-cone condition on residue vectors instead of a single zero-free witness. This is not developed in the manuscripts. It would still be an analytic abstraction unless new arithmetic supplies such a collection.
