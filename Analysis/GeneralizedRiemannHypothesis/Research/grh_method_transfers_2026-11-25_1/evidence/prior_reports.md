# Review of prior GRH transfer reports

## Source status

The full `docs/incoming/README.md` was retrieved via the GitHub connector.
Its current text contains no occurrences of `GRH`, `Riemann`, or `Alpöge`.
Thus the five new ZIPs must be reviewed directly rather than inferred from
the drop-zone index. The index explicitly describes incoming ZIPs as
external manuscript packages awaiting placement and independent review.

## Archive-by-archive synthesis

All five packets inspect the same upstream commit,
`72fead102f663d5c7a407964a13dc0cf9d977207`, Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. All distinguish Dirichlet GRH
from Hecke/Artin/nonabelian Dedekind RH. Their full upstream kernel checks
are attributed to Sutherland's independent records rather than to local
rebuilds. One packet contains a local log for seven small transfer lemmas.

### 1. `grh_transfer_analysis.zip`

Main text: `grh_transfer_analysis/report/grh_transfer_analysis.tex`.
Completed paper arguments include a rank-sensitive determinant comparison,
the sharper comparison including twice the index correction, a completion
cost formula, a scalar one-sided Landau pole-exclusion criterion, and a
principal-class criterion for the order-three class character of
Q(sqrt(-23)). The first five pages' consequences (Vinogradov's small
nonresidue conjecture, abelian Dedekind RH) are expressly known consequences.

The seven elementary algebraic Lean lemmas in `lean/Transfer.lean` are
`determinant_budget`, `determinant_sandwich`,
`sharp_determinant_sandwich`, `power_scale`, `determinant_power_scale`,
`square_root_loss_identity`, and
`zeros_on_line_of_finite_factorization`. The latter assumes the analytic
factorization and the factor zero theorems. The logs do not amount to an
independent Lean proof of the analytic transfer criterion or cubic RH.

Sections 5.4--5.5 give the cubic target and explicitly leave its arithmetic
principal-ideal-class estimate unproved. Sections 6--7 rank extensions and
explain why Artin primitive-root density, general class-group generators,
Elliott--Halberstam, twin primes, Vandiver and BSD are not supplied.

### 2. `grh_transfer_analysis_2026-11-25.zip`

Main text: `grh_transfer_report/report.tex`. Its most valuable additions
over the scalar interface are:

* Theorem `thm:landau`: locally integrable E of exponential order, eventual
  upper bound of exponent beta-1, meromorphic transform, and a **positive
  leading Laurent coefficient at each real pole** imply pole exclusion
  and absolute convergence on Re(s)>beta. Merely nonnegative residues are
  sufficient only when all poles are at most simple.
* Theorem `thm:sparse`: an auxiliary set S of eligible primes is enough
  if limsup S(X)/X^(1-eta)=infinity, eta=(beta-1/2)/18. Divergence of
  sum_(d in S) log(d)/d is a sufficient stronger condition. It proves a
  selection principle, not existence of an arithmetic witness family.
* The conductor-23 S3 target has a positive selector and a complete
  conditional analytic reduction, with the arithmetic estimate and a
  suitable nonvanishing twist selection left as separate inputs.
* Proposition `prop:tate-obstruction`: a pure Tate twist is unramified
  away from ell, so it cannot satisfy the source's inertia-scalar condition
  zeta_*^2-1 being a unit. This prevents a direct substitution into the
  generic anticyclotomic Selmer theorem.
* Lemma `lem:gcd`: pointwise branch witnesses require
  gcd_q(product_j A_(q,j)), not a separate gcd along each branch. Its
  (2,3)/(3,2) example is an actual quantifier obstruction.

It distinguishes the source's `shaOdd` cocycle model from ordinary
Tate--Shafarevich/cohomology groups and a fixed-field exceptional integer
from Vandiver's diagonal variation of the field with the prime.
The K-theory discussion includes Pintar and Mok--Zheng follow-on claims,
so neither their ranges nor the generic idea should be reannounced as new.

### 3. `grh-transfer.zip`

Main text: `grh-transfer/report.tex`. Beyond standard consequences it
claims, with human arguments and finite computations:

* A classification of exactly 229 finite abelian fields K/Q satisfying
  B_K=sum_(rho) 1/(1/4+gamma_rho^2)<2: 168 quadratic, 47 quartic,
  7 cubic, one quintic, 4 sextic, one degree-eight, and Q.
  This is a classification of Zhao's sufficient numerical condition,
  **not** an equivalence with all eventual Mertens sign phenomena.
* Many representations n=xy+yz+zx with distinct positive coordinates,
  and x+y a small prime of size O(log(n)^2), including a common-prime
  version for finitely many comparable inputs.
* Theorem `thm:detect`: for a finite Galois M/Q, RH(zeta_M) is equivalent
  to a bounded upper square-root-normalized smoothed completely-split
  prime remainder. A one-sided x^(-1/2+epsilon) bound for each epsilon
  is enough. Prime-power corrections are holomorphic only in the **open**
  half-plane Re(s)>1/2, which is sufficient.
* Corollary `cor:poly`: for M_l=Q(zeta_l,2^(1/l)), l odd prime, RH is
  equivalent to a one-sided bound on a finite dyadic sum over primes at
  which X^l-2 is irreducible. The needed inequality remains unproved.
* An exact limsup for the split-prime remainder under field RH:
  2*#{g:g^2=1}/|G| + B_M/|G|. Simultaneous approximation, not linear
  independence of zero ordinates, gives the upper endpoint. This argument
  is already in this packet and should not be repeated as a new result.

The 95-state RH-machine nonhalting deduction is a direct composition of
published results; its combined Lean build is not claimed. The Kummer
family discussion correctly notes that prime-degree cases alone do not
supply all squarefree parameters required by Hooley's sieve.

### 4. `grh-lean-transfers.zip`

Main text: `grh-transfers/report.tex`, with nine mathematical input files.
The most substantial claimed results are in `quintic-theory.tex` and
`odd-prime.tex`: exactly 26 quintic coefficient fields of weight-two CM
newforms (all levels and nebentypus), and a bijection in every odd prime
degree l>=7 with imaginary quadratic fields of class number l. The count
is 31 in degree 7, 41 in degree 11, and 37 in degree 13. These are explicitly
**unconditional** deductions using Yang/Gonzalez's class-number divisibility,
CM character theory and published class-number classifications. They are
not mathematical consequences that need the RH proof internally.

`genus.tex` proves that the genus field lies in the value field for
trivial-nebentypus CM forms of every even weight, by a ramified-prime
square-root calculation, and thereby gives a noncomputational explanation
of the class-number-two case. `class-three.tex` uses Kummer theory to
replace a GRH-based exponent bound by class-number divisibility in the
cubic coefficient-field classification. The report carefully credits the
earlier class-number and CM results and asserts no publication priority.

`races.tex` gives a simultaneous weighted race for every finite quotient
G of a unit group, with the prime-square term and all central-zero
multiplicities retained. `cubic.tex` treats X^3-2 and classifies every
real weight (u,v,z) on its three Frobenius types. Writing
C=(u-z)/3, C=0 is the abelian direction; C!=0 has a precisely signed
one-sided criterion equivalent to the missing cubic RH. It proves an
L2 orthogonality obstruction to encoding the standard S3 trace using
any fixed periodic weights. That obstruction is already established in
the prior work.

### 5. `grh_transfers.zip`

Main text: `grh_transfers/grh_transfers.tex`.
Theorem `six` proves completeness of the known 432 exponent-six imaginary
quadratic fields on the union of the families omega(|D|)<=6 and
|D|/P^+(|D|)<=10^8. It gives upper bounds 2.1*10^22 and 2.2*10^24 for a
missing field with exactly 7 and 8 ramified primes respectively. The
finite histogram is 60,141,140,76,12,3 for 2,...,7 prime factors. Its
global conclusion relies on the published EKN census through 3.1*10^20;
its own class-group enumeration stops at 5,761,140.

Theorem `race` proves the mod-4 ramp-window bias J_4(x)>0 for every real
x>3/4, with exact-rational logarithm checks up to 65,536 and a large-x
analytic estimate. The analogous conductor-23 cubic assertion is an
**equivalence with the individual degree-two RH**, not an established
eventual sign.

Proposition `eta` gives strong log-concavity/variance control for positive
eta products. For eta(z)eta(23z), it yields a small unconditional zero-free
horizontal band and, assuming its own RH, a bound on its total zero
sum. The text notes that prior computations go farther for this specific
field; no new optimal zero-free region is claimed.

## What is and is not new relative to these packets

The scalar Landau mechanism, covolume cancellation, sparse auxiliary
families, S3 test cases, completely-split detection, branch-switching
quantifiers and the fixed-modulus orthogonality obstruction are all prior
work. A matrix/cone synthesis, if useful and valid, would be an extension
of these scalar reductions, not an already finished nonabelian proof.

I found no direct contradiction among the five packets in the shared
claims reviewed. I did not independently rerun the large class-group or
abelian-field enumerations, nor certify the priority of their arithmetic
classifications. The global counts should remain attributed to the
particular packet and cited published census unless independently rebuilt.

The last packet explicitly asks whether smaller genus subfields combined
with small ramified ideals can improve the exponent-six exclusions. The
new argument in `genus_extension.md` answers this limited question and
proves explicit stronger exclusion families. It uses the exported
Dirichlet GRH together with class field theory and explicit Chebotarev,
not the internal theta-lift construction. This distinction should be made
explicit in the final research report.
