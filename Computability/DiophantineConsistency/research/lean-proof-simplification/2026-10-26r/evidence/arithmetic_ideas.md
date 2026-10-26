# Three residual arithmetic simplifications

Snapshot: ProveIt `9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9` (2026-10-26).
The earlier a-f waves and five incoming ZIPs were audited by the separate
prior-art agent. All three ideas below survived that audit. A tempting
signed-congruence/orbit idea was rejected: it is explicit in two incoming
archives. The existing source-context bundles, row extraction, rational
root descent, carry normal forms, finite-fiber APIs, and generic semiring
abstractions are assumed already applied.

## 1. Compare Pell coordinates directly instead of sandwiching them between powers

### Concrete target

`Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativePellBootstrap.lean`,
`main_index_gt_first`, lines 309-333. Its clients include the same file's
`source_bootstrap` (line 398) and `NativePellFirstIndex.source_first_index_exact`
(line 57). The existing proof first excludes p=1, introduces p-1 and n-1,
and proves four power inequalities to contradict k<c.

The repository statement assumes 1<A, 1<P, 1<c, 0<p, 0<n,
2A<2P-1, c=y_A(p), k=2y_P(n), and k<c. Its essential conclusion is n<p.

### Better mathematical statement

If A<=P, c=y_A(p), y_P(n)<=k, and k<c, then n<p. The ordinary Pell
definitions require A,P>1, but no positivity or lower-index assumptions on
p,n,c are needed by this argument. Suppose p<=n. Then

    c = y_A(p) <= y_P(p) <= y_P(n) <= k < c.

The first inequality is monotonicity in the *base*, the second the already
available monotonicity in the *index*. Prove base monotonicity simultaneously
for the two positive-coordinate recurrences:

    x_A(0)=1, y_A(0)=0,
    x_A(n+1)=A*x_A(n)+(A*A-1)*y_A(n),
    y_A(n+1)=x_A(n)+A*y_A(n).

If A<=P, then A*A-1<=P*P-1 in Nat. Each recurrence is monotone in every
argument. One simultaneous induction gives both x_A(n)<=x_P(n) and
y_A(n)<=y_P(n). This avoids using the second-order recurrence with subtraction,
whose monotonicity would be much less direct.

### Lean implementation and verification

`lean/ArithmeticPellMonotonicity.lean` compiles with official
Lean 4.32.0 and import `Std`. It proves:

- `pellPair_eq_of_recurrences`: exact equality with any functions exposing
  the displayed zero/successor equations;
- `pellPair_mono_base`: coordinatewise base monotonicity;
- `pellPair_y_mono_index`: weak index monotonicity;
- `index_lt_of_gap`: the stronger contradiction theorem.

The recurrence adapter reports `propext`; base monotonicity reports no axioms;
the last two report only `propext, Quot.sound`. The log is beside the source.

Mathlib's pinned `Mathlib/NumberTheory/PellMatiyasevic.lean` exposes
`xn_succ` at line 133, `yn_succ` at line 137, and `strictMono_y` at line 375.
Its private `d` is definitionally `a*a-1`. A production proof should use
`change` to expose that expression after rewriting the recurrence rather
than attempting to name the private definition. The core file proves the
adapter obligation abstractly; it is not a compiled production replacement.

Suggested migration: add the base comparison to the shared Pell layer,
preserve the current public theorem signature as a short wrapper, and add
the stronger theorem for new clients. The old hAP implies A<=P by omega.
The old equality for k supplies y_P(n)<=k by omega. The new helper removes
irrelevant exponent growth, natural subtraction, and low-index case splits.
Net production line savings have not been measured; do not count the whole
25-line existing declaration as saved without charging the new common lemma.

Novelty delta: this is a new comparison theorem for two different Pell bases,
not source-row extraction or a renamed signed residue interface.

## 2. A natural-number perturbation theorem replaces the duplicate real ratio analysis

### Concrete targets and duplication

`NativeHalfBinomial.lean`, `upper_estimate_scaled`, lines 18-108, duplicates
most of `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/PellRatio90.lean`,
`upper_estimate'`, lines 222-312. The former uses xi<2(Y+1) and error<1;
the latter uses xi<Y+1 and error<1/2. Both repeat the same growth bounds,
the same relative perturbation epsilon=9/[Y(U+1)], and the same power estimate.
The previous proposals only suggested cosmetic `set` replacements for
artificial existential lets here; that suggestion is excluded.

### Exact perturbation inequality

For natural H,b,r with 2*r*b<=H,

    H*(H+b)^r <= H^r*(H+2*r*b).                         (P)

The proof is elementary induction. For r=0 both sides are H. In the successor
step, use the previous bound and

    (H+2*r*b)*(H+b) <= H*(H+2*(r+1)*b).

After cancellation of the common polynomial terms, this scalar inequality
is just b*(2*r*b)<=b*H. There are no divisions, inverses, real numbers,
or positivity conversions in this proof. It also covers H=0 whenever the
budget allows it. Positivity enters only when cancelling H^r later.

### Checked power-sandwich theorem

For H>0, suppose

    Z*H <= Q*(H+b),   V <= Z^r,   Q^r <= W,
    2*r*b <= H.

Then

    V*H <= W*(H+2*r*b).                               (M)

Raise the scalar comparison to r, use (P), and cancel the positive factor
H^r. The complete argument is kernel checked, not merely proposed.

### Instantiation for the actual Pell estimates

Use natural variables:

    D = U^r,             N = (U+1)^(2*r),
    H = Y*(U+1),         b = 9,
    P = 2*(U*Y^2)+1,     a = Y*(U+1),
    K = y_P(r+1),        c = y_(a+2)(2*r+1),
    Z = (2*(a+2))^2 * U,
    Q = (2*P-1) * (U+1)^2,
    V = c*D,             W = K*N.

Existing `psi_succ_le_pow` proves V<=Z^r after `mul_pow`/`pow_mul`;
existing `pow_le_psi_succ` proves Q^r<=W. Existing `Ratio90.upper_key`
is exactly Z*H<=Q*(H+9), after substitution. The existing premises U,Y>=1
give H>0; the current 72*r<U+1 gives 18*r<=H. Therefore (M) yields

    c*D*H <= K*N*(H+18*r).                            (C)

This is the stable shared interface. It keeps an exact integer error budget
available rather than choosing 1/2 or 1 inside the growth proof.

### Changing the tolerance without replaying the growth proof

A second checked theorem says that from

    c*D*H <= K*N*(H+e),   q*N*e < D*H,   K>0,

one obtains

    q*c*D < K*(q*N+D).                                (E)

When all denominators are positive, this means c/K < N/D+1/q. q=1 gives the
native undoubled error<1; q=2 gives the earlier error<1/2.

For the native case, k=2*K and e=18*r. A further checked wrapper gives

    2*c*D < k*(N+D).                                  (N)

To derive its required budget N*18*r<D*H, use the existing lower ratio and
the source interval c<k*(Y+1) to get N<2*(Y+1)*D. Then

    N*18*r < 36*r*(Y+1)*D
             <= 72*r*Y*D
             < (U+1)*Y*D = D*H.

The middle inequality uses Y>=1; the final one uses 72*r<U+1 and Y*D>0.
For the older undoubled case, its stronger N<(Y+1)*D gives the same bound
for 2*N*18*r, so q=2 is available. These are ordinary multiplication/order
arguments over Nat; no source-defined witness or Pell classification changes.

### Artifacts and exact verification scope

`lean/ArithmeticPerturbation.lean` compiles with Lean 4.32.0,
import `Std`, and proves:

- `perturbed_power_le` (P);
- `majorant_of_power_sandwich` (M);
- `ratio_error_of_budget` (E);
- `doubled_ratio_upper_of_budget` (N).

The first two report only `propext, Quot.sound`. The last two additionally
report `Classical.choice`. No sorry, added axiom declaration, or native
evaluation is used. The remaining integration work is to instantiate the
checked generic arguments with the current Pell growth lemmas and upper_key,
then update the two current clients. Those production adapters have not been
compiled here. No production source or performance reduction is claimed yet.

This is a useful improvement even if every earlier source-context, row,
representation, and sign-interface proposal has already been applied.

## 3. Exact binomial quotient rounding instead of a real fractional witness

### Concrete targets

`NativeHalfBinomial.lean`, `half_binomial_of_ratio`, lines 146-177,
and the adapters inside `source_half_binomial`, lines 210-241. The current
proof calls `Jones1982.rho_split_c` to obtain Q,w and a real fraction f;
it then proves Q even, writes xi/2=t+f/2, and casts two real comparisons
back to Nat. The source client separately casts the Pell lower bound and
the two source interval inequalities to reals.

### Exact Euclidean certificate

For r>=1 and X>=2^(2*r+1), put

    A=(X+1)^(2*r), D=X^r,
    S=sum_(j<r) binom(2*r,j)*X^j,
    Q=sum_(r<=j<=2*r) binom(2*r,j)*X^(j-r).

The binomial expansion gives A=Q*D+S. It also gives

    Q=binom(2*r,r)+X*w

for an explicit nonnegative w. The lower coefficient mass is at most
2^(2*r), and every lower power is at most X^(r-1). Since 2^(2*r)<X,

    S <= 2^(2*r)*X^(r-1) < X^r=D.

If X is even, Q is even: the central binomial coefficient is even for r>0,
and X*w is even. Write Q=2*t. The required certificate is now simply

    A=2*t*D+S,   S<D.                                 (B)

Final source audit: the needed finite-sum certificate already exists as `Jones1980.Ratio90.binomial_floor_two` in the imported Paper1980/PellRatio90.lean:367. It proves the stronger remainder bound 4*S<D under the same native base bound. Reuse that theorem, existing parity, and the checked rounding kernel. No fresh binomial finite-sum lemma is required; the production adapter to these existing facts has not been compiled here.

### Exact rounding mechanism

The native Pell inequalities already supply, or Proposal 2 supplies,

    k*A < 2*c*D,   2*c*D < k*(A+D).                   (R)

The positive source coordinates give

    k*Y < c < k*(Y+1).                               (I)

Substitute (B) in (R). The lower inequality forces k*t<c. The upper one,
using S<D, forces c<k*(t+1). A number c cannot lie strictly inside both
consecutive k-sized intervals indexed by Y and t unless Y=t. Therefore

    2*Y=Q=binom(2*r,r)+X*w.

This is exactly the public conclusion currently needed by
`source_half_binomial` and `NativePopulationLower.source_population_lower`.
The construction changes no witness coordinates, equation, or consistency
claim. It changes the proof interface at the arithmetic rounding boundary.

### Checked artifacts and constraints

`lean/ArithmeticQuotientRounding.lean` compiles with official
Lean 4.32.0 and import `Std`. It proves `rational_window_unique`,
`half_quotient_window`, and `half_quotient_rounding`. Despite the first name,
all statements and proofs are over Nat. The final theorem accepts the exact
decomposition (B), both inequalities (R), and the source interval (I), and
concludes Y=t. All three report only `propext, Quot.sound`.

Do not remove the parity step: an odd Q leaves a half-integer interval and
does not imply 2Y=Q. Do not remove S<D; the short interval is what makes the
integer index unique. The source interval inequalities are strict because
eta,zeta are positive. For compatibility, retain the current real theorem
as a wrapper if other clients need its arbitrary rho interface. The new
integer theorem specifically suits the actual source ratio rho=c/k.

### Relationship of proposals 2 and 3

They address different maintained proof blocks and can be integrated
independently. Proposal 2 removes repeated relative-error analysis and
proves a stronger quantitative integer certificate. Proposal 3 changes
the final central-coefficient extraction from real fractions to Euclidean
division. Together they can remove real-number conversion from the entire
native source-to-half-binomial path, while the earlier article may retain
a real wrapper for its stated theorem. This full production integration is
proposed, not completed.

## Citation and verification records

Pinned repo source URLs use
`https://github.com/VladimirReshetnikov/ProveIt/blob/9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9/`
plus the exact paths above. Mathlib recurrence source:
`https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/PellMatiyasevic.lean`.

The three final arithmetic modules are in `lean/`. Their matching compiler
logs and exact SHA-256 records are in `evidence/checks/`. Exploratory signature
probes and obsolete intermediate files are not included in the deliverable.
