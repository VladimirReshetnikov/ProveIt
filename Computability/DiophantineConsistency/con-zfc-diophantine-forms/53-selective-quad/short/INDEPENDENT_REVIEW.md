# Independent review of the relaxed-rank P72/P74 assembly

Verdict: no gap found in the local ordinary mathematical reduction in
`PROOF.md`, including the relaxed-rank lemma, deleted-quotient restoration,
main target/sign recovery and canonical normalized-witness replacement.
The inherited half-binomial/compiler/calibration boundary remains explicit.
This is an AI-assisted review, not independent human or proof-assistant review.

## Critical mathematical checks

1. The grouped sum-of-squares equations really force all five factors to
   integer units, and the consecutive-product descent plus two mod-4
   exclusions force the three norm factors to +1 before either remaining
   unit sign is assumed. The boundary C=0 is retained until Nt=1 is recovered.
2. The first-index residue gives a nonnegative wrap parameter because
   0<R+epsilon<E. It yields the large main index before the relaxed norm
   is used; consequently c>A*Delta^2 is available noncircularly.
3. In the relaxed-rank proof, L*S0=Delta, so the exact gcd identity is
   gcd(c^2,L*psi_F(ep))=c*gcd(c,Delta). It divides L*psi_F(gcd(t,ep)),
   giving the required lower bound. A proper divisor of ep is at most ep/2;
   doubling and c>A*Delta^2 force ep|t. The later c|m conclusion follows
   from gcd(c,Delta)=gcd(p,Delta)|p. No unjustified c^2|psi_A(m) is used.
4. Only after p|m is established does c^2|(f^2-1) follow. This makes the
   restored j integral. The positivity argument uses f>2c and
   rho^2>Rf^2+c; it does not reuse the unavailable normalized f>c^2 bound.
   Thus both deleted quotient witnesses o,j are positive integers.
5. The auxiliary signed step-down gives the exact target p=R before wrap
   removal. The negative remaining unit sign contradicts the main/first
   Pell ratio using chi_A(2)>P0, so both index/transport signs are +1.
6. The normalized replacement m'=2cR makes psi_A(m') divisible by c^2.
   Its odd quotient has both required negative congruences because R=3 mod4.
   From o'f'=V'+c and f'^2=1 mod c, T'=(o'+Rf')/c is integral and positive.
   Hence the argument is an existence equivalence, not a same-coordinate
   use of the normalized P75 Lean theorem.
7. The reverse map i_new=Delta*i_old leaves f,T,y and all outer data
   unchanged and directly satisfies the relaxed strong equation. Both
   presentations therefore have the claimed completeness direction.

## Direct check of the fixed-minus parity step

The following short derivation verifies the inherited parity conclusion
from the exact hypotheses used in this package. After p=R is odd, write
the auxiliary odd index as ell=2u+1. The strong plus-congruence step-down
applied to chi_A(2ell)=chi_A(2p) modulo chi_A(m) yields

    ell=2qm+sigma*p, sigma in {+1,-1}.

Pell addition gives psi_A(ell)=(-1)^q*sigma*c modulo f=chi_A(m).
The auxiliary odd-quotient congruence is
(-1)^u*psi_A(ell)=-c modulo f. Since f>2c, it forces

    (-1)^(u+q)*sigma=-1.

Modulo c, using c|m, the other auxiliary congruence gives
(-1)^u*sigma*p=-p modulo c. Since c>2p, it forces
(-1)^u*sigma=-1. Thus q is even. Consequently
u has the parity of (sigma*p-1)/2, and the last sign equality gives
p=3 modulo 4 for either sigma. No parity assumption on m is needed.

## Arithmetic and provenance replay

Rebuilt all three circuits and reran `audit_relaxed.py` normally and under
Python `-O`. It passed all source/payload binding, liveness, unit-sign and
exact-leading-form checks. The exact results are:

- P72: 15 positive variables, degree 80, 72 operations = 40 multiplications
  + 17 additions + 15 subtractions. Highest form:
  64*gamma^2*w^8*s^14*(eta+zeta)^6*(beta*J)^50.
- P74: degree 56, 74 operations = 40 multiplications + 18 additions
  + 16 subtractions. Highest form:
  w^4*s^8*T^4*f^8*(eta+zeta)^4*(beta*J)^28.
- Six-equation system: residual degrees 22,18,28,7,2,22, 61 operations
  = 34 multiplications + 15 additions + 12 subtractions.

The separately authored `independent_literal_audit.py` imports neither the
builder nor the primary auditor. It compares literal displayed formulas
against all three JSON evaluators on 500 signed/degenerate assignments,
half using the actual coefficient ports modulo 1000000007: 4000 scalar
or residual comparisons, all passing normally and under Python `-O`.

These finite diagnostics validate transcription, not the unbounded semantic
endpoint. The marked-Wang and blank-K215 theorems were not re-proved or
kernel-checked by this review. The exact-degree formulas were reviewed
algebraically, including the canceled degree-18 main norm.

## Comparison scope

Historical Q56 already uses the relaxed kernel and has degree 56 at 74
operations. P74 is an alternate grouping at a known metric point, not a
new frontier. P72 is the modest degree-80 / 72-operation tradeoff; neither
the relaxed rank theorem nor a global simplicity breakthrough is claimed.
