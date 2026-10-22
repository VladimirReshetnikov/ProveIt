# Independent review of the twelve-positive-variable elimination

The independent arithmetic reviewer examined `TWELVE_VARIABLE_PROOF.md`,
`code/build_twelve.py`, and the emitted system/polynomial in `data/`
on 22 October 2026. The reviewed weights are

    M=1+8*T*H*i*c^2+16*R*E*H^2*i^2*c^3,
    N=1+2*H*M.

The review found no substantive gap in the reduction. This is a separate
mathematical review, not a formal assistant build or independent verification
of every inherited native-compiler and Pell theorem.

## Algebra and branch interpretation

Writing `W=Ht+NP` and `m=HM`, the displayed quartic in the formal roots
`tau^2=A`, `u^2=S` is

    [d(W-m*tau-N*u)^2-H^2 e]^2-H^4 Baux^2 D.

Substituting `u=P+H gamma` gives `H^4` times the four-root auxiliary
polynomial in `t-M tau-N gamma`. Its leading coefficient is `d^2 H^4`.
Taking both two-root norms consequently produces the factorization with
prefactor `d^8 H^16` and sixteen linear factors, counted with multiplicity.
Dependence between quadratic fields causes repetitions, not a failure of the
product identity or of the zero implication.

The DAG uses `-f1` and `-f2` in place of the signed reduced coefficients.
This leaves U unchanged and negates V; the final expression `U^2-A V^2`
is therefore unchanged. Its V is visibly even, so the modulo-four unit
guard is valid.

## Separating estimates and rationality

All estimates precede root reconstruction and use only the retained positive
coordinates plus the weak `Nk,Nt` unit bootstrap. They do not assume signs
of eliminated roots. In particular `a+2<2E`, `c<2kY`, `sqrt(A)>Ec/2`, and
the bound on every complex auxiliary branch imply

    |y|/sqrt(A)<8THic^2+4/E+16REH^2i^2c^3<M.

The comparison `S>A` follows from `c>kY` and
`Delta-E^2>2EY`. Hence `N sqrt(S)/H>2M sqrt(A)`. These inequalities dominate
the difference of two branches first when gamma changes and then when tau
changes. Once gamma and tau are fixed, equality of t fixes y; the nonzero
coefficient Baux fixes f. The argument applies to all complex auxiliary
branches and does not require the four quadratic extensions to be
linearly independent.

Every automorphism of a finite normal closure fixes the integer t and all
retained rational parameters, so injectivity fixes the entire selected
tuple. Its entries are rational.

## Denominators and integer recovery

Rational square roots of A, D and S are integers. Thus the denominator of
gamma divides H. If `y=r/s` in lowest terms, its quadratic relation implies
`s^2|d`. Since `Q` is divisible by `H^2`, `gcd(H,Q-1)=1`; also
`N=1 (mod H)`. In `y+N gamma=t-M tau`, the reduced denominators of the two
terms are coprime. They must both be one. This is a valid simultaneous
integrality argument, not an inference from rationality alone.

The reconstructed multiplier is the positive integer `Delta H i` in the
ordinary strong parent theorem. Gamma may be signed, and the explicitly
proved signed parent domain includes it. No unsupported positive-root
restoration is used.

## Strengthened completeness

For full explicitness, the following expands the period argument in the
proof. Choose m to be a common positive multiple of R and a period of the
invertible Pell matrix modulo `Hc^2`; it may be chosen arbitrarily large.
Set

    f=chi_(a+2)(m), i=psi_(a+2)(m)/(Hc^2),
    rho=Delta psi_(a+2)(m),
    V=chi_rho(R)/rho, y=psi_rho(R).

The canonical native rank has `R=3 (mod 4)`. The standard odd quotient
identities give `V=-c (mod f)` and `V=-R (mod c)`. Thus

    o=(V+c)/f, T=(o+Rf)/c

are positive integers; for T, use `of+R=0 (mod c)` and
`f^2=1 (mod c)`. The second congruence follows immediately from
`f^2-1=Delta H^2 i^2 c^4`. This realizes exactly the supplied auxiliary
polynomial and proves that H-divisibility loses no accepting witness.
The period argument does not claim that i can simultaneously be odd.

## Degree certificate

The reviewed leading branches have `M*tau` equal to `+/-16 b_top`.
The two gamma contributions have leading coefficient zero at degree 50
and `-64 b_top`, respectively; the former actually has degree 44.
The auxiliary branches have leading values `+/-b_top`. Consequently the
linear factors have the stated leading magnitudes

    15,17,15,17,15,17,15,17,
    47,49,79,81,47,49,79,81.

Their nonzero product gives exact degree 1360 for the norm, and multiplying
the independent degree-seven and degree-two factors gives 1369 for the
single polynomial. This verifies the structural degree proof, beyond a
univariate numerical specialization.

## Scope

The conclusions concern the new elimination layer and its exact interface
to already proved ordinary mathematical parent lemmas. They do not verify
the enormous coefficient expansion, rerun the K215 Lean/Rocq build, prove
Con(ZFC), or establish a global minimum variable count.
