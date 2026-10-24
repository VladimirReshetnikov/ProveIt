# Independent mathematical review of the strong-Pell budget

Reviewer: a separate agent in the same AI collaboration, 23 October 2026.
Scope: new mathematical steps in `PROOF.md`, especially Sections 4--6.
This is not external human peer review or a new end-to-end formal certificate.

**Verdict: no blocking defect found in the new growth and sign-bootstrap argument.**

The strong-divisibility step is justified in the stated order. If
`f=chi_A(m)`, `c=psi_A(p)` and `psi_A(m)=i*c^2`, ordinary strong divisibility
first gives `p | m`. Writing `m=p*v` and `g=chi_A(p)` then gives
`psi_g(v)=i*c`. Since `g^2=1 mod c` and `g` is a unit modulo `c`, the Pell
recurrence yields `psi_g(v)=v*g^(v-1) mod c`; hence `c | v`. The condition
`c>=6` now makes `v>=6` and `i*c>g^5`, giving the claimed strong lower
bound for `i`. This does not silently replace `c | m` by `c | m/p`.

The bound `i>8*q*Delta*c^4` implies `i^3>6*q*f^2` including the constant
term in `f^2=1+Delta*i^2*c^4`: the surplus `2*q*Delta*c^4*i^2` is larger
than `6*q`. The bounds `i>q` and `i>A*c^2` give `i^3>q^2`, `fbar<i^2`,
and the stated margin above `fbar+k`.

The sign bootstrap was checked in both branches. For `V>0`, the excess
`y-V` is less than `c*T-R`, and the budget `i^3>q^2` dominates a possible
negative R through the displayed Bneg bound. For `V<0`, integrality gives
`c*T-R<=0`, so `R>=c*T>=c>8*q^9`. Consequently `R<2*q*Bneg`, and
`abs(V)<Df*R`, `y-abs(V)<R`. The budget `i^3>6*q*Df` then dominates the
negative-root loss. No positivity of C is used before the contradiction.

After C is recovered, the same excess estimate makes the reconstructed
source variable r positive for every signed root choice. In completeness,
the strengthened budget and the inherited weighted-witness choice give
`r>q*W-2*k>c*T+fbar`, so the new n is positive. The witness selection order
is acyclic and imposes no extra congruence restriction on the strong pair.

The new proof still imports the retained ordinary source/compiler calibration,
standard Pell identities, and the weighted-witness existence theorem. This
review did not independently reconstruct the entire inherited native compiler
or an encoded object-language ZFC derivation. The literal-polynomial and exact
degree audits have their separate executable receipts.
