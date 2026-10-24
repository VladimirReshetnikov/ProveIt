# Ten positive unknowns,102 operations,degree368

This complete sibling lowers exact total degree from388 to368 at the
same102-operation count and ten strictly positive integer unknowns.
It retains the entire original compact44 fixed coefficient tuple.
The evaluator has60 multiplications,24 additions and18 subtractions;
all102 gates, ten inputs and four fixed coefficient ports are live.
No page, frozen endpoint, incoming archive or Lean source is changed.

The two mathematical changes from `ten-positive-shifted-strong` are

    I=i*c^2,
    F8(delta*Z^2;9*delta*M^2*Dtau,delta*M^2*Df,M^2*Dnum)=0.

Every other polynomial definition, including L=H*I+b, is retained.
Thus the three roots have weights3,1,1. Removing the private i+q^2
addition saves one operation; inserting the scalar9 for the first
radicand adds one multiplication. The new polynomial is not asserted
to be pointwise identical to the parent polynomial.

## Why the weaker strong input is sound

The original full-mu lower bound was used for root separation before
integrality. This sibling replaces it by an explicit integer modulus
argument. After multiplying the three weighted roots by sqrt(delta),
their integer squared arguments are(-9,-1,-1) modulo mu=q^2+1.
A cancelling pair involving3*tau would force mu|8. A cancelling f/y
pair would give the impossible integer identity V^2-Df=-1/Delta.
A cancelling triple would force

    mu|F8(0;9,1,1)=2025=3^4*5^2.

Since q^2+1 is coprime to3, this implies mu|25, contradicting
mu>=1025. These statements require neither q even, rational roots,
Pell classification nor source soundness. All three roots are then
rational by the signed-sum character argument, and the retained
integer-square/adjacent-coefficient descents make them integral.

Main folding and the first Pell norm give c>8X*mu^2*Y^2>8mu before
transport or q parity. Together with I>=c^2, this implies
4*tau<(A-1)I and f<A*I, so3*tau+f<H*I. The same rational-rho
inequality and L=HI+b now exclude a negative transport coordinate.
The main rank is recovered before q evenness; only afterwards are
carrier coprimality and the first-index congruence used. The original
whole-product bound recovers X=2^R, with no cancellation through a
possibly nonunit factor. Fresh positive source61 witnesses are rebuilt
without dividing the current I by mu, including the J=1 soundness case.
`PROOF.md` gives the full unbounded chronology and inherited interfaces.

Completeness uses canonical old102/388 witnesses with integral roots
and positive center tau+f+y. Set

    i_new=i_old+q^2,    n_new=n_old+2*tau.

Both remain positive, I and all strong/transport data remain identical,
and the center becomes3*tau+f+y. No positive inverse i_old=i_new-q^2
is claimed at arbitrary new zeros. The construction proves equivalence
of positive-zero existence through the common finite-refutation theorem,
not a bijection of all positive zero sets.

## Exact degree and independent literal checks

The complete division-free schedule is `equation.json`. `CUTS.json`
accounts for every parent and child row, the one deleted shift addition,
the changed I operand, the new scalar and all thirteen unchanged tail
gates. The exact degree proof has unique leading form omega0^4, where

    omega0=2^7*q0^46*i^5*w^10*Y^19*(eta+zeta)^10
                      *(q0-F-alpha)*(q0-F), q0=beta*J.

Its selected coefficient is

    [J^184*i^20*w^40*Y^76*eta^40*alpha^4*F^4]P=2^28*beta^184>0.

The exponent sum is368. The scalar9 affects a smaller-degree radicand
and cannot change this leading form. The other three coefficient ports
do not occur in the witness coefficient. This proof also gives exact
degree368 at the separately calibrated entire BFS page tuple, without
identifying its different K0 with the original coefficient here.

The independent checker verifies the full parent seal, every literal
cut, complete topology/liveness and operation inventory, all35
independently expanded weighted norm coefficients, the universal
positive-root identity, the modulus constant2025, all residues modulo3,
the exact f=y residual factorization, and the unique centered degree368
term. It independently multiplies the seven-variable leading forms,
including the i^20 exponent, rather than merely recording the result.
It also checks120 actual-port kernel controls,50 exact signed free-port
controls, two full actual-tuple degree368 slices and three semantic
corruptions. These finite controls check transcription; they do not
replace the unbounded proof. The full original four compressed/raw
coefficient payloads and every copied source dependency are authenticated
against their exact pinned repository bytes.

The inherited ordinary native/compiler/refutation equivalence remains
explicit. No new Lean or encoded object-ZFC derivation, proof of
consistency, or claim of a global simplicity minimum is supplied. The
canonical PDF/TeX are unchanged and Lean remains paused.

Run from the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_ten_positive_weighted_roots.py --check
python -B -O Computability/DiophantineConsistency/tools/build_ten_positive_weighted_roots.py --check
python -B Computability/DiophantineConsistency/candidates/ten-positive-weighted-roots/check.py
python -B -O Computability/DiophantineConsistency/candidates/ten-positive-weighted-roots/check.py
```

No historical coefficient emitter or Lean process is executed.
