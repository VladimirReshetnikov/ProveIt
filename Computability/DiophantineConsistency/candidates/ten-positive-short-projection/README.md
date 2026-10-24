# Ten positive unknowns,101 operations,degree368

This complete sibling saves one operation from the frozen weighted-root
endpoint while retaining its ten strictly positive integer unknowns,
exact degree368 and entire original compact44 coefficient tuple. Its
acyclic evaluator has60 multiplications,24 additions and17 subtractions.
All101 gates, ten inputs and four coefficient ports are live. Frozen
endpoints, pages, incoming archives and paused Lean work stay unchanged.

The only mathematical change is to replace the projection numerator by

    Kpos=X*(3c-2X)+2

in the same weighted(3*tau,f,y) octic center. The old numerator is used
only as a proof abbreviation:

    Kquad=X*(X+2*(A-2)*c)-1, H=4A-5,
    Kpos=H*X*c-2*Kquad.

The private old ap=A-2 subtraction disappears. Five old projection gates
are replaced by five gates for Kpos, and the carrier uses Kpos. Every
other parent definition and all thirteen norm-tail gates are unchanged.
`equation.json` is the full polynomial schedule; `CUTS.json` accounts for
every parent and child row and operand.

## Positivity, soundness and the actual witness map

Kpos need not be positive at arbitrary positive inputs. The inherited
modulus noncancellation argument and Pell folding first recover all
integral roots, then c>8X*mu^2*Y^2>2X, before transport or q parity.
At this stage Kpos>0, so the original bad-transport contradiction may
drop its negative projection term. This order is essential.

After rank recovery, q parity and licensed partial fractions, the new
center gives H|P*Kpos, with P=q^3(q-1). Since H is odd, its exact identity
implies H|P*Kquad. Only the factor2 is inverted modulo H; P is never
cancelled through the possibly composite H. The retained strict
whole-product bound then recovers X=2^R and licenses all remaining CRT,
ratio and fresh positive source61 reconstruction, including positiveJ=1.
The full unbounded proof is in `PROOF.md`.

Any old positive zero supplies the integer kappa=Kquad/H. Set

    n_new=n_old+3*kappa-X*c.

The exact identity

    3*Kquad-H*X*c=3*(X^2-1)+(2A-7)*X*c>0

makes n_new strictly larger than n_old. All other inputs stay fixed,
and n_new+Kpos/H=n_old+Kquad/H, so the complete integer Z and norm
output agree. Conversely new soundness yields a finite refutation and
hence old canonical witnesses; no positive pointwise inverse n map is
assumed. The universal center identity with an explicitly supplied
quotient u is

    H*(n+3u-Xc)+Kpos-(H*n+Kquad)=3*(H*u-Kquad).

There is no unconditional polynomial input map involving an undefined
quotient, and no substitution of a sampled identity for the theorem.

## Entire leading component and independent checks

Kpos has degree4 in place of the old numerator's degree9. The complete
Z change has degree at most17, and its squared-center change has degree
at most84. An independent generic centered-norm expansion verifies that
the full new polynomial minus the old has degree at most360. Thus the
entire degree368 leading component is unchanged, not only one coefficient.
Its selected coefficient remains

    [J^184*i^20*w^40*Y^76*eta^40*alpha^4*F^4]P=2^28*beta^184>0.

The literal checker independently verifies all three projection/witness/
center ring identities, the entire operand map, topology/liveness,
operation count, all35 weighted norm coefficients, generic output
difference degree360, the seven-variable leading product and all copied
source/provenance bytes. It checks the complete frozen parent seal and
all four compressed/raw coefficient payloads.

Supplementary controls cover120 actual-port kernel/carrier instances,
120 quotient-licensed modular center/output restorations,50 exact signed
free-port instances, seven licensed exact integer restorations, two
actual-port degree368 lines and three rejected semantic corruptions.
These controls check transcription; they do not replace the unbounded
ordinary proof. The coherent BFS tuple with its different K0 remains a
separate specialization through the already proved coefficient-uniform
native/source theorem, rather than a pointwise identity with this tuple.

The ordinary positive-solvability/refutation equivalence is retained.
No new Lean or encoded object-ZFC derivation, proof of consistency, or
global simplicity minimum is claimed. The canonical page is untouched.

From the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_ten_positive_short_projection.py --check
python -B -O Computability/DiophantineConsistency/tools/build_ten_positive_short_projection.py --check
python -B Computability/DiophantineConsistency/candidates/ten-positive-short-projection/check.py
python -B -O Computability/DiophantineConsistency/candidates/ten-positive-short-projection/check.py
```

No historical native emitter or Lean process is executed.
