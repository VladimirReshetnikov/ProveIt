# One Pell cap for modular binomial arithmetic and signed pairs

This component supplies four complete explicit Diophantine equations.
Every final equation is the sum of squares of its entire listed quadratic
residual set; the complete collected quartic is supplied beside it.

| Endpoint | Domain | Variables | Rows | Quartic terms | Coefficient height |
|---|---|---:|---:|---:|---:|
| equation240/natural | Nonnegative integers | 240 | 188 | 25,987 | 90,589,484 |
| equation239/natural | Nonnegative integers | 239 | 187 | 360,097 | 491,869,488 |
| integer381 | Unrestricted integers | 381 | 225 | 13,179 | 2,445,790,974,704 |
| integer391 | Unrestricted integers | 391 | 235 | 10,764 | 80,496,640 |

All four have exact degree four. The 240-variable form is a more balanced
representation than the very dense 239-variable companion. The 391-variable
integer form trades ten variables for much smaller coefficient height than
the 381 form. No comparison is presented as a global minimum.

## Mathematical contribution

`PROOF.md` proves the natural composition. It adds all eleven modular
numerator indices to the common size frame, permitting a single indexed
Pell cap to replace fifteen full indexed certificates. A separate cofinal
Pell parameter makes the enlarged frame compatible with the common-root
congruence used for the binomial residues. There are six exact powers,
eleven modular digit requests, and one factorial/CRT binomial.

`SIGNED_CAP_PROOF.md` gives a new oriented cap. For signed Pell pairs,

    V = W + 1 + sum_i Y_i^2 + s,
    sum_i[(Y_i-k_i)^2+(X_i-1)^2] = (A-1)Q

simultaneously forces every index and both coordinate signs when the
large square frame is used. Thirty principal coordinate sign guards
disappear. Sequential power recovery also makes the output, modulus and
divisibility-quotient sign guards unnecessary premises. The final source
uses 52 explicit three-square nonnegativity graphs.

Together with the retained C222/refutation calibration, ordinary mathematics
formalizable in ZFC proves that each equation has no solution in its stated
domain if and only if Con(ZFC). This is not a proof of consistency, a new
end-to-end Lean/Rocq proof object, or a claim of worldwide priority. K215
execution and Jones's universal polynomial are not used by this route.

## Readable literal data

Each JSON term `[c,[i,j,...]]` means `c*z_i*z_j*...` with zero-based indices.
An empty index list denotes a constant. The ordered variable array fixes
the interpretation. No coefficient port or domain condition is implicit.
`expanded_polynomial.json` contains every collected coefficient of the
single sum-of-squares polynomial.

## Offline verification and reconstruction

Python 3.10 or later with its standard library is sufficient. From this
directory:

```sh
python3 -B verify.py
python3 -B check_signed_cap.py integer381
python3 -B check_signed_cap.py integer391
python3 -B reproduce.py
```

Run the three checkers with `-O` as well. For optimized reconstruction use
`python3 -B reproduce.py --mode optimized`.

The natural verifier checks the 468-row inherited prefix, all 60 affected
semantic row identities, 428 affine restorations, natural contractions and
every coefficient. The integer verifier independently derives the three
changed rows, checks every guard and all 174 row sign consequences, verifies
all fifteen indices positive before powers, checks the ordered base
schedule, replays all integer restorations and re-expands the entire
quartic. Both use explicit exceptions and algebraic corruption controls.
Neither imports an equation producer or optimizer. Reproduction runs
fresh producers in temporary directories and demands byte-identical
endpoint files. Finite checks verify syntax and finite algebra; they do
not replace the ordinary unbounded proof or inherited logic.

To generate fresh outputs at an explicit destination:

```sh
python3 -B build.py --output NEW240 --support-cap 32
python3 -B build.py --output NEW239 --support-cap 96
python3 -B build_signed_cap.py --output NEW381 --late-signs
python3 -B build_signed_cap.py --output NEW391 --late-signs --affine-support 4
```

## Provenance

The repository comparison pin is
`f4d8db99e060339f3306a04d507c35bc1d0d68c5`.
The direct source and modular arithmetic come from the incoming
`ConZFC_Shared_Binomial_Certificates_2026-10-24.zip`; the natural cap comes
from `ConZFC_Shared_Pell_Bound_261_2026-10-24.zip`. The generic signed monic
projector and elementary sign-inference producer come from
`ConZFC_Unified_Binomial_Even_Indices_Round15_2026-10-24.zip`.
These preexisting mechanisms are credited explicitly. The new work is
their rigorously checked enlarged-frame composition and the oriented
signed-cap theorem and its complete integer equations.

Imported files retain their licenses and notices. New work is AI-assisted
research supplied under the accompanying MIT No Attribution license.
Independent review in this packet means a separate mathematical or
computational review within this workflow, not external human endorsement.
