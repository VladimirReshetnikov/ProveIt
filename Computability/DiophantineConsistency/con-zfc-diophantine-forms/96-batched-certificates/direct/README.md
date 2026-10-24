# Shared arithmetic certificates for a direct Con(ZFC) quartic

This component supplies an ordinary polynomial in **667 nonnegative integer
variables**, of exact degree four, with 23,747 expanded monomials. It is the
sum of the squares of 535 explicitly listed quadratic residuals. The maximum
absolute expanded coefficient is 2,649,643,818,040.

It refines the direct C222 proof-certificate construction in
`ConZFC_Shared_Certificates_2026-10-24.zip`. That inherited construction uses
3,614 nonnegative variables. The transformations here preserve existence of
a certificate: a common binomial radix, one offset for signed congruence
quotients, a shared Pell frame for all power graphs, and exact monic
coordinate eliminations. The ordinary proof is intended to be composed with
the inherited C222-to-ZF and ZF-to-ZFC refutability calibrations, formalizably
in ZFC. No consistency assumption is used by these reductions.

The construction uses no K215 machine or Jones universal polynomial. Its
667-variable count improves the directly compiled small-coefficient quartic
route; it is not a variable-count record against the existing nine-positive
or ten-integer equations, whose degrees and coefficients are much larger.
No global minimality or worldwide priority claim is made.

## Supplied equations

| Directory under `output/` | Nonnegative variables | Quadratic residuals | Quartic monomials | Maximum absolute coefficient |
| --- | ---: | ---: | ---: | ---: |
| `common_radix` | 2,108 | 1,745 | 10,629 | 127,777,275 |
| `common_radix_offset` | 1,968 | 1,717 | 10,545 | 127,777,275 |
| `shared_frame` | 1,153 | 1,021 | 9,234 | 127,778,299 |
| `compact667` | 667 | 535 | 23,747 | 2,649,643,818,040 |
| `compact680` | 680 | 548 | 18,302 | 690,871,812,080 |

Each `equation.json` fixes its complete coordinate order and every quadratic
residual. The single polynomial is the sum of their squares.
`expanded_polynomial.json` lists the entire ordinary integer polynomial.
A monomial is a sorted list of coordinate indices, with repetitions denoting
powers and the empty list denoting the constant monomial. There are no
variable exponents, division, factorials, binomial functions, bounded
quantifiers, or unspecified coefficient ports in those files.

The two compact forms retain the complete monic elimination certificates,
including the reverse polynomial restoration of every deleted coordinate.
The 680-variable form trades thirteen extra variables for fewer terms and a
smaller coefficient height. The 1,153-variable form has substantially smaller
coefficients and is retained as a separate useful working point.

## Reproduction

Python 3.10 or later and its standard library suffice. All commands work
offline. From this directory:

```sh
python3 verify.py
python3 -O verify.py
python3 verify.py --rebuild
```

The default verifier only reads the delivered files. `--rebuild` constructs
all five equations and the shared-frame fixture in a temporary directory,
then compares sixteen primary files byte for byte. Optional `--receipt PATH`
writes the verification report to the explicitly chosen path.

Individual construction commands are:

```sh
python3 build_common_radix.py --shared-offset --shared-frame --output /tmp/shared-frame
python3 terminal_elimination.py /tmp/shared-frame/equation.json /tmp/compact667 --max-support 16 --expand
python3 terminal_elimination.py /tmp/shared-frame/equation.json /tmp/compact680 --max-support 16 --quadratic-first --expand
```

Use an output directory distinct from this release when experimenting.

## Verification boundary

`audit_common_radix.py` imports no builder. It checks the raw quadratic gate
graph, independently reconstructs the nonnegative affine projection,
compares all new radix/frame/congruence identities over integer polynomial
rings, checks the actual call-site positivity order, and independently
expands the final coefficient dictionaries.

`verify_projection.py` imports no elimination optimizer. It replays every
monic substitution, checks reverse restoration and the degree bound, and
rejects a deliberately corrupted restoration. The fixture file checks all
80 literal rows of the shared frame for the powers 2^1 and 3^1. A separate
small-parameter certificate exercises distinct indices 1 and 2 and a pooled
matrix period modulo 64.

These finite checks support transcription, exact counts and implementation.
The unbounded Pell/CRT arguments, the source-calculus calibration and their
formalizability in ZFC are separate mathematical arguments. This contribution
does not contain a new end-to-end Lean/Rocq or object-ZFC proof term and does
not prove that the complete polynomial lacks solutions.

## Provenance and licensing

`PROVENANCE.json` records the exact incoming ZIP hash and the unmodified
upstream builder, numerical calculus and source-predicate hashes. The
`upstream/` directory preserves their source and immediate mathematical
provenance, together with the inherited license and notices. The common
radix and positivity notes are in `common_radix_section.tex`; the full
article in the parent package supplies the shared-frame and equivalence
proofs. New code follows the ProveIt repository's MIT No Attribution license.
