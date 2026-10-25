# Three compact positive-integer equations for Con(ZFC)

This packet gives three completely specified ordinary polynomials in the same
ten strictly positive integer variables. Their lack of a positive zero is
ZFC-provably equivalent to Con(ZFC), by the ordinary arithmetic proof in
`PROOF.md` composed with the explicitly retained native/refutation calibration.

| Literal circuit | Positive unknowns | Live binary operations | Exact degree |
| --- | ---: | ---: | ---: |
| `equation77.json` | 10 | 77 | 626 |
| `equation78.json` | 10 | 78 | 464 |
| `equation79.json` | 10 | 79 | 460 |
| Frozen first parent | 10 | 78 | 630 |
| Frozen second parent | 10 | 79 | 468 |

The first two new equations strictly improve both operation count and degree
over their corresponding parents. The third lowers the second parent's degree
by eight while preserving its operation count. Other constructions trade more operations for much
lower degree. This packet does not claim a global simplicity optimum.

The mathematical change is to use `XY` or `q^4` as the carrier
denominator in place of `Y^2`. A known divisor `q^4` is already large enough
to identify the first Pell index. The full denominator is recovered after
that index is known. Reusing `XY` to evaluate both Pell bases saves one
multiplication; the smaller degree of the carrier saves four total degrees.

## Complete equation

The only unknowns are `J,F,alpha,i,T,w,s,n,eta,zeta > 0`. The four ports
`beta,K0,MC,MF` are fixed integer coefficients, **not unknowns**. Their exact
bytes and complete finite recipe are included. The largest port has 592,884
bits. The polynomial abbreviations and single final equation are all printed
in `PROOF.md`. Every row of a JSON circuit is one ordinary addition,
subtraction, or multiplication; there is no variable exponent or division.

This compact branch retains the inherited native/K215 calibration. The
separate direct-calculus construction in the enclosing research delivery is
the route that avoids K215 and a large coefficient tuple.

## Reproduce

Python 3.10 or later and its standard library suffice:

```sh
python3 -B build.py --check
python3 -B verify.py
python3 -B -O verify.py
python3 -B rebuild_coefficients.py
```

The builder reads the frozen parent circuits as JSON and imports no parent
program. The verifier imports no builder. It independently checks 28 exact
free-polynomial identities per circuit, covering every gate; all leading
homogeneous coefficients; circuit liveness and operation counts; four exact
coefficient reconstructions; frozen-source hashes; and actual-coefficient
modular controls. Deliberate algebraic mutations must be rejected. The
verifier was adapted from the explicitly retained parent checker, so its
independence is from the constructor, not independent invention of every
checking routine.

`CHECK.json` and `CHECK_OPTIMIZED.json` record the completed runs. These finite
checks authenticate equations and algebra. The unbounded equivalence with
syntactic ZFC refutability is the written proof and its identified ordinary
dependencies; no new end-to-end Lean, Rocq, or object-language ZFC proof
certificate is claimed.

## File map

- `PROOF.md`: complete definitions, new theorem, both directions, exact sizes.
- `equation77.json`, `equation78.json`, `equation79.json`: the full literal arithmetic circuits.
- `build.py`, `verify.py`: independent construction and checking paths.
- `coefficients/`, `rebuild_coefficients.py`: exact fixed numerals and recipe.
- `parent/`: immutable immediate predecessor equations and proof material.
- `proof_sources/`: retained ordinary Pell, rounding, and native calibration.
- `SOURCE_PINS.json`, `PROVENANCE.json`: source hashes and archive identity.
- `licenses/`, `NOTICE.md`: attribution and inherited notices.

The mathematics, implementation, and exposition were developed with AI
assistance. The new result is the proved carrier substitution and the three
checked circuits, not a new consistency proof or a claim of human refereeing.
