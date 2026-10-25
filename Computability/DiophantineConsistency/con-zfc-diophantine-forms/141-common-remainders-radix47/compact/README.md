# Smaller carrier denominators: three explicit ten-positive equations

This self-contained component supplies three ordinary integer polynomials in
the ten strictly positive unknowns

```text
J, F, alpha, i, T, w, s, n, eta, zeta.
```

Their lack of strictly positive solutions is provably equivalent in ZFC to
Con(ZFC), by the new denominator lemma and the retained native/refutation
calibration. All four fixed coefficient integers are supplied as exact bytes,
with a finite independent reconstruction recipe.

| Literal circuit | Carrier denominator | Weight | Live binary operations | Exact degree |
| --- | --- | --- | ---: | ---: |
| `equation_78_626.json` | X Y | V squared | 78 | 626 |
| `equation_79_464.json` | X Y | b V | 79 | 464 |
| `equation_80_460.json` | q to the fourth | b V | 80 | 460 |

The matched incoming parents have 78 operations at degree 630 and 79 operations
at degree 468. Replacing the carrier denominator Y squared by X Y lowers each
degree by four at unchanged cost. The q-to-the-fourth companion lowers degree
to 460 at a cost of one additional multiplication. These are concrete
cost/degree tradeoffs, not claims of global minimality.

## The new argument

Keep the first Pell norm based on X times Y squared unchanged. Only its later
carrier denominator changes. The replacement theorem applies to every
positive D satisfying

```text
D > 2,        q^4 divides D,        D divides 4 X Y^2.
```

The first-index recovery needs only the q^4 divisibility. After that index is
known, the full Pell congruence supplies 4 X Y^2 dividing its error, and hence
D divides the error. This separates the early index-recovery modulus from
the later complete denominator. The X Y variant reorders two already present
multiplications, so it adds no operation.

`DENOMINATOR_PROOF.md` proves both directions, including positive completeness
with freshly constructed witnesses. `upstream/parent/PROOF.md` and its entire
`proof_sources/` directory retain the inherited Pell and native calibration.

## Exact specification and coefficient size

Each JSON file is a complete acyclic arithmetic graph using only addition,
subtraction, multiplication, and literal constants. Its only quantified inputs
are the ten unknowns above; intermediate registers are polynomial abbreviations.
Its four fixed coefficient ports are beta, K0, MC, and MF. Their literal
little-endian integer byte strings are in `coefficients/`; compression is only
a storage format. The largest coefficient, K0, has **592,884 bits**. This
compact-circuit branch therefore optimizes unknown and operation counts while
retaining very large fixed coefficients.

The whole coefficient tuple is inherited coherently from the indexed native
construction. Its finite 436-character source recipe, complete ordinary proofs,
parent circuits, and original notices are preserved unchanged under
`upstream/parent/`. This branch retains that native machine-derived calibration;
it should not be confused with the separate direct C222 quartic construction.

## Verify and rebuild

Only Python 3.10 or newer and its standard library are required:

```sh
python3 -B verify.py
python3 -B build.py --check
```

Both commands work when invoked by an absolute path from another working
directory. To write freshly reconstructed JSON files into a separate directory:

```sh
python3 -B build.py --output-dir /path/to/rebuilt
```

The independent verifier imports no producing builder. It checks immutable
source hashes, the exact allowed source changes, all graph dependencies and
liveness, every register through exact free-polynomial identities, the two
denominator divisibility identities, and the complete leading homogeneous
polynomial. The nonzero leading coefficients establish the stated exact total
degrees, not merely upper bounds. It also reconstructs all four fixed numerals
and checks the actual compressed and uncompressed bytes. The supplied
`VERIFICATION.json` records the completed checks.

All 38 files of the original compact parent were retained byte for byte. Their
identities, the incoming ZIP hash, and the comparison commit
`55d1f72aedebf892e446c90d35fa1ae37689b0f2` are recorded in `SOURCE_PINS.json`.

The verification is exact finite algebra. The ZFC equivalence additionally uses
the stated unbounded mathematical proofs and inherited logical calibration.
No new end-to-end proof-assistant derivation, consistency proof, or
literature-wide priority claim is asserted.
