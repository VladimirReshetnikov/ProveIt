# A signed binding that remains positive

The [candidate](candidate16.json) removes `dValueVariable` from the previously
finite-audited 17-variable graph. Its right-hand side `DstarComputed` contains
a subtraction, but is positive for every positive assignment when the fixed
port satisfies **beta ≥ 2**. The resulting sum of seven squares has 16 distinct
positive integer variables, 96 binary arithmetic rows, and exact degree 32
after specializing the four recorded fixed ports. A [guarded historical Lean author run](../../reviews/ipra-aq16-guarded-author/README.md)
compiled the full 52-module chain, including transport and native and standard
iPRA clients and passed an independent author-artifact audit. A subsequent
[historical pair](../../reviews/ipra-aq16-historical-retry-pair-terminal/README.md)
matched all 52 additions and passed an [independent complete-result audit](../../reviews/ipra-aq16-historical-retry-pair-independent-audit/README.md). No
formal PDF binding or global minimality is claimed.

The maintained [14-variable degree-30 equation](../../equation30-direct.pdf)
uses 90 circuit operations, so it is smaller on all three of those stated
metrics. This AQ16 construction is useful as a reduction along the freshly
rebuilt AQ29-to-AQ22 proof chain; its proof provenance and replay status are
tracked separately from the other equation's.

The [base-10 candidate display](equation32-16.pdf) lists all 16 positive
unknowns and its complete 96-operation circuit. An [independent audit](../../reviews/equation32-16-independent-audit/README.md)
checked the preceding PDF; a [separate review](../../reviews/equation32-16-wording-independent-audit/README.md)
passed for its exploratory-run wording. A [later review](../../reviews/equation32-16-paired-wording-independent-audit/README.md)
passed for the paired-run wording.
The fixed decoder and rank recipe
retain the project's documented manual-transcription boundary.

Write `q = 1 + J*beta`, `E = X*Y`, `a = E+Y`, `k = eta+zeta`,
`c = eta+Y*k`, `U = Y*q^2`, `H = 4*a+3`, and let `R` be the surviving
positive `rankVariable`. The original circuit has

```
shift = U*gamma + E*q - k + R + 1
DstarComputed = U*(X + a*c) + H*shift
```

An exact sparse integer-polynomial expansion checks the identity

```
DstarComputed = U*(X + a*eta) + (U*a*Y - H)*k
                + H*(U*gamma + E*q + R + 1).
```

Since the witnesses are positive and beta ≥ 2, `q ≥ 3`, `a ≥ 2`, and
`U*a*Y = Y^2*q^2*a ≥ 9*a > 4*a+3 = H`. Thus all three terms on the
right are positive. This is an integer identity; subtraction here is not
truncated natural subtraction. The actual recorded beta bytes equal
`2^94517 - 1`, so the required hypothesis holds. The linkage of those bytes
to the historical Lean port and PDF still has the previously documented
manually transcribed decoder and recipe boundary.

At an AQ17 zero the deleted `dDifference = dValueVariable - DstarComputed`
forces the coordinate to equal the displayed expression. Conversely, an AQ16
zero reconstructs that coordinate as the expression above, which is positive;
all seven retained residuals are identical and the deleted residual vanishes.
The program checks all eight residual substitutions by exact sparse polynomial
expansion and checks both output sum-of-squares trees. This proves equality of
positive-zero existence in ordinary integer mathematics under beta ≥ 2.

The `A0` residual still has the witness monomial `J^8 X^2 Y^4 eta^2` with
coefficient exactly `-beta^8` and no other port contribution at that witness
monomial. The maximum residual degree is 16, and the leading sum of squares
cannot cancel over the reals; since the actual beta is nonzero, the equation
has exact degree 32. Positive-variable shifting preserves the degree.

Run the generator/checker with ordinary Python from the repository root:

```sh
python3 Computability/DiophantineConsistency/research/aq17-positive-signed-binding/generate.py
```

The checker refuses to overwrite a different candidate, rejects optimized
Python, and exercises a wrong-sign identity, corrupted residual operation,
and output-sign mutation. The [terminal observation](terminal-observation.json)
records the actual exit. An [independent finite audit](../../reviews/aq16-independent-audit/README.md)
also checks the substitution, positivity and exact degree with a separately
represented sparse polynomial calculation; it is not a Lean replay.
