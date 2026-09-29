# Radical Pell-replacement cost audit after 97

This is an exploration note, not a new universal certificate or a lower-bound
claim. The frozen round-29 certificate remains the proved result. Fixed
numerals and equality tests are free; every addition, subtraction-as-reverse-
addition, and multiplication is counted. Adding unknowns is permitted.

The current certificate spends 39 operations through the definition of `r`
and 58 afterward. The latter block establishes the binomial divisibility,
the necessary power-of-two condition, and the variable-radix exponent
`q = B^L` together. A replacement must establish all three.

## Reproducible counts

Run `python current/verification/explore_round29_radical_pell_cost.py`.
The script checks the algebraic rewrites and final residuals compositionally
and emits the full primitive schedules in the adjacent JSON file.

| Construction audited | Multiplications | Additions | Total |
|---|---:|---:|---:|
| Terse exponentiation, one general call | 31 | 20 | 51 |
| Norm-4 bridge, specialized to `g=1` | 45 | 24 | 69 |

These are favorable direct expansions: their input-domain conversions are
not included. They are exact counts of the displayed DAGs, not proofs that
no smaller DAG for either mathematical construction exists.

## Terse exponentiation

The source is Figure 2 of [Luca Vallata and Eugenio G. Omodeo, *A
Diophantine representation of Wolstenholme's pseudoprimality*
(2015)](https://ceur-ws.org/Vol-1459/paper31.pdf), which attributes the
exponentiation construction to Matiyasevich and Julia Robinson (1975).
It specifies one relation `x^n=y`. Its Pell-index layer uses three Pell
expressions and requires their product to be a square, a divisibility
condition, and an order condition. Its outer layer adds another Pell-square
test and an approximation inequality.

The count includes two supplied square roots, one divisibility quotient,
and an inequality slack. In the displayed source, `C=B+k` already provides
the needed order condition, so that condition is not charged again.
Replacing `4*n*(y+1)` with `4*(n*y+n)` shares `n*y` with the approximation
inequality and removes one multiplication from an otherwise direct
52-operation expansion. The three-factor square test itself costs three
operations: two products and the supplied root's square. No high powers
are treated as primitives.

One such 51-operation call does not provide the three obligations of our
58-operation block. A direct binomial-ratio implementation additionally
needs the powers with bases `U+1` and `U`, a sufficiently large power-of-two
`U`, and `q=B^L`. There is no proved way in this audit to merge those calls
into one. Accordingly the small number of quantified variables in the
source is not an operation-count improvement here.

The quotient sign, nonnegative-input encodings, and slack endpoint are
deliberately left as source-domain obligations rather than silently
converted to positive unknowns. Charging such conversions can only raise
the count of this particular direct implementation.

## Lucas norm-4 bridge

The source is Definition 10 and Theorem 11 of [*A Formal Proof of
Complexity Bounds on Diophantine Equations*
(2025)](https://arxiv.org/html/2505.16963v1). It combines a power-of-two
predicate with central-binomial divisibility using Lucas sequences and
the norm equation `X^2-(A^2-4)Y^2=4`. The theorem has explicit lower bounds
on its six witnesses and its three principal parameters.

The 69-operation schedule fixes the free precision parameter `g=1` and
uses these exact factorizations of its longer aliases:

```
G = 1 + C*D*F - 2*(A-2)*((A*A-4)*E*E)
H = C + F*(B+(2*y-1)*C).
```

The first reuses the product already needed for `F`; the second avoids
separately computing both multiples of `F`. The product `D*F` also serves
both `G` and the final square test. The first bridge scale `ell*Y` is
shared with the final ratio inequality. Both square predicates, the
divisibility quotient, and the strict inequality slack are counted.

The six witness lower bounds are omitted from this favorable count.
Literal positive-witness shifts would add six operations. Taking
`X=r`, `Y=n^2`, and bridge `b=n` fits the existing preliminary bounds:
the positive packed terms give
`r >= (n^2-n)+(n^2-1) >= 3*n` for `n>=4`. Thus the theorem's
`X>=3b` condition is not the obstruction.

The obstruction in this direct approach is its arithmetic size. The
69-operation bridge alone exceeds the entire current 58-operation Pell
block, and it does not yet express `q=B^L`. Keeping the present 39-operation
coding prefix would already reach 108 before that missing exponent and
the witness-bound conversions. This rules out the audited direct
substitution, while leaving open a substantial redesign of the bridge.

## Result of this bounded lane

No improvement below 97 follows from either audited replacement. The
useful reusable artifacts are the full DAGs, the shared-product rewrites,
and the explicit list of obligations that cannot be counted as free.
