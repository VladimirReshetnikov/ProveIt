# An explicit quartic over 8,619 unrestricted integers

The complete ordinary polynomial is [expanded_polynomial.json](expanded_polynomial.json). Equivalently, it is the sum of the squares of all residuals in [equation.json](equation.json). Every variable ranges over all integers.

| Variables | Quadratic residuals | Exact degree | Nonzero monomials | Coefficient height |
|---:|---:|---:|---:|---:|
| **8,619** | **4,619** | **4** | **39,811** | **127,285,349** |

This is the unrestricted-integer companion of the frozen 3,609-natural-variable prime-lift equation. It preserves that entire residual system and adds one quadratic nonnegativity guard for each of its 1,670 semantic inputs. The 1,939 arithmetic gate wires need no separate guards. There are no large native constants, variable exponents, bounded quantifiers, factorials, binomials, or external compiler choices in the final polynomial file.

## Integer/natural equivalence

For each semantic input x introduce three fresh unrestricted integers a,b,c and append

\[
x-a^2-b^2-c(c+1)=0.
\]

For every integer c, `c(c+1)>=0`, so this equation forces x to be natural. Conversely every natural x has such a representation: Legendre's three-square theorem applies to `4x+1`, which is 1 or 5 modulo 8 and is not divisible by 4. Exactly one representing square is odd and two are even. Write them `(2c+1)^2,(2a)^2,(2b)^2`, subtract 1 and divide by four.

Every retained gate wire has a monic defining equation whose right side is a polynomial with nonnegative coefficients in earlier retained coordinates. This property holds after the original nonnegative affine substitutions. Starting from the now guarded semantic inputs, topological induction forces all 1,939 gate values to be nonnegative. Thus an integer zero of the new system is a natural zero of the parent. Conversely a natural parent zero extends by the three-square theorem to an integer zero of the new system.

Only **additional residuals** are appended. No square expression is substituted into the parent's residuals, so the construction preserves the quadratic row bound and quartic final degree. The count is

```text
variables = 3609 + 3*1670 = 8619
rows      = 2949 + 1670   = 4619.
```

A fresh guard auxiliary has fourth-power coefficient 1 in the final polynomial and occurs nowhere else. Hence the degree is exactly four, independently of any generic degree bound. Full expansion confirms all 39,811 terms and the stated coefficient height.

The parent source has ordinary existence equivalence with the repository's syntactic ZFC refutation predicate, by the prime-lift CRT proof, actual C222 calibration, and finite Pell-based arithmetic graphs. Composing the equivalence above and negating gives the ordinary ZFC-formalizable equivalence between absence of integer zeros and Con(ZFC). No consistency or unsolvability assertion is proved here. Lean formalization remains paused; no new kernel-checked compiler theorem or object-language ZFC derivation is claimed.

## Reproduction

From the repository root:

```sh
python3 Computability/DiophantineConsistency/tools/build_shared_crt_prime_lift_integer.py --check
python3 -O Computability/DiophantineConsistency/tools/build_shared_crt_prime_lift_integer.py --check
python3 Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/integer/check.py
python3 -O Computability/DiophantineConsistency/candidates/shared-crt-prime-lift/integer/check.py
```

The generator authenticates the frozen natural parent and adds the displayed guards. It writes new integer files only. The checker imports no builder: it compares the complete original prefix, verifies exact coverage of all semantic inputs and freshness of all 5,010 auxiliaries, checks every nonnegative topological gate definition directly, and independently expands the full squared system. It also checks 1,001 small three-square representations as controls; the universal completeness proof is Legendre's theorem above. The natural source, natural candidate, and incoming archives are unchanged.
