# The four candidate generating functions

The candidate order below is the order fixed before the recorded draw.
All were explicitly labeled conjectural in the inspected OEIS records.
These expressions are retained for audit, not as assertions that the
three unselected candidates are proved.

## 1. A225114

Skew partitions of n whose diagrams have no empty rows and columns.
Conjecture by Mikhail Kurkov, September 3, 2024.

    1 / (2 - 1/(1 - x/(1 - x/(1 - x^2/(1 - x^2/(1 - x^3/(1 - x^3/(1 - ...)))))))).

The continued fraction repeats each positive exponent twice.
Source: https://oeis.org/A225114

## 2. A244475

Fifth-largest distinct term in the n-th row of Stern's diatomic triangle.
Conjecture by Alois P. Heinz, June 20, 2022.

    -x^3*(x^14+x^13+x^12+2*x^11+3*x^10+5*x^9+8*x^8
           +x^7+3*x^6+3*x^5+2*x^4+4*x^3+5*x^2+2*x+1)/(x^2+x-1).

Source: https://oeis.org/A244475

## 3. A289587

Permutations avoiding 321 and mesh pattern (12,174); the entry also
identifies the equinumerous class for mesh pattern (12,234).
Conjecture by Thomas Scheuerle, December 23, 2025.

    (x^4+4*x^3+11*x^2
      -(x^2+5*x+3)*sqrt(x^4-2*x^3-5*x^2-2*x+1)+10*x+3)
      /(8*x*(x+1)^2).

The formal square root has constant term 1.
Source: https://oeis.org/A289587

## 4. A381190 — selected

Connected minimal dominating sets of the n-trapezohedral graph.
Conjecture by Joerg Arndt, January 7, 2026.

    -2*x^3*(4*x^5+8*x^4+4*x^3-9*x^2-8*x-3)/(x^3+x^2-1)^2.

Source: https://oeis.org/A381190

The original OS-random draw returned index 3 (zero-based). There was no
reroll. Only candidate 4 is resolved in this package.
