# Explored reductions that are not claimed

The baseline was the current 31-positive-variable quartic with 22 quadratic
residuals and a 60-operation comparison circuit, together with the inherited
67-operation scalar equation and 59-operation higher-degree system.

1. Rewriting a Pell equation with Delta=A^2-1 as D^2+c^2=(Ac)^2+1 does
   remove Delta from that one equation. Across the full strong-index and
   auxiliary constraints, however, the required product witnesses replace
   the same number of existing auxiliaries. No reduction below 31 variables
   or below the existing operation counts was established.

2. A potential way to eliminate the positive variable h is to merge the
   congruence E | (k-R-1) into the radical carrier already used to enforce
   the main Pell-root congruence modulo H. A direct homogenized construction
   gives only E | H(k-R-1) and H | E(g-b0). Without an independent bound or
   coprimality theorem for gcd(E,H), this does not recover the two required
   congruences. Establishing X=2^R first would be circular because that step
   itself needs the unweakened main-root congruence. No eleven-positive-variable
   form is claimed.

These are possible research directions, not incomplete proofs of new records.
