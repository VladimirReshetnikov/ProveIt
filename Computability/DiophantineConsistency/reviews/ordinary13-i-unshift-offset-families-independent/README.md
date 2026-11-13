# Independent review: infinite mod-3 offset families

The [reviewed packet](../../research/ordinary13-i-unshift-offset-families-mod3-obstruction/README.md) correctly excludes the stated five offset classes for the fixed-compact, power-of-two-q family under exact leading-power matching and `R=2n−1`. Its two integral-division arguments are sound. The result is the same exclusion as the separately developed [general-offset packet](../../research/ordinary13-i-unshift-mod3-general-offset-obstruction/README.md), expressed with an offset shifted by one; it is not an additional set of excluded classes.

The reviewed packet writes `d=L−h`; the earlier packet writes `d=L+1−H`. Thus `H=h+1`. The reviewed excluded classes `h≡0,2,3,5,6 (mod 9)` map exactly to `H≡1,3,4,6,7 (mod 9)`.

When h≡0 mod 3, h+1 is invertible modulo 3, so the matching formula reduces to `n≡L(2L+1)`. The corresponding `2n−1` is never 0 mod 3. When h≡2 or 5 mod 9, write h=3k+2; then 3 does not divide k+1. Integrality of n makes both numerator factors vanish modulo 3, so L=3t+2 and

```
(k+1)*n = 3*(t−k)*(2t−k+1).
```

Coprimality of k+1 and 3 implies 3|n, hence `2n−1≡2 mod 3`. This step uses the integer divisibility before reduction; it does not divide by a multiple of 3 in a residue field. Both branches contradict the source-level compact rank congruence R≡0 mod 3 when q is a power of two.

The receipt reproduces both authors' checkers and independently verifies the offset mapping and bounded integral matches. The symbolic argument, rather than finite controls, proves the family statement. It does not cover unmatched leading powers, shifted index relations, non-power-of-two q, other witness maps, arbitrary graph zeros, Lean/model proofs or provider/PDF validation. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-i-unshift-offset-families-independent/check.py | cmp - reviews/ordinary13-i-unshift-offset-families-independent/receipt.json
```
