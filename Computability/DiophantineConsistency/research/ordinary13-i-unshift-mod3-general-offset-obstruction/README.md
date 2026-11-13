# A general mod-3 exclusion for matched i-unshift offsets

This is a source-only strengthening of the [preceding offset packet](../ordinary13-i-unshift-more-power-offset-obstructions/README.md). In the same fixed-compact, exact-leading-power family with positive offset `h=L+1−d`, exact rank `R=2n−1`, and q a power of two, it excludes every `h≡1,3,4,6,7 (mod 9)` for **any** natural J. It does not exclude the i-unshift graph's other witnesses, establish graph-zero nonexistence or an iPRA theorem, or cover q that is not a power of two.

The preceding packet establishes that the actual fixed-compact rank satisfies R≡0 mod 3 whenever q is a power of two, and that exact leading-power matching entails

```
h*n = d*(d+L+1),   d=L+1−h,   R=2n−1.
```

The previously proved case h≡1 mod 3 excludes h≡1,4,7 mod 9. To handle h≡3 or 6 mod 9, write h=3u with gcd(u,3)=1. The matching equation modulo 3 forces L≡2 mod 3. Set L=2+3j. Then

```
d = 3(j+1−u),
d+L+1 = 3(2j+2−u),
u*n = 3(j+1−u)(2j+2−u).
```

Since u is coprime to 3, n is divisible by 3, hence R=2n−1≡2 mod 3, a contradiction. This includes all h with 3 dividing h exactly once, not just the earlier h=3 and h=6 examples.

The checker reproduces the predecessor receipt and tests bounded integer matches against the congruence proof. The displayed number-theoretic derivation establishes the quantified exclusion; those finite tests are controls only. The other residue classes of h, shifted index relations, nonmatching power families and all unrestricted graph witnesses remain open. No huge constants or Pell ordinates are expanded, and no Lean process, build, provider/axiom validation or PDF binding is involved. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-i-unshift-mod3-general-offset-obstruction/check.py | cmp - research/ordinary13-i-unshift-mod3-general-offset-obstruction/receipt.json
```
