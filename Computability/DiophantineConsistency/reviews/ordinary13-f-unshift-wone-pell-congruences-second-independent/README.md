# Independent review: fixed F-unshift w=1 Pell constraints

The reviewed `research/ordinary13-f-unshift-fixed-wone-pell-congruences/` gives necessary standard-integer conditions for a full zero at the **fixed compact tuple with J=1, F=0, C>0 and w=1**. It does not exclude the slice, supply a zero, or prove a model/iPRA theorem.

The earlier independently checked kernel gcd for w≡1 mod beta, together with the first signed norm, gives `C=beta=q−1` and `alpha=1`. The actual rank then satisfies `R+1≡MC mod q`. Its least base-`2^67` low-mask digit is `2^67−2`, so `MC≡−2 mod 2^67`. Combining this with the preceding norm result `2n≡R+1 mod q^5` yields `n≡−1 mod 2^66` and hence `n≥2^66−1`.

For both possible signs of the actual main signed root, put `a=q³s(q+1)`, `H=4a+3` and `U=q^5s`. Since q is a power of two, H is odd; since H≡3 mod s, `gcd(H,U)=gcd(H,s)=gcd(s,3)=g`. The literal root equation therefore requires `d−a*c≡q mod H/g`. The positive Pell root satisfies `x_m−a*y_m≡2^m mod H`. Its conjugate is the inverse modulo H because their product is `1+H*y_m²`. Thus the positive and negative root branches give respectively

```text
2^m ≡ q (mod H/g),       −2^(−m) ≡ q (mod H/g).
```

These are necessary conditions only. For `3∤s`, g=1, and fixed N odd gives q≡−1 mod 3 while H is divisible by 3. The first congruence forces m odd and the second m even. The main multiplier is even, so c=y_m has the parity of m; since Y is even, eta has the same parity. The parity conclusion does not follow from this mod-3 argument when 3 divides s.

In the negative branch with 3∤s, c is even and `I=c²i` is divisible by 4. The actual strong unit equation modulo 8 then forces f odd, and the auxiliary unit equation modulo 4 forces y odd. The preceding strong/auxiliary result supplies y≥2, hence y≥3; it still leaves the auxiliary Pell-index/positive-T condition unresolved.

The independent checker pins the literal and compact digit sources, reproduces the author's receipt, and runs a separate 1,440-case recurrence check of the gcd, both sign formulas and their parity implications. It also independently exhausts the negative-branch modular parity conditions. These controls supplement the universal calculations above; they do not validate a Lean proof or decide a graph zero.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-f-unshift-wone-pell-congruences-second-independent/check.py | cmp - reviews/ordinary13-f-unshift-wone-pell-congruences-second-independent/receipt.json
```
