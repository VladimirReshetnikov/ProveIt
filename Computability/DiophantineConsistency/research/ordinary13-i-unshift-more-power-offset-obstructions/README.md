# Further fixed-port power-match obstructions for i-unshift

This packet extends the [two earlier matched-index obstructions](../ordinary13-i-unshift-fixed-shifted-power-modular-obstructions/README.md). It gives new necessary-congruence obstructions for other offsets, not a proof that the i-unshift graph has no zero or that an existential zero map exists. All claims are ordinary-integer arithmetic at the exact symbolic compact ports, and no Lean/model/provider result is asserted.

Use the same power-match family: `Y=2^L`, `X=2^m`, `m=n+d`, and `P=2XY`, `Q=4XY²`. Exact equality of the leading powers `P^(m−1)=2Y*Q^(n−1)` is equivalent to

```
n*(L+1−d) = d*(d+L+1).
```

Set `h=L+1−d>0` and also impose the proposed exact index relation `R=2n−1`. Eliminating n gives the necessary integer identity

```
h*R = 4L²+(8−6h)L+2h²−7h+4.          (1)
```

The pinned compact recipes give beta≡MC≡MF≡1 mod 3. Whenever `q=1+beta*J` is a power of two, q²≡1 mod 3 and J≡q−1 mod 3; the actual graph rank therefore satisfies `R≡J(1+q)≡0 mod 3`, for **every** natural J in this power-of-two-q case.

If `h≡1 mod 3`, the right side of (1) is `L²+2L+2`, which is 2, 2 or 1 modulo 3. Thus no such matched witness exists. This rules out the entire indicated offset class, including d=L−3 and d=L−6, as well as the already known d=L case.

Two more offsets are excluded for every J with q a power of two by including integrality of n:

* For `h=3`, or d=L−2, the matching identity is `3n=(L−2)(2L−1)`. Integrality requires L=2+3j and then `n=3j(1+2j)`, so `R=2n−1≡2 mod 3`.
* For `h=6`, or d=L−5, it becomes `3n=(L−5)(L−2)`. Integrality again requires L=2+3j and then `n=3j(j−1)`, so R≡2 mod 3.

For `h=5`, or d=L−4, a different fixed-port prime rules out the J=1 case. Let `p=761838257287`; the checker verifies primality by complete trial division and `2^67≡1 mod p`. Thus beta≡0 and q≡1 mod p. Direct evaluation of the exact low/high digit recipes gives `MC≡761838256300`, `highNat≡564148635659`, so the actual J=1 graph rank is `R≡564148634672 mod p`. Equation (1) becomes `5R=4L²−22L+19`; completing the square gives

```
(4L−11)² ≡ 20R+45 ≡ 617237091467 (mod p).
```

Euler's criterion evaluates the right side to p−1 at exponent (p−1)/2, so it is a quadratic nonresidue. This excludes d=L−4 for J=1. It does **not** exclude other J for this offset; their rank residue is J times the indicated mask sum.

The checker reproduces the prior receipt, pins graph and exact compact recipes, computes the residues without expanding large constants, verifies the prime and Euler test, and exercises the exponent and rank identities on bounded integers. The displayed modular reasoning supplies the general proof. None of the results covers non-power-of-two q, nonmatching leading powers, a shifted `R=2n−1`, other Pell-index constructions, arbitrary witnesses, a graph zero/nonzero claim, or a PDF endpoint. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-i-unshift-more-power-offset-obstructions/check.py | cmp - research/ordinary13-i-unshift-more-power-offset-obstructions/receipt.json
```
