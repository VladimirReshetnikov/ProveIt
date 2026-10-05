# Correction: the exceptional set constrains the base prime

The fixed-quotient theorem in the frozen
`direct_X_short_period_lucas_obstruction_pascal.md` is unchanged. Its opening
must instead read:

> For a canonical direct-X index R=2h*p^e-2j+1, with h and j fixed and
> p^e>2j, the base prime p divides Y_R exactly when it belongs to the
> explicit finite exceptional set of prime divisors of N_(h,j). This set
> is independent of e.

Only the designated base prime p is tested. There is no assertion that
all odd prime divisors of the integer Y_R belong to that finite set.

**Correction remark 2 (retained overbroad opening).** The original opening
said “the odd primes dividing the half-binomial scale belong to an explicit
finite set independent of e.” Read as a statement about every odd prime
divisor of Y_R, this is false. Take h=1,j=2,p=5,e=1, so R=7, X=128 and
N_(1,2)=3. Directly from the defining scalar formula,

```
Y_7=(20+15*128+6*128^2+128^3)/2
   =1098698=2*549349.
```

The odd integer 549349 is greater than 1 and is not divisible by 3.
It therefore has an odd prime divisor outside the proposed set {3}.
The actual theorem still gives the correct base-prime result:
Y_7=3 modulo 5, so the designated p=5 does not divide Y_7.
Root identified the scope error during independent review; the author's
freeze message crossed that review message, so the original bytes are
retained and this separate correction is issued.

Equation (5), its complete proof including xi=-1, both special index-family
obstructions, the short-period q's coprimality to 33, and the fixed-quotient
scope remain unchanged. No general all-prime or all-index obstruction is
inferred. The original numbered Review remark 1 and all limitations remain
in force. There is still no full compiler zero or universal83 conclusion.

The frozen original trio remains byte-identical:

- MD: `726c18d0d0fbba1d04bde35003093f25028e8556c299cf7e868e32d1dbc1f29b`.
- PY: `7e8f450d3a98f8b27f2dbd14ba61d32426e3c3ac1d353af58a213b5dc20a5667`.
- JSON: `feb6155bca2a908b325e88cba27b52367e97a67e8ea80ce3d41633a5b4508ffa`.

Its scalar evidence continues to corroborate precisely the corrected
base-prime theorem. No frozen helper was rerun or copied for execution.
The companion correction receipt only authenticates those existing bytes,
binds this correction, and records the freshly handwritten R=7 scalar
calculation. No source array, predecessor program, compiler or builder ran.
