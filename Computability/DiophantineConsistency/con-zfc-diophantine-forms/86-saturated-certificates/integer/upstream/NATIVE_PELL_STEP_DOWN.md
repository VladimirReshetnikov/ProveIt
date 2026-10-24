# Signed native Pell step-down

`NativePellStepDown.lean` isolates the auxiliary index recovery for the
literal minus-sign coordinate

```
V = j*c - J = o*f - c.
```

It does not replace this coordinate by the plus-sign interface of
`Jones1980.half_index`. The auxiliary coordinate `V`, and the multipliers
`j,o`, may be arbitrary integers.

## Precise bridge

Assume the recovered main Pell data

```
A > 1, p > 0, c = psi_A(p), f = chi_A(m),
2*p <= m, c | m,
I > 1, c | I, I^2 = (A^2-1)*(f^2-1),
y > 0, I^2*V^2 - (I^2-1)*y^2 = 1.
```

The theorem `signed_index_residues` takes the two minus-sign congruences
`V = -c (mod f)` and `V = -J (mod c)` and concludes

```
c | J-p  or  c | J+p.
```

The proof classifies the Pell pair `(I*abs(V), y)`. Its index is odd because
the even-index chi recurrence is `+1` or `-1` modulo `I`. The existing
`Jones1980.Qh` identities recover the auxiliary index modulo `f` and `c`.
Squaring the former removes the sign of `V`; the signed chi step-down in
`Jones1980.step_down` gives the main index up to sign modulo `m`, hence
modulo `c`. No factorization of the composite modulus `c` is assumed.

`eq_of_residues` removes both alternatives' ambiguity under
`p,J > 0`, `2*p < c`, and `2*J < c`. The direct source-form theorem
`source_index` therefore concludes `p=J`. It assumes neither oddness of
`J` nor positivity of `V`; this avoids using the odd-rank conclusion
before native compiler recovery establishes it.

`source_index_of_strong` combines this result with the checked
`Jones1980.relaxed_aux`. Its explicit bootstrap is
`c = psi_A(p)` and `c > A*(A^2-1)^2`; it also assumes the two half-modulus
bounds. From the supplied strong norm
`(i*c^2)^2 = (A^2-1)*(f^2-1)` it obtains `f=chi_A(m)`, `c|m` and the
strong rank identity, and derives `2*p <= m` before applying the signed
step-down. Thus callers need not supply the recovered auxiliary index.

## Strong quotient restoration

`quotient_dvd` proves, for arbitrary integer inputs,

```
c | f^2-1  and  c | o*f+J  =>  c | o+J*f.
```

`quotient_identity` then proves that any supplied quotient satisfying
`c*T=o+J*f` reconstructs exactly

```
c*(T*f-1) - J*f^2 = o*f-c.
```

The divisibility `c | f^2-1` remains an explicit premise. It must come from
strong Pell rank recovery; cancelling the discriminant from the strong
norm would not establish it.

## Remaining native obligations

This module supplies one unbounded arithmetic bridge, not an authentic
native source-to-machine theorem. It does not derive `c=psi_A(p)` or its
large-index bootstrap from the seven source residuals. The caller must
still obtain the displayed recovered main data and half-modulus bounds,
then finish the main-root, mask-population and ordinary compiler steps
listed in `NATIVE_CALIBRATION52.md`. It does not establish an internal
object-language ZFC derivation.
