# A unit-anchored rank shear

This is a zero-preserving transformation of the maintained 14-positive-input
integer equation, not a smaller candidate: the direct circuit below has **67
live operations**, compared with 65. It does not establish any optimality or
add a Lean theorem. The actual TeX/PDF connection remains separate.

Let `Q=N1=D²−Δc²`, where `D=main_root` and `Δ=(a+2)²−1`. The current
scaled output can be written

```
F = N0 * Q * Na * Nt * Z − Δ,
Z = Δ * B,
B = f² − Δ*(i*c²)².
```

For every positive input, `Δ>0`; all displayed quantities are integers.
Regardless of the values of the other factors, `F=0` therefore makes `Q` an
integer divisor of 1. Moreover `Q≠−1`: if `a` is even then `Δ≡3 (mod 4)`,
while if `a` is odd then `Δ≡0 (mod 4)`, and the resulting difference of
squares cannot be 3 modulo 4. Hence **Q=1 at every zero**. This proof does not
require any claim about the sign of the first or transport factor.

`Q` depends on the inputs but not on `R`. Replace every occurrence of `R`
in the other factors by

```
R' = R + H*(Q−1),
```

where `H` is any integer-valued polynomial in the original inputs, and leave
`Q` unchanged. The transformed equation is well-defined by direct
substitution. Its zeros also force `Q=1` by the same unit argument, so on a
zero of either equation `R'=R` and every remaining factor agrees. This is
coordinatewise zero equivalence on exactly the same positive domain; it is
not a witness-elimination argument. The claim does not rely on proving `Nt=1`.

As a concrete test take `H=1`. Insert `rank_plus_main=R+Q` and
`sheared_rank=rank_plus_main−1` after the original `R` gate; replace the two
later uses of `R` by `sheared_rank`. All 67 gates are live, so this version
adds two operations. A useful exact identity exhibits the change. Put
`d=Q−1`, `S2=normalized_S²`, and `f2=f²`. Then

```
N0' = N0 − 2*tau*d + d²
Na' = Na + S2*(-2*V*f2*d + f2²*d²)
F'−F = Q*Nt*Z*d * [(-2*tau+d)*Na'
                       + N0*S2*(-2*V*f2+f2²*d)].
```

The checker pins the source graph, verifies both changed rank uses and live
gate counts, checks all 64 residue triples modulo 4, and verifies the last
identity by exact sparse-polynomial arithmetic over the integers. These
checks do not verify Lean, external files, or the PDF.

```
python3 -I -S -B research/current14-carrier65-main-norm-shear/check.py
```

Independent external review is recorded in
`../../reviews/current14-carrier65-main-norm-shear-independent/`.
