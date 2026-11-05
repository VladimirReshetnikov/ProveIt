# A fixed-coordinate obstruction to normalizing a 72 zero

For any **standard positive integer zero** of the 72 graph, consider an old
76Y witness at the same ports and with the same `J` and `k=eta+zeta`, whose
old carrier expression maps to the same `h`. Other coordinates, including
`F,alpha,z,T,s` and the Pell witnesses, may change. Such an old witness must
have a uniquely determined transport gap `C'=q−F'−alpha'`:

```
q = beta*J+1
C' = (h+k−1−MC*J) mod q,       1 ≤ C' ≤ q−2.
```

If that least nonnegative residue is 0 or `q−1`, **no such fixed-coordinate
old witness exists**. This is only an obstruction to a class of witness
normalizations; it does not exclude old witnesses with a different `J`, `k`,
or mapped `h`, and does not prove nonexistence or an existence equivalence.
The argument is external arithmetic, not a Lean theorem.

## Proof and an additional 72-zero constraint

The old transport equation is
`(K0+w') C' = F'+z'(q−1)`. Positivity of `F'` and nonnegativity of
`z'(q−1)` imply `C'>0`; positivity of `F',alpha'` then gives `C'≤q−2`.
The old rank satisfies

```
R' = ((q−1)(q−F')+alpha')(q²−1)+(MC+q MF)J
R' ≡ C'+MC*J (mod q).
```

The old carrier equality `h=U' gamma'−k+R'+1`, together with
`q | U'=q⁶(s')²`, forces `C'≡h+k−1−MC*J (mod q)`. The interval above
contains at most one representative of that residue.

In fact every 72 zero also has `q | h`. Its main residual says
`Dstar²=U²(D c²+1)`, so integer square divisibility yields `U | Dstar` and
therefore `U | H h`. The graph has `U=q⁶s²`, `H=4a+3`, and `q³ | a`.
Every prime common to `q` and `H` is 3. If `3 | q`, then `H≡3 (mod 27)`,
so `gcd(q⁶,H)=3`; otherwise this gcd is 1. It follows that
`(q⁶/gcd(q⁶,H)) | h`, hence `q | h`. Thus the necessary transport gap
simplifies to `(k−1−MC*J) mod q`. This divisibility reasoning is for standard
integers; this packet does not claim it has been formalized in `IΣ₁` or iPRA.

## Application and compact44 limitation

The independent [full symbolic 72 zero](../p64-qcube72-full-zero-mod-q-obstruction/README.md)
has `q=3`, `J=1`, `h≡0`, `k≡2`, and `MC≡1 (mod 3)`. Its required residue
is 0, outside `1≤C'≤q−2`. Thus no old zero at its particular ports can
reproduce those three fixed values `J,k,h`, even if every other coordinate is
changed. This strengthens the simple fixed-valuation inverse obstruction but
still does not rule out a different old zero.

For the compact44 ports, the repo defines
`beta=2^(67*8807)−1` and `MC=lowNat`. The same necessary condition is

```
C' = (k−1−lowNat*J) mod (beta*J+1),   1 ≤ C' ≤ beta*J−1.
```

Equivalently, the necessary condition excludes the two classes
`k ≡ lowNat*J` and `k ≡ lowNat*J+1 (mod q)`. No claim here shows this
condition holds or fails for arbitrary compact44 72 zeros. Determining
whether the other residuals exclude those classes, or finding a normalization
that changes `J` or `k`, remains open.

A narrower family keeping both `C` and `w` fixed is rigid: transport forces
`F'≡F (mod q−1)`, while positivity gives `1≤F,F'≤q−2`, so `F'=F` and then
`alpha'=alpha`, `z'=z`. Thus merely shifting `F,alpha,z` at fixed `C` and `w` cannot
repair the carrier congruence.

[`check.py`](check.py) pins the full-zero packet, graph and compact-port source,
checks 7,560 finite rank/rigidity cases and 2,303 finite `U | Hh` controls, and
rechecks the example residue. It also tests a transport-only counterexample showing why `w` must stay fixed
in the narrower rigidity claim. These are controls, not a replacement for the
universal proof above. Run `python3 -I -S -B check.py`.
