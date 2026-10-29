# Recovered adaptive radix

From a zero of the actual current adaptive natural expression, every selected
`IΣ₁` model now has positive internal `N` and a residual factor `w` such that

```
q = Exp.exp(width·N),    width·N ≤ R,
w = Exp.exp(R−width·N),  X = q·w,
```

where `width = 47·2011`. Both exponential graph relations are provided as
well. The prior results supply `X=Exp.exp R` and `q | 3X`. To remove the
factor 3, a separate all-model theorem proves that, for every internal
`d≥4` and `u`, `3·Exp.exp u` cannot be one modulo `Exp.exp d−1`. It
reduces the exponent modulo d, bounds the remainder, and uses an explicit
Bezout certificate; it does not assume standard factorization or a standard
exponent. The existing internal alignment theorem then recovers N and w.

This is the recovered radix, not the full carrier or HA equivalence. The
transport and arithmetic window still need to be bound to the actual zero,
and the internal machine/syntactic proof chain must be completed.
