# Multiplicative anchor shears and an affine screen

The maintained 65-operation circuit has two rank-independent unit anchors,
`N1` and `Nt`, whose values are 1 at every positive zero. The previously
reviewed anchored-shear proof therefore gives two exact coordinatewise
zero-equivalent substitutions:

```
R' = R*N1,     R' = R*Nt.
```

Each is `R + R*(anchor−1)`, so this uses the audited shear theorem with an
integer coefficient. The main norm `N1` is available before `R`; for `Nt`,
the five independent transport gates are moved earlier, after `R` and
before its first downstream use. Both variants have **66 live binary gates**
on the same 14 positive inputs: one more than the maintained equation.
Their validity and acyclicity were independently reviewed at
`../../reviews/current14-carrier65-multiplicative-shear-independent/`.
This is not a gate saving, a Lean theorem, or a PDF/file binding.

To look for compensating sharing, `check.py` applies the previously used
single-target affine modular filter to both 66-gate variants, at the actual
four pinned port values. For each target the filter checks direct aliases,
a constant leaf, one-gate affine forms, and two-gate `c*x±y` forms, with one
arbitrary fresh constant leaf. It evaluates four samples for each of three
prime moduli; every nonliteral scale has a nonzero pivot in each prime. In
each variant it checked 66 targets and 447,172 two-affine queries. Neither
variant had a strictly smaller live candidate in these forms. A 3→2 positive
control is included.

The residue checks only filter necessary conditions: the conclusion is
restricted to these two transformed graphs, listed one-target forms, fixed
ports and the observed nonzero pivots. It is not a bound for other shears,
other zero-preserving transformations, multi-target rewrites or arbitrary
circuits, and modular survivors would require exact verification.

Reproduce without Lean:

```
python3 -I -S -B research/current14-carrier65-anchor-product/check.py > /tmp/anchor-product-result.json
cmp /tmp/anchor-product-result.json research/current14-carrier65-anchor-product/result.json
```

The affine-screen receipt and scope were independently reviewed at
`../../reviews/current14-carrier65-anchor-product-independent/`.
