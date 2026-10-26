# Keep only weighted labels in Psi

This is an exact identity refactor of the frozen admissible942 tuple.
Let `Psi_weighted` be its two label terms, omitting `(2-t)*x^1005`.
Then

```
Psi_old(x,1) = Psi_weighted(x,1) + x^1005,
Psi_old(x,2) = Psi_weighted(x,2).
```

Use the new Psi in Phi and replace the MC recipe by

```
MC = beta - rho^977 - rho^1005 - G_942(rho) - Psi_weighted(rho,1).
```

The complete coefficient polynomial Phi, every physical position and all
four fixed integers are exactly unchanged. The audit rebuilds all3297
coefficients, all978 physical positions and each whole integer. It also
checks a negative control: omitting the explicit MC marker term changes
the whole mask population and forbids the physical marker, so it is not
an acceptable shortening.

The exact MC and Psi TeX blocks stored in the receipt are6 bytes shorter
in total, including their line breaks. This is a local literal comparison,
not a measured full-page file. The raw four-port size remains94,689 bytes,
and the same specialized66-gate polynomial is retained pointwise. No new
native witness map is needed because the fixed tuple is identical.

```
python research/weighted-only-psi/audit.py --write
python research/weighted-only-psi/audit.py
python -O research/weighted-only-psi/audit.py
```

This isolated note does not modify the frozen source page or proof.
