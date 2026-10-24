# Complete 512-variable checkpoint

This directory is the independently complete intermediate specialization of
the frozen incoming 517-variable direct quartic. The principal 508-variable
result is in `principal/`.

`equation512.json` gives 310 quadratic residuals in 512 unrestricted integer
variables. Their squared sum has degree four, 6,742 monomials, and coefficient
height 3,904,268. Every collected coefficient is in `polynomial512.json`.

The changes are the cofinal horizon `t = 16 + s^2`, the strengthened guard
`F >= 1`, and the deterministic modulus `y = V^2 + 3F - 1`. Here the retained
parent power is `V = (F*t^2 + 1)^t`. The principal refinement uses a different
radius and is proved separately. Do not mix their definitions.

`PROOF.md` and `../proofs/COFINAL_PROOF.md` give the ordinary existence
equivalence. `specialization_certificate.json` identifies the exact three
changed residuals and five deleted coordinates. `source517.json` is the
literal parent. `verify.py` checks the entire finite specialization and full
coefficient expansion without importing the builder.

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B build.py --output /tmp/conzfc512-rebuilt
```

The frozen `MANIFEST.json` authenticates the original checkpoint component;
the packet-level `../MANIFEST.sha256` also covers this integration README
and the additional `principal/` component.
