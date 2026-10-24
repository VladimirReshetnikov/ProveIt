# Coprime scale carriers and fixed prime separation

Five complete unrestricted-integer polynomial equations improve the inspected radical frontier. The standalone paper is `standalone.pdf`; `section.tex` is its inclusion-ready source and `PROOF.md` gives the detailed ordinary proof.

- 13 variables, exact degree1072, 192 live binary operations.
- 14 variables, exact degree378, 145 operations.
- 15 variables, exact degree172, 123 operations.
- 15 variables, exact degree170, 134 operations.
- 16 variables, exact degree98, 138 operations.

Every polynomial is supplied as a literal division-free JSON DAG. The six fixed coefficients are the actual authenticated source34/source71 integers under `coefficients/`. MF is already shifted. There are no free coefficient parameters or hidden existential registers.

The mechanism combines a degree-two scale Y=qv with one carrier for the coprime scale/main congruences, fixed three-adic radical separation before guard recovery, and signed unit-product finalizers. The centered two/three-root companions additionally expose cancellations through integral root shifts. Existing prime-separation and coprime-carrier ingredients are expressly inherited; the complete endpoint compositions here are new relative to the inspected source snapshot.

## Reproduce offline

Python3.10+ standard library only:

    python build.py
    python check.py
    python -O check.py
    python check_center_identity.py
    python -O check_center_identity.py

The newly authored scripts execute no imported upstream code. `build.py` deterministically writes the five circuits and metrics. `check.py` independently validates topology, liveness, actual coefficient hashes, complete circuit-to-conjugate-product transcriptions on signed modular inputs, and exact attained-degree certificates using two primes. Universal degree upper bounds are proved separately in the paper. `check_center_identity.py` checks every coefficient of the centered identity over the integers, including singular parameter values.

Compile `standalone.tex` with ordinary pdfLaTeX twice from this directory. The source needs standard article, lmodern, amsmath, amssymb, booktabs, geometry, microtype and hyperref packages. The supplied PDF was visually reviewed after rendering; QA intermediates are not part of the research deliverable.

## Mathematical boundary

The new transformations restore all five rows of the literal inherited seventeen-integer CRT parent. The inherited ordinary native/compiler/K215 calibration and normalized canonical-completeness argument remain explicit mathematical dependencies. This package supplies no new Lean/Rocq end-to-end certificate or encoded object-language ZFC proof. It proves neither Con(ZFC) itself nor global minimality. Absence of zeros is equivalent to consistency only at the same ordinary theorem level as the named inherited calibration.

A proposed twelve-coordinate shortcut was rejected: the ternary positive representation cannot simply lose one witness, even with its nearest-square variable free. The explicit obstruction is recorded in PROOF.md.
