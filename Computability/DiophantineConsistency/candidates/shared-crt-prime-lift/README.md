# Smaller direct quartics from a prime-power CRT lift

This ordinary arithmetic refinement of the received shared-direct construction removes five natural variables from its affine build. All variables are nonnegative integers; each equation is the sum of the squares of its listed quadratic residuals.

| Build | Variables | Residuals | Exact degree | Expanded terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| [Affine](affine/equation.json) | **3,609** | 2,949 | 4 | 15,752 | 127,285,349 |
| [Retained affine wires](retained/equation.json) | **6,180** | 5,520 | 4 | 17,421 | 1,992 |

The complete expanded coefficient dictionaries accompany both residual systems. Fixed coefficients are ordinary literal integers. There is no remaining arithmetic macro, quantified bound, native tuple, or external compiler choice in either polynomial.

[PROOF.md](PROOF.md) gives the universal range-certificate argument and both existence directions. Its prime-power CRT lift permits factorial-free binomial range conditions without adding the coordinate bound to the global factorial argument. It also permits a private-coordinate bound U independent of the label bound m. A plain shift by the unlifted CRT product would be invalid; the proof explicitly chooses positive columns modulo the stronger periods.

The pinned incoming builder is changed at exactly two source lines, with all arithmetic graphs and numerical C222 rules preserved. [SOURCE_PINS.json](SOURCE_PINS.json) authenticates the incoming archive and every copied/patched source. [check.py](check.py) independently checks exact polynomial expansion, pins, lift controls, and the retained arithmetic/affine auditors. The generator and commands are in the proof.

The no-zero/Con(ZFC) equivalence inherits the received ordinary C222/refutation and Pell characterization theorems. This is a new local ordinary proof and literal materialization. It supplies no new Lean or object-language ZFC proof; Lean formalization remains paused. The incoming archive and all earlier candidates are unchanged.
