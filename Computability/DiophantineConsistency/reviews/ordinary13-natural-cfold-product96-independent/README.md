# Independent review: natural C-fold four-unit product

The [96-operation candidate](../../research/ordinary13-natural-cfold-product96/README.md) and its [97-operation parent](../../research/ordinary13-natural-cfold97-degree28/README.md) have the same zero set pointwise for **every integer input and integer port tuple**. The 13-natural-input candidate has exact specialized degree 50 at the authenticated compact ports. The independent checker verifies the finalizer edit, graph shapes and liveness, all relevant residue cases, and a degree-50 ray by finite differences. This local pointwise result does not use calibration or port positivity. The inherited equivalence to the positive C-fold parent, however, remains conditional on the reviewed sign-free calibration, first-Pell/main-norm replay and their stated fixed-port hypotheses.

The unchanged parent residuals are `A0`, `A1`, `Fa−1` and `g72`; its output is their sum of squares. The new output is `(1+A0)*(1+A1)*Fa*(1+g72)−1`. For any integers, `b` and `q=b+1` have opposite parity, so `M=q^3*b` is even. Thus `1+A0` is `1+Z²` modulo four and cannot be `−1`. With `Delta=a²+4a+3` in `{0,3}` modulo four, `U²*(1+Delta*c²)` is 0 or 1 and `1+A1` cannot be `−1`. Also `f²−1` is 0 or 3 modulo four, so `Q=Delta*(f²−1)` is 0 or 1. The exact identity `u*(u+2V)=(V+u)²−V²` makes `Fa` congruent to one of those squares, while `1+g72=1+I²−Q` is 0, 1 or 2 modulo four. All four exclusions hold without any sign or fixed-port assumptions.

If the product is one, each integer factor is a unit and the exclusions force each to be +1. This gives `A0=A1=g72=0` and `Fa=1`, exactly the equations obtained when the parent sum of squares vanishes. The converse follows directly. The checker independently exhausts the residues used above and confirms the expression rows, but the unbounded unit and sum-of-squares reasoning is the mathematical argument.

The graph edit replaces the eight old finalizer nodes with seven new nodes and preserves all other rows; all 96 gates, 13 inputs and four ports are live. At the authenticated P72/P115 ports, the 50th finite difference of the all-inputs-equal ray has nonzero leading coefficient 604845992 modulo 1,000,000,007. The separate factor rays have nonzero leading terms at degrees 14, 13, 13 and 10. Their matching upper bounds are inherited from the parent C-fold cancellation proofs, so the exact specialized degree is 50. No Lean elaboration, iPRA derivation, physical-file/PDF theorem, provider replay or minimality claim is made.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary13-natural-cfold-product96-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary13-natural-cfold-product96-independent/result.json
```
