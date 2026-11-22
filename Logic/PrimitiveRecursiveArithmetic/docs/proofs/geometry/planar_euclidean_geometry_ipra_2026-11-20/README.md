# Planar Euclidean geometry in iPRA

Open **geometry.pdf** for the proofs. The main result is Theorem 3.1. Every first-order point formula has a primitive recursive test on real algebraic coordinates, and iPRA proves the equivalence for that fixed formula. This realizes the complete elementary theory of the ordinary real plane. The report also gives a two-way framed coordinatization and distinguishes straightedge-and-compass witnesses from general algebraic witnesses.

## The report

- Sections 2 and 3 construct exact number codes, prove polynomial root enumeration and eliminate point quantifiers. All bisections, grid searches and coefficient branches have primitive recursive bounds.
- Sections 4 and 5 verify Tarski's axioms with elementary continuity and recover coordinates from points alone.
- Sections 6 and 7 classify line and circle intersections, prove the nine-point circle theorem and classify motions and congruence of finite configurations.
- Sections 8 and 9 describe the completion to general real names and the remaining steps for formalization in the embedded arithmetic.

The source is **geometry.tex**, with component files under **parts/**. To rebuild it with a standard TeX Live installation, run:

```sh
latexmk -pdf -halt-on-error geometry.tex
```

## Checked Lean material

The seven source files under **lean/** compile with Lean 4.32.0 and mathlib v4.32.0. **verification/lean.log** records the run. The arithmetic dependencies were read from ProveIt revision **83421593771f877bc1ae98f4229eb35507bff05b**. The following command can be run from this packet with a checkout of that revision:

```sh
./check-lean.sh /path/to/ProveIt
```

**MetricIdentities.lean** proves two closed formulas of type `Prf PRAAx [] φ` with ProveIt's `ipra_ring` infrastructure. Each formula states an integer identity under eight natural-number binders. **Axioms.lean** checks Euclid, inner Pasch and five segments over an ordered field, together with the polynomial characterization of betweenness. **Translation.lean** and **Bridge.lean** verify the first-order point/scalar translation, including existential betweenness semantics. **FrameRelations.lean** and **CanonicalFrame.lean** verify the geometric definitions of arithmetic and the canonical-frame bijection. **ObjectLanguage.lean** compiles formulas into the actual iPRA formula type given seven primitive-recursive scalar symbols. Section 9 sets out the remaining work to supply those symbols and the general object-theory proof generator.

The Lean metatheoretic axioms listed in the log are those reported for the two closed embedded derivations. No supplied Lean file contains a proof placeholder. The algorithms and mathematical arguments of the general elimination and scalar chapters have not been fully mechanized in iPRA.

## Exact executable examples

From the packet root, using Python 3.10 or later:

```sh
python3 code/scalar_records.py
python3 code/exact_scalars.py
python3 code/sign_cells.py
python3 -m unittest discover -s code -p 'test_plane.py' -v
python3 -m unittest discover -s code -p 'test_sign_cells.py' -v
```

These commands use the standard library. The geometric tests include irrational secants, tangency, zero radii, coincident circles, and right and obtuse triangles. **scalar_records.py** implements the rational certificate check, bisection, normalization, gap test and root grid. **exact_scalars.py** implements field operations, exact comparison and nonnegative square roots. For addition and multiplication it computes a rational annihilator using an interpolated univariate resultant. **plane.py** uses those operations directly. **sign_cells.py** computes every realized sign vector of a list of rational univariate polynomials using signed remainders. **algebraic_roots.py** also computes all real roots of a polynomial with algebraic coefficients, using SymPy (tested with 1.14.0) for exact resultants, rational factorization and root isolation:

```sh
python3 code/algebraic_roots.py
python3 code/witness.py
python3 -m unittest discover -s code -v
```

**quantifier_elimination.py** implements coefficient branching for small prenex formulas over rational polynomials, including degree drops and alternating quantifiers. Pass a SymPy Boolean matrix and an outermost-first sequence of quantifiers to `qe`. **witness.py** combines that elimination with algebraic root isolation and cell sampling. Its examples recover the equilateral vertex, the positive fourth root of two from an algebraic parameter, and a negative counterexample to surjectivity of squaring.

Floating-point approximations do not decide comparisons. Python exceptions on invalid application inputs expose the mathematical domain guards. In the iPRA interpretation each underlying numerical function is totalized as specified in the paper.

## Sources

[ProveIt arithmetic framework](https://github.com/VladimirReshetnikov/ProveIt/tree/83421593771f877bc1ae98f4229eb35507bff05b/Logic/PrimitiveRecursiveArithmetic) · [GeoCoq's statement of the point axioms](https://geocoq.github.io/GeoCoq/html/GeoCoq.Axioms.tarski_axioms.html) · [Cohen and Mahboubi on ordered-field quantifier elimination](https://arxiv.org/abs/1201.3731). Further sources are cited at the relevant proofs.
