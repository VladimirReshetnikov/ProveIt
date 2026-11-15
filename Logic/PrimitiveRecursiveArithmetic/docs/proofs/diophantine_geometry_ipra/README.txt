DIOPHANTINE GEOMETRY IN INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
Prepared for Vladimir Reshetnikov, November 15, 2026

START HERE

Read diophantine_geometry_ipra.pdf. Its complete LaTeX source is
diophantine_geometry_ipra.tex together with sections/*.tex.

This is a self-contained development of a selected substantial part of
rational Diophantine geometry in first-order iPRA. It includes full written
proofs, exact reference implementations, a compiled Lean arithmetic core,
and a detailed roadmap for a complete deeply embedded iPRA formalization.

PRINCIPAL RESULTS

1. Canonical projective points and exact bounded-height enumeration over Q.
2. Rational-root bounds and complete finite root enumeration.
3. Explicit two-sided height inequalities for maps [F:G] of P1, using two
   Sylvester-adjugate polynomial identities and a bound on gcd cancellation.
4. A primitive recursive complete list of all rational preperiodic points
   of any input map of degree >=2 with nonzero homogeneous resultant.
5. A total parametrization of every nonsingular rational conic with a
   supplied point, including its tangent parameter and an explicit inverse.
6. Explicit quadratic conic height comparison and linear point-count bounds.
7. Fermat's square-area theorem by a specified finite descent; exponent-four
   and rational-square progression corollaries.
8. The signed triangle/congruent-number-curve correspondence, and the
   complete rational point list E1(Q)={O,(0,0),(1,0),(-1,0)}.
9. Finite congruence-obstruction certificates; square and cube denominators
   and complete bounded-x-height searches on integral Weierstrass equations.
10. A conditional finite-generation theorem with a supplied primitive
    recursive height-reducing selector and explicit coefficient extraction.

FORMAL VERIFICATION STATUS

Thirteen named theorems in lean/DiophantineCore.lean were compiled under
Lean 4.32.0, using only Std. They cover bounded scans, witness search,
finite descent, conic/circle polynomial identities, and the cleared-
denominator triangle/elliptic-curve identities.

Their #print axioms reports contain only propext and Quot.sound (one
theorem only propext). They contain no Classical.choice, sorryAx, added
axioms, or native_decide. Actual compiler output and a source hash are in
evidence/lean-build.txt and evidence/lean-build.json.

These are ambient Lean proofs. The full geometric theorems have NOT yet
been constructed as Prf PRAAx values in the deeply embedded iPRA theory.
Section 8 gives the exact module and dependency plan for that work. The
existing ProveIt bridge pra_iff_native transfers an iPRA derivation only
after that derivation has been constructed; it does not turn arbitrary
Lean theorems into iPRA theorems.

The general Mordell-Weil, Roth, Siegel and Faltings theorems are not claimed
as results of this package. No unprovability claim about them is made.

REPRODUCTION

PDF, with a normal LaTeX installation:
    latexmk -pdf -interaction=nonstopmode -halt-on-error diophantine_geometry_ipra.tex

Exact Python checks (standard library only):
    python3 code/check_all.py

Exact worked examples:
    python3 code/geometry.py

Lean (Lean 4.32.0):
    cd lean
    lake build

Or, to display every named theorem's axiom report:
    cd lean
    lean DiophantineCore.lean

The Makefile provides pdf, check, and lean targets. No compiled toolchain
or Mathlib checkout is required in the archive. Invalid input codes in
Python may raise ValueError; the iPRA versions totalize those branches with
an explicit failure flag and default output, as described in the report.

EVIDENCE

evidence/validation.json: exact executable-check results, including
729 quadratic coefficient pairs, 480 nonzero resultants, 11,520 height
comparisons, general-conic inverse/enumeration checks, and square-area
arithmetic/triangle correspondence checks.

evidence/examples.json: complete preperiodic lists for t^2 and t^2-1,
congruence obstruction counts, bounded elliptic examples, and rational roots.

evidence/pdf-build.json and pdf-build.txt: PDF compiler and visual-layout checks.
SHA256SUMS: integrity hashes for every file in this package except itself.

evidence/source_manifest.json: pinned upstream ProveIt revision and file
blob identifiers, the inspected draft index, and primary-source references.

evidence/reviews/: independent mathematical audits. Minor precision issues
identified there were addressed; see evidence/review_resolutions.txt.

Finite tests detect implementation errors. They do not prove an unbounded
theorem; all completeness and nonexistence claims rest on the written
arguments and the stated formalization boundary.

UPSTREAM FOUNDATION

Repository: https://github.com/VladimirReshetnikov/ProveIt
Inspected revision: b5a3ad037723c44d69a3d5b28a950c554327a989
Relevant namespace: LeanProofs.ConciseIPRA
Relevant definitions: PR, PTm, PRAAx, PRA.qfInd
Relevant translation theorem: pra_iff_native

No repository changes were made. No unread archived draft is used as a
proof dependency. The new arithmetic development is self-contained.
