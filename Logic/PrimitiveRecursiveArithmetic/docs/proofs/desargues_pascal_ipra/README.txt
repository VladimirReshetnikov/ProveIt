DESARGUES AND PASCAL IN INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
Prepared for Vladimir Reshetnikov -- 15 November 2026

START HERE
  paper.pdf            Complete human-readable proof and formalization plan.
  paper.tex            Main LaTeX source.
  sections/*.tex       All included source sections.
  lean/FORMALIZATION.txt  More detailed implementation roadmap.
  evidence/            Executed checks and pinned repository-source audit.

WHAT IS PROVED IN THE PAPER
1. Desargues, including the converse, in the rational projective plane.
2. Pascal for every nonzero homogeneous rational quadratic, including
   singular conics, whenever the stated intersections are genuine points.
3. Primitive recursive algorithms producing an actual common line or center.
4. Universal polynomial identities over every commutative ring.
5. A conditional iPRA schema for fixed primitive-recursive real coordinate
   names with explicit regularity and apartness premises.

The exact internal theorems use integer homogeneous representatives and
signed-natural-pair arithmetic. They quantify over arbitrary numerical
coordinates, not merely over the examples or tested cube.
The real-name schema does not assert a first-order sort of all reals or
a total universal evaluator for arbitrary PR programs.

LEAN STATUS -- READ BEFORE USING
The two .lean files are concrete UNCOMPILED candidates. No Lean or Lake
executable was available in the authoring environment. They contain ambient
algebra proofs written with ring and explicit finite data. They have not
been kernel checked and do not yet construct the deeply embedded iPRA
derivations. The paper and FORMALIZATION.txt state the remaining obligations.
No new theorem is claimed as formally checked merely because its source
contains no proof hole. Lean/mathlib v4.32.0 is the inspected repository pin.

EXACT EXECUTED CHECKS (Python standard library only)
Run from this directory:
  python3 code/verify_pascal.py
  python3 code/verify_desargues.py
  python3 code/exact_geometry.py
  python3 lean/check_column_certificates.py

The first two use exact sparse integer polynomials in symbolic variables.
They check universal identities, not randomly sampled numerical inputs.
Pascal's polynomial has 720 monomials; Desargues' has 1,290.
The six Pascal cofactor identities are also checked symbolically.
The generic column-replacement checker supports the chosen Lean encoding.

The geometry script checks both Desargues examples, the Pascal parabola
example (including a point at infinity), a degenerate conic example, and
all 7,146 determinant-zero triples from the small integer cube with first
vector nonzero. All four common-kernel branches are covered.
These checks are supplementary evidence, not emitted iPRA or Lean proofs.

LEAN BUILD (in a configured environment)
  cd lean
  lake update
  lake exe cache get
  lake build

This requires network access to obtain the pinned dependency if absent.
Source elaboration or performance may require repair because compilation
was unavailable here. Use #print axioms on the final theorems after building.
See FORMALIZATION.txt for object-iPRA milestones; ambient ring proofs alone
do not establish Prf PRAAx derivability.

PDF BUILD
A standard LaTeX installation needs amsmath, amsthm, mathtools, lmodern,
microtype, geometry, booktabs, listings, fancyhdr, xurl, and hyperref.
Run:
  bash build.sh
or run pdflatex -interaction=nonstopmode -halt-on-error paper.tex twice.

PROVENANCE
ProveIt commit:
  0bba41d70f061442357cae0f6de055434a33fb09
Relevant actual interfaces:
  PR, PTm, PRAAx, PRA.qfInd
  LeanProofs.ConciseIPRA.pra_iff_native
Read-only repository inspection; no GitHub write or push was performed.
evidence/source_audit.json records inspected source URLs, Git blob hashes,
and SHA-256 content hashes. Draft directory filenames were inspected;
no draft archive was used as an additional mathematical assumption.

The complete deliverable is contained in this archive. Generated TeX
auxiliary files and machine-specific temporary tooling are omitted.

