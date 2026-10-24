# Ten-positive one-sided centered residue norm

- Ten strictly positive integer unknowns.
- Exact total degree 912, down from 1152 (20.833% reduction).
- 126 live binary arithmetic operations, down from 131.
- Fixed compact44 coefficient tuple and inherited calibration unchanged.
- No new canonical congruence or unproved freedom assumption.

Read PROOF.md for the complete local proof and logical boundary. The genuinely useful refinement is one-sided control of the rational main-carrier residue; its negative values need not be bounded. This permits the same small weight k(T+F+alpha) to cover both the auxiliary root gap and the main residue after offsetting T and centering the two large roots.

Rebuild and audit:

    python build.py
    python independent_check.py
    python degree_specialization.py

The generator and exact 495-term norm checker adapt the inspected radical-residue predecessor. New formula edits, branch-degree proof, and leading-form simplification are supplied here. The proof is ordinary mathematics formalizable in ZFC, not a new end-to-end formalization. No global optimality claim is made.
