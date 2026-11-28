Standalone Lean support: canonical negative frames
=================================================

Verified file: BorderedGram.lean
Verification result: exit status 0; no warnings; no sorryAx.
The complete compiler output is lean_check.log.

Versions
--------
Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
Mathlib commit 56a005855ea17e0b0958f73ec801ae140b0a1679.
These match the toolchain and Mathlib revision pinned by the analyzed
ProveIt GRH package at f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f.

Reproduction
------------
From a Mathlib checkout at the revision above, with Lean 4.35.0 and the
matching dependencies and compiled cache available, run:

    lake env lean /absolute/path/to/formal/BorderedGram.lean

The verification used precisely this command, with these local paths:

    working directory:
      /workspace/scratch/37fbfd908a4b/research/mathlib
    command:
      PATH=/workspace/scratch/37fbfd908a4b/research/runtime/lean-4.35.0-linux/bin:$PATH lake env lean /workspace/scratch/6c0d6de06470/output/grh_canonical_frame/formal/BorderedGram.lean

The final packaged file was checked directly at the path above.
The optional lakefile.toml and lean-toolchain allow a new standalone
project to fetch the same Mathlib revision. They were not needed for the
recorded run against the already available pinned checkout.

Assertions actually checked
---------------------------
All six theorems are in namespace CanonicalFrame.

1. bordered_completion
   The completed-square identity for rectangular matrices over any field,
   under the explicit scalar relation w*v = (d-h)*I and h,d nonzero.
   Positivity and conjugation are not needed for this algebraic identity.

2. det_scalar_corner
   The Schur determinant formula at a nonzero scalar corner.

3. bordered_determinant
   The determinant factorization that combines the first two assertions.

4. hermitian_bordered_determinant
   The same identity directly for H + [X,v]^* [X,v]. The exact formal
   hypotheses are star(h)=h, h,d nonzero, and v^*v=(d-h)*I.

5. rank_one_determinant
   det(I - v*w/d) = h/d, given w*v=(d-h)*I and d nonzero.

6. jacobian_cancellation
   The exact cancellation of scalar powers after substituting
   det(P)=h/d and det(S)=det(H)/h into the complex Jacobian formula.
   This checks the powers and arithmetic, not a measure-change theorem.

Each final #print axioms reports only propext, Classical.choice,
and Quot.sound. No theorem uses sorry, an admitted axiom, or a GRH premise.

Scope
-----
This supplement verifies the core matrix algebra used by the proposal.
It does not formalize the positivity lemmas, complex Jacobian theorem,
bordered Hua integral inequality, or the bridge from the GRH source's
canonical negative frames to the public majorant theorem. The paper
supplies mathematical proofs of those statements. Integrating them and
rebuilding the GRH package remain further formal work. Compiling this
standalone support file is not a verification of the complete GRH proof
or an implemented net line-count reduction.
