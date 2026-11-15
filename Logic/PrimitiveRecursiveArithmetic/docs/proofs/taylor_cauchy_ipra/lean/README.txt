LEAN SCRIPTS AND FORMALIZATION ROUTE
==================================

Status: UNCOMPILED in the producing environment.
No completed Taylor/Cauchy formalization or embedded iPRA derivation is claimed.

FiniteCore.lean
--------------
Actual proof scripts for finite algebra:
  prefix_telescope
  summation_by_parts
  finite_geometric
  taylor_product_split
  affine_triangle_numerator
  cancel_common_edge
  quotient_remainder

It imports Mathlib and uses ordinary algebra structures. These results are
Lean metatheorems, not proofs of the corresponding object iPRA formulas.
The object arithmetic reconstruction is a separate layer.

NativeBridge.lean
----------------
Imports ConciseIPRA.NativeBiInterpretation and applies the source-audited
pra_iff_native theorem to an ALREADY CONSTRUCTED Prf PRAAx derivation.
It does not assume or construct the missing Taylor/Cauchy derivations.

Pinned baseline:
  ProveIt commit 876ef598f674759da5f084dc34f63ca4e182aae0
  Lean 4.32.0 / Mathlib v4.32.0

BUILD COMMANDS
--------------

In a matching Mathlib-enabled project, replacing the paths with the
absolute extracted paths:

  lake env lean /absolute/path/taylor_cauchy_ipra/lean/FiniteCore.lean

In a checkout of the pinned ProveIt repository, first make its imported
native bridge available:

  lake build +ConciseIPRA.NativeBiInterpretation
  lake env lean /absolute/path/taylor_cauchy_ipra/lean/NativeBridge.lean

These commands are instructions, not commands that were successfully run
while producing this archive. The source APIs were inspected; the full
repository and dependency closure were not rebuilt.

COMPLETION GATES
----------------

1. Compile these two source files and retain the named #print axioms output.
2. Implement the rational codes, PR schedules and arithmetic contract formulas.
3. Construct object-level proofs of the paper's finite Taylor and grid
   inequalities using only syntactically quantifier-free induction.
4. Formalize the integral names and all approximation/error transport.
5. Construct the full first-order iPRA derivations for the final precision
   statements, then universally close precision.
6. Apply native_of_ipra and audit the resulting native derivations.

FORMALIZATION_PLAN.txt gives the detailed source API and layer-by-layer route.
The mathematical statements and constants are authoritative in report.tex.
