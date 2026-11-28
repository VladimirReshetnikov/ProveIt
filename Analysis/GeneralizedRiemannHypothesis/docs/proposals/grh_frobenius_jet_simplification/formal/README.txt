FINITE FROBENIUS ORTHOGONALITY: CHECKED ALGEBRAIC CORE
===================================================

Files
-----
FrobeniusJets.lean  Self-contained Lean proof of the finite algebraic core.
lakefile.toml      Portable package with the exact mathlib revision pinned.
lean-toolchain    Exact Lean release used by the inspected ProveIt source.
validation.txt    Actual validation command, exit status, version, and axioms.

The parent proposal analyzes ProveIt commit
9050b04000647d588d0c78d945180abcd3b0bcf7. This package does not import ProveIt.
Its exact versions match that source:

  Lean:    leanprover/lean4:v4.35.0
  mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679

Reproduce from a clean directory
-------------------------------
Install elan (the Lean toolchain manager), place these files in one directory,
and run the following commands from that directory. The first two commands
require network access and fetch pinned dependencies and the mathlib cache.

  lake update
  lake exe cache get
  lake build
  lake env lean FrobeniusJets.lean

The final command prints the axiom dependencies of six principal theorems.
Every displayed list should be exactly:

  [propext, Classical.choice, Quot.sound]

These are standard Lean foundations. There is no sorryAx, custom axiom, or
external computation admitted as a theorem. The checked source contains no
sorry, admit, or axiom declaration.

The validation performed for this deliverable reused the already available
read-only mathlib build cache. The exact command and resulting successful exit
status are recorded in validation.txt. A fresh network dependency installation
was not performed for this package; lakefile.toml is the portable specification
of those same versions, not a claim that a second clean build was run.

What the checked core proves
----------------------------
1. The finite geometric resolvent sum(j<N) f^j(z) has Artin--Schreier difference
   z - f^N(z). It solves y - f(y) = z whenever that tail is zero. Solutions whose
   N-th iterate is zero are unique.

2. For a commutative ring R, a ring endomorphism f, a finite vector z_i, and
   weights w_i fixed by f, put M_e = sum_i w_i z_i f^e(z_i). Then

     sum_i w_i f^a(z_i) f^b(z_i) = f^min(a,b)(M_|a-b|).

   The file also checks the finite double-sum identity for arbitrary finite
   index sets and exponent families, including repeated exponents.

3. Inert case: if y_i - f^2(y_i) = z_i and (f^2)^N(y_i) = 0, vanishing of
   M_e for odd e < 2*N implies sum_i w_i y_i f(y_i) = 0.

4. Ramified case: if y_i - f(y_i) = z_i and f^N(y_i) = 0, vanishing of M_e
   for e < N together with M_0 = 0 implies

     sum_i w_i (y_i^2 - c*z_i^2) = 0

   for every c in R. The proposed application uses c = 1/2. The separate
   M_0 hypothesis also makes the statement correct when N = 0.

5. Natural-number weights are fixed by every ring endomorphism. Specializing
   f to the characteristic-p Frobenius gives the displayed pairing identity
   with ordinary p-power expressions, over an arbitrary characteristic-p
   commutative ring. No field, reducedness, or injectivity assumption is used.

How the finite-jet application matches the core
----------------------------------------------
Take R to be the quotient of the degree-B jet algebra by the required moment
ideal. Take f to be Frobenius and weights to be natural multiplicities. In the
inert case choose N with p^(2*N) > B; in the ramified case choose N with p^N > B.
The augmentation ideal then supplies the iterate-nilpotence hypotheses.
Moments whose degree p^e+1 exceeds B vanish automatically, so the finite
moment hypotheses above require no extra coupling condition.

Integration limitations
-----------------------
This package is a proved algebraic component of a proposed refactor. It is
not an integrated ProveIt patch and is not a verification of RH or GRH.
It does not formalize in this package:

  * the quotient/finite-jet construction and its degree-nilpotence bridge;
  * the formal-group inputs producing the raw theta exponent;
  * the transfer of modulo-pi vanishing to integral exponential coefficients;
  * the gradient coefficient certificate used in coupling sharpness;
  * the migration of the actual Divisibility and Sharpness consumers;
  * a whole-project build, dependency reduction, or net source-line saving.

Those steps are specified and analyzed in the accompanying report. Formal
verification here is limited to the statements explicitly present in
FrobeniusJets.lean. The use of an abstract endomorphism is deliberate: the
proof does not silently treat Frobenius as linear over a non-prime field.
