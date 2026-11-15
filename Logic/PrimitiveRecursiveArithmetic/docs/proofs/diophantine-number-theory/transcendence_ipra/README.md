# Transcendence of e and pi in intuitionistic PRA

This package gives a complete human-readable mathematical proof and an explicit Lean completion plan.

## Main result

For each nonzero integer polynomial P, the paper defines primitive recursive integers B(P)>0 and N(P)=4*B(P)*lambda(P)+1 such that

    s >= N(P)  ==>  2*B(P)*abs(P(c_s)) > 1,

where c_s is the specified rational name for e or pi. The final assertion is an integer inequality after clearing positive denominators. It supplies a rational apartness witness and refutes polynomial vanishing.

The proof for e uses a Hermite polynomial. The proof for pi uses a rational companion matrix and additive exterior powers, followed by an integer trace argument. Neither a splitting field nor algebraic root isolation is needed. The Hermite parameter need only be coprime to a specified integer; primality is unnecessary.

## Files

- transcendence_ipra.tex — complete paper, including all parameters and finite cutoff proofs.
- transcendence_ipra.pdf — compiled paper.
- lean/Blueprint.lean — **uncompiled implementation blueprint**, not a completed proof.
- lean/ROADMAP.md — module order, internal proof obligations, and quantifier-free induction inventory.
- code/e_checks.py — exact scalar Hermite identities and sample rational separation certificates.
- code/matrix_checks.py — exact exterior-power, Newton trace, companion, and Hermite congruence checks.
- code/finite_analysis_checks.py — exact finite Hermite defects, Machin identities, and representative Cauchy/tail checks.
- code/bounds.py — structural computations and a finite arithmetic expression graph specifying the paper's enormous bounds.
- verification/ — saved check results, a bound graph for P(X)=X-3, and provenance.
- requirements.txt and Makefile — reproduction commands.

## Status

The mathematical proof is supplied in full. The Lean development is an outline with concrete object-theory interfaces and a clear module-by-module route; it has not been compiled, and it does not instantiate the missing Programs or Derivations records. There is no axiom or sorry declaration pretending to supply either transcendence theorem.

The Python scripts passed their stated representative exact checks. They are not universal iPRA proof certificates and do not replace the mathematical proof.

The key formal target is an actual internal derivation:

    Prf PRAAx [] (AllAccepted concretePrograms.piTest)

and its counterpart for e. A theorem about Real.pi in ambient Mathlib would not, by itself, establish iPRA-provability.

## Reproduce the artifacts

With a normal TeX Live installation:

    make pdf

With Python 3 and SymPy 1.14.0 installed:

    make checks
    make bounds

The e script itself uses only the Python standard library. The two other check scripts and the pi bound construction use SymPy.

To display the bound graph for another polynomial:

    python3 code/bounds.py --coeffs='1,-3,2' --constant=both

Coefficients are listed from the constant term upwards. The bound graph records exact operations but does not materialize its immense final factorials. Structural pi computations grow with dimension 2^(2*degree); the provided example has degree one.

## Repository provenance

Inspected ProveIt commit:

    0bf379a84212abd05e9a3f0b1320a3d7da509cf9

The repository toolchain at that snapshot is leanprover/lean4:v4.32.0.
The source interfaces are from the ConciseIPRA import root, with namespace LeanProofs.ConciseIPRA. See verification/provenance.json for exact source paths and blob hashes.

No repository files were changed or committed. The draft directory was inventoried, but no unverified result from an archived draft is assumed.

