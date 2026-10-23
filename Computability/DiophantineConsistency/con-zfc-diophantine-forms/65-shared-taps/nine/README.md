# Shared kernel taps for the nine-variable consistency equation

Primary: **9 positive integer unknowns, exact degree 1,675,396, 458 binary
operations**. Companion: **9 positive unknowns, degree 1,738,228, 457 operations**.
The comparison is package59's degree1,910,404/473 at pinned commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`.

The new idea permits multiple source monomials to share a reversed-kernel
coefficient when their complete fixed coefficient polynomials agree. The
coefficient is stored once. This lowers source height2161 to1873; the exact
finite certificate checks every required and forbidden target monomial.

Read `PROOF.md` for the mathematical proof and exact register definitions.
`section.tex` is the article section. The literal primary equation is
`generated/shared_taps_positive.json`; its twelve nonliteral fixed leaves
are materialized under `fixed/shared_taps/`. The companion and natural
translations have their own files and coefficient bindings.

All data are local; Python3's standard library is sufficient:

    python3 construct.py
    python3 materialize_fixed.py
    python3 verify.py
    python3 -O verify.py

The native coefficient builder and full coherent original31 tuple are under
`coefficients/`; original-source and finalizer proofs are retained with
attribution. The new mathematical equivalence uses those inherited compiler,
calibration and Jones ratio theorems. No new end-to-end Lean certificate,
object-language ZFC derivation, global minimum, or literature priority is
claimed. A positive-domain result is not an unrestricted-integer result.
