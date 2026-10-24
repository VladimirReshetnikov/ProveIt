# Twelve integers at degree 2048

The complete equation has twelve unrestricted integer unknowns, exact total
degree 2048, and 233 live binary operations: 148 multiplications, 53 additions
and 32 subtractions. Every fixed coefficient is one of the six actual
source34/source71 numeral payloads included under coefficients/.

Read standalone.pdf or its inclusion-ready section.tex. PROOF.md contains
the same mathematical argument in text form. The polynomial is the complete
division-free graph integer12_degree2048.json; intermediate registers are
not hidden existential variables.

The construction combines the late supplied full-residue Pell interpolation
lemma with a coprime homogeneous quintic carrier, a guard Pell witness
divisible by three, fixed prime separation, and doubled auxiliary centering.
It improves the supplied twelve-variable degree4832 / 248-operation point.
The degree16000 / 223-operation source remains a cheaper, higher-degree
tradeoff. This is not a global minimum or a variable-count record.

## Portable reproduction

Python 3.10 or later, standard library only:

    python build.py
    python check.py
    python -O check.py

The builder imports only the locally authored circuit.py. The independent
checker imports no builder or upstream project code. It checks the actual
coefficient hashes, all live nodes and input leaves, a separate binomial
quintic remainder, complete formal 32-sign norm evaluations, exceptional
zero-multiplier slices, and exact attained-degree certificates.

Compile standalone.tex twice with a standard pdfLaTeX installation. It uses
standard article, lmodern, amsmath, amssymb, booktabs, geometry, microtype and
hyperref packages. The supplied PDF was rendered and visually inspected.

## Mathematical provenance and boundary

The full-residue interpolation lemma and direct normalized signed-kernel
proof come from the explicitly pinned late package
ConZFC_Twelve_Integer_Interpolation_2026-10-24. Its proofs and source notices
are retained in inherited/. The six coherent fixed payloads, their finite
recipe, and the native/compiler/K215 ordinary proof dependencies are included.
MF is already shifted and must not be shifted again.

Unlike the earlier odd-multiplier chart, this proof does not claim that
(Delta*s*r-1)/2 is integral. The direct normalized signed-kernel theorem
handles the arbitrary nonzero multiplier. The zero-multiplier branch is
excluded algebraically before any rational norm factor is interpreted.

This is an ordinary mathematical consistency equivalence composed with the
named inherited proofs. It is neither a proof of Con(ZFC) nor a new
end-to-end Lean/Rocq certificate or encoded object-language ZFC derivation.
No upstream code was executed and no remote repository was changed.
