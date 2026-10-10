# Focused corrections and qualifications

## C1: Clausen-index parity terminology

Source: `Analysis/Polylogarithms/docs/manuscript/chapters/02-cyclotomic.tex` at commit `aeafd6e9b843b589a3bf66850d15bf8ad0e196dd`, blob `89d2885681b701de3348d6074749fd9288b54b3c`.

Location: the section titled **The fundamental constants, by conductor**.

Existing sentence (whitespace normalized):

> Odd Clausen values use the odd character sector.

The chapter defines even-index Clausen values as imaginary parts and odd-index Clausen values as real parts. Under that convention the sentence confuses index parity with sine/cosine parity.

Proposed replacement:

> Imaginary, sine-type cyclotomic values use the odd character sector; real, cosine-type values use the even sector. Under the Clausen convention used here, even-index Clausen functions belong to the odd sector and odd-index Clausen functions belong to the even sector.

The source chapter's own Cl3 example with the even quadratic character of conductor 5 supports this correction. No claim is made that the correctly stated DFT formulas in the chapter are false.

`propose_clausen_correction.py` finds exactly one matching sentence, prints a real unified diff against the supplied local repository, and refuses an unexpected source version on an apply operation unless explicitly overridden. No repository file was changed in preparing this delivery.

## C2: Integral versus field-valued relation transport

This is a scope clarification, not a demonstrated false equation. A DFT and its inverse operate over the stated cyclotomic field; inverse Fourier matrices need not be unimodular over integral coefficient rings. Thus “DFT-conjugacy of relation lattices” should not be read as an integral Smith-form assertion without an explicit denominator analysis.

The new report demonstrates the distinction: the unreflected weighted distribution matrix has a unit maximal minor, whereas reflection coinvariants can contain nonzero 2-torsion. Rational ranks alone do not see that torsion.

## C3: Preserve the distinction between two kinds of jets

The characteristic-two jets in the new theorem are power-series deformations of formal algebraic weights. The spectral derivatives of complex polylogarithms are analytic jets with prime-logarithm coefficients. There is no asserted reduction modulo two of complex logarithms or of arbitrary complex spectral parameters.

## Status boundaries

The original characteristic-zero conductor normal form is not retracted. Classical ordinary distribution and sign cohomology results remain attributed to their antecedents. The S6 conjecture retains its unresolved status. Numerical residuals in the package are diagnostics, not interval certificates or independence proofs.
