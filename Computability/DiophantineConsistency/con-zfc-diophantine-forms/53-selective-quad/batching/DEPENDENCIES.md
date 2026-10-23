# Dependency boundary and fixed coefficient instance

All repository sources reviewed for this supplement are pinned to ProveIt
commit `124c07c0b77a9e20e84676514d8b1ff78536ea3f` in `SOURCE_PINS.json`.
Every listed local file matches both its SHA256 and its Git blob SHA.
Historical commit names inside copied sources remain historical provenance;
they do not override this review pin or select different coefficient bytes.

## What this supplement proves

`PROOF.md` proves, over eleven strictly positive supplied variables, that
the displayed norm-product equation is solvable exactly when the inherited
normalized blank-K215 compiler has a canonical witness. It treats all formal
sign branches, excludes exceptional inner denominators, reconstructs positive
`h` and `gamma`, and constructs a strictly positive new carrier in the reverse
direction. It also proves the exact degrees and the shifted-system equivalence.

The new steps are the weighted radical gap and denominator-Y absorption.
The source38 signed-index reconstruction and source44 multiplier-one recovery
are reproduced with their required hypotheses, not applied circularly before
the deleted index quotient is recovered.

## Immediate copied mathematical dependencies

- `upstream/eleven/ELEVEN_POSITIVE_PROOF.md`, Sections 4-6: rational Pell
  saturation, normalized strong divisibility, signed auxiliary-index reduction,
  and short-index reconstruction.
- `upstream/TWELVE_POSITIVE_PROOF_PINNED.md`, Sections 4-8: multiplier-one
  norm, modular exceptional-root exclusion, canonical completeness, and
  degree-892/896 Laurent factor certificates. This is the canonical source44
  proof; the unpinned filename `TWELVE_POSITIVE_PROOF.md` is reference-only.
- `upstream/COEFFICIENT_PROOF.md`, Sections 1-5: the actual complete Wang943
  121-by-8801 tuple adapter, including clauses, carries, masks, unbounded rank
  adjustment, positive slack and signed-completeness promises.
- `upstream/NORMALIZED_COMPILER_PROOF.md`, Sections 7-8, and
  `upstream/RATIO12_PROOF.md`, Section 7: the normalized blank-compiler interface
  and its harmless signed strong-root/quotient convention. These copied sources
  refer further to the package09/package20 normalized compiler theorem.

`upstream/SIGNED10_PROOF.md`, Section 2, identifies the same selected tuple.
It cites the coefficient adapter rather than replacing it. None of its Sun
representation or ten-unrestricted-integer finalization is needed here.

## Fixed instance and historical files

The only active four ports are the bytes named by `COEFFICIENT_BINDING.json`:
`beta`, `K0=K`, `MC`, and `MF=MF_source`. They must be selected together.
`MF_source` is already shifted. The byte order is unsigned little-endian.
The four uncompressed sizes total 533,099 bytes; the largest port is
1,070,004 bits. The adapter proves these numbers supply the inherited
compiler interface, not just a finite algebraic test instance.

`coefficients/original_binding.json` is an unmodified historical record.
Its original relative path to the coefficient proof does not resolve in this
relocated package; the active binding points to the included adapter above.
Historical circuit builders in `upstream/` are inert reference material and
are never imported or executed by the active builder or independent audits.

## Inherited logical endpoint, not newly certified here

The marked-Wang/native-Pell compiler theorem and the blank-K215 equivalence to
existence of a finite ZFC refutation remain inherited mathematical inputs.
Composing those theorems with this supplement gives an ordinary proof,
formalizable in ZFC, that no positive solution is equivalent to Con(ZFC).
The package does not supply a new end-to-end Lean/Rocq proof, a new object-level
ZFC derivation, an independent human review, or a consistency decision.

The finite programs verify payload binding, algebraic transcription, exact
degree attainment, gate counts, and selected arithmetic inequalities. They do
not verify the unbounded compiler or exhibit a calibrated halting witness.
