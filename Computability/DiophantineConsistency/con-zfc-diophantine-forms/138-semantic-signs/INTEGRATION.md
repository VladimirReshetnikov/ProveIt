# Integration notes

The packet is ready to unpack as a new research entry beneath
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`.
A suitable descriptive suffix is `semantic-signs-cofinal`; choose the
numeric prefix at integration time. The inspected snapshot ends at package
133. No existing equation, proof, index, or source module has been changed.

Keep the four component directories together with `report/`, the root
Python checker, endpoint catalog, source ledger, verification receipt, and
manifest. The root checker uses relative paths and needs no Git metadata.
It can be run directly after extraction.

Recommended index entries are:

- Direct signed quartic: 286 integer variables, 196 quadratic rows,
  6,607 monomials, height 128,446. This saves 38 variables from its matched
  parent while increasing support by 799.
- Direct sparse companion: 319 integer variables, 207 rows, 5,779 monomials,
  height 128,446.
- Natural quartics: (235 variables, 184 rows, 22,185 monomials, height
  90,911,633) and (236 variables, 185 rows, 15,645 monomials, height 88,233,865).
- Ten strictly positive inputs: 83 operations/degree 436, 81/560, and 80/750.
- Eleven unrestricted integer inputs: 107 operations/degree 924 and 108/840.

The direct branches use C222 and its ZF/ZFC finite-refutation interface.
The compact branches retain the separate native K215 calibration and full
large fixed numerals. Preserve that distinction in summaries.

All new equivalence arguments are ordinary proofs, not fresh end-to-end
proof-assistant certifications. The release includes finite exact
verification and separate internal reviews. A formalization should begin
with the negative-exponent lemma, even-frame anchor, linear cofinal bound,
and free auxiliary-coordinate transport, whose interfaces are isolated in
the report and component proofs.

For a repository that deduplicates inherited dependencies, the component
source ledgers identify exact existing copies. In particular
`integer11/RESTORED_DEPENDENCIES.json` records source paths for dependencies
that were omitted from the parent research packet but were restored here
with exactly matching hashes. Keep a mapping if such copies are removed;
the standalone ZIP intentionally includes them.

The root manifest seals this delivered tree. If integration changes any
tracked file or removes duplicates, regenerate the manifest and replay
the verification in the resulting tree; do not retain a stale manifest as
evidence for modified content.
