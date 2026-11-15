# Delivered iPRA proof packets

This directory holds the research packets that were delivered to `docs/drafts` as archives
on 14 and 15 November 2026. Each packet gives a human-readable proof of a classical theorem
of analysis, number theory or geometry. Each proof is in a finitary, quantitative form meant
for intuitionistic primitive recursive arithmetic (iPRA). Most packets also include
exact-arithmetic reference code and a Lean formalization plan or scaffold aimed at the iPRA
development in [`ConciseIPRA`](../../ConciseIPRA/README.md).

The packets are filed as delivered. Nothing in them was rerun, checked, compiled or edited
for this placement. The Lean files have not been built, and the summaries in the table below
only repeat what each packet says about itself. Several packets say that their Lean files are
uncompiled specifications or outlines, or that part of what was asked for is not proved.

## Layout

- Each archive has one directory, named after the archive without `.zip`.
- Every archive wraps its files in a single top directory. That directory is removed, so the
  archive member `<wrapper>/<path>` is the file `<directory>/<path>` here. The table gives
  each wrapper.
- Text files are stored under the repository's `.gitattributes`, which normalizes line
  endings to LF. Other bytes are as delivered.

## What is not placed

[`OMITTED.tsv`](OMITTED.tsv) lists every archive member that has no file here, with the
reason.

| Reason | Members | Where the bytes are |
|---|---:|---|
| `ignored` | 29 | The member matches the repository's `.gitignore`: 24 `SHA256SUMS` / `SHA256SUMS.txt` checksum manifests and 5 LaTeX `.log` files. It is available only from the delivered archive. |
| `sibling-packet` | 13 | `puiseux_ipra` bundles `dependencies/FTA_iPRA/`, a byte-identical copy of the packet filed in [`FTA_iPRA`](FTA_iPRA/). The reference column gives the placed file. |
| `sibling-archive` | 1 | `zeta_zeros_ipra_2026-11-15` bundles `dependencies/zeta_functional_equation_ipra.zip`, a byte-identical copy of the delivered archive filed in [`zeta_functional_equation_ipra`](zeta_functional_equation_ipra/). |
| `repository-copy` | 3 | `zeta_zeros_ipra_2026-11-15` bundles `sources/Deduction.lean`, `sources/NativeBiInterpretation.lean` and `sources/PR.lean`, byte-identical to the files of the same names in [`ConciseIPRA/Lean/ConciseIPRA`](../../ConciseIPRA/Lean/ConciseIPRA/). The reference column gives that file. |

Other checksum manifests (`MANIFEST.sha256`, `manifest.sha256`, `MANIFEST.txt`) are not
matched by `.gitignore` and are placed. None of them was verified. The README,
`SOURCE_MANIFEST.md` and article of `puiseux_ipra` still refer to its `dependencies/`
directory. Its files are in [`FTA_iPRA`](FTA_iPRA/). Likewise, `sections/status.tex` and
`sources/source_manifest.json` of `zeta_zeros_ipra_2026-11-15` still name its omitted
`dependencies/` archive and `sources/` copies.

To recover an omitted member, restore the archive from the commit that added it
(the Arrival column):

```bash
git show <arrival>:docs/drafts/<archive>.zip > <scratch>/<archive>.zip
```

## Packets

The 33 archives hold 683 members: 637 placed here, 29 ignored, 13 in the bundled copy of
a sibling packet, 1 nested copy of a sibling archive and 3 copies of repository files. P is the number of placed files and O the number of omitted members of each
packet. Arrival is the commit that added the archive to `docs/drafts`.

| Directory | Arrival | Wrapper in the archive | What the packet states | P | O |
|---|---|---|---|---:|---:|
| [`FTA_iPRA`](FTA_iPRA/) | `ea3f6066cf` 2026-11-14 | `FTA_iPRA` | An arithmetized constructive fundamental theorem of algebra, with a Lean formalization blueprint and exact rational reference programs. | 12 | 1 |
| [`basel_ipra`](basel_ipra/) | `ea3f6066cf` 2026-11-14 | `basel_ipra` | The Basel identity, ∑ 1/j² = π²/6, as a universally quantified PRA inequality. Its Lean files are uncompiled specifications and an outline. | 17 | 1 |
| [`bohr_mollerup_ipra_2026-11-15`](bohr_mollerup_ipra_2026-11-15/) | `b2d7526ffc` 2026-11-15 | `bohr_mollerup_ipra` | A finitary constructive Bohr–Mollerup theorem, with a structured Lean scaffold and roadmap. | 13 | 0 |
| [`brun_ipra_2026-11-15`](brun_ipra_2026-11-15/) | `fb79243454` 2026-11-15 | `brun_ipra` | Brun's theorem on twin-prime reciprocals, with a primitive-recursive Cauchy modulus. | 20 | 1 |
| [`calculus_ipra`](calculus_ipra/) | `6ad3d9f371` 2026-11-14 | `calculus_ipra` | Effective versions of both parts of the fundamental theorem of calculus and the finite-order Euler–Maclaurin formula. | 12 | 1 |
| [`cauchy_residue_ipra`](cauchy_residue_ipra/) | `4ea4d4a14a` 2026-11-15 | `cauchy_residue_ipra` | Quantitative constructive versions of Cauchy's integral theorem and the residue theorem, stated as schemas. | 13 | 1 |
| [`desargues_pascal_ipra`](desargues_pascal_ipra/) | `4ea4d4a14a` 2026-11-15 | `desargues_pascal_ipra` | Desargues' and Pascal's theorems, with a formalization roadmap and a repository-source audit. | 28 | 0 |
| [`dimension_invariance_ipra`](dimension_invariance_ipra/) | `f616f72b66` 2026-11-15 | `dimension_invariance_ipra` | Quantitative dimension invariance for finite rational tables, via cubical Sperner parity on staggered grids. | 13 | 1 |
| [`diophantine_geometry_ipra`](diophantine_geometry_ipra/) | `d72c8b2463` 2026-11-15 | `diophantine_geometry_ipra` | Selected rational Diophantine geometry: bounded-height enumeration, height inequalities for maps of P¹, rational preperiodic points, conic parametrization, and Fermat's square-area theorem by finite descent. It states that its Lean arithmetic core is compiled. | 38 | 1 |
| [`diophantine_ipra_2026-11-15`](diophantine_ipra_2026-11-15/) | `b5a3ad0377` 2026-11-15 | `diophantine_ipra` | Størmer's theorem, a constructive Davenport–Schmidt theorem, and Roth cutoffs for quadratic irrationals. It says the general effective Roth cutoff is not proved and its Lean files are not compiled. | 23 | 1 |
| [`dirichlet_kronecker_ipra`](dirichlet_kronecker_ipra/) | `db4b793b19` 2026-11-14 | `dirichlet_kronecker_ipra` | Logical obstructions to the unrestricted statements, with constructive scalar and simultaneous Dirichlet approximation and quantitative Kronecker theorems. | 23 | 1 |
| [`eight_geometry_theorems_ipra`](eight_geometry_theorems_ipra/) | `390098877e` 2026-11-15 | `eight_geometry_theorems_ipra` | Constructive coordinate proofs of eight theorems: Pappus's harmonic theorem, Ceva, Menelaus, Carnot's conic and polygon theorems, Hoehn, Pappus's hexagon theorem and Brianchon. | 31 | 0 |
| [`euler_rodrigues_ipra`](euler_rodrigues_ipra/) | `db4b793b19` 2026-11-14 | `euler_rodrigues_ipra` | Euler's rotation theorem and Rodrigues' formula. It says the unrestricted exact-axis form is not constructively provable (LLPO reduction) and proves constructive replacements. | 21 | 2 |
| [`goldbach_euler_ipra`](goldbach_euler_ipra/) | `d72c8b2463` 2026-11-15 | `goldbach_euler_ipra` | The Goldbach–Euler theorem, ∑ 1/(p−1) = 1 over perfect powers p, with an explicit convergence modulus. Its Lean outline has explicit `sorry` obligations. | 13 | 1 |
| [`hurwitz_khinchin_ipra`](hurwitz_khinchin_ipra/) | `b5a3ad0377` 2026-11-15 | `hurwitz_khinchin_ipra` | Sharp constructive Hurwitz approximation and quantitative constructive Khinchin approximation. | 18 | 1 |
| [`isoperimetric_ipra`](isoperimetric_ipra/) | `0bf379a842` 2026-11-14 | `isoperimetric_ipra` | The sharp planar isoperimetric inequality L² ≥ 4πA, with its equality characterization, for effective presentations. | 16 | 0 |
| [`jordan_ipra_constructive_2026-11-15`](jordan_ipra_constructive_2026-11-15/) | `4ea4d4a14a` 2026-11-15 | `jordan_ipra` | A quantitative Jordan curve theorem for primitive-recursively presented circle embeddings. | 22 | 1 |
| [`minkowski_ipra`](minkowski_ipra/) | `057b790401` 2026-11-14 | `minkowski_ipra` | Minkowski's convex-body theorem. | 37 | 1 |
| [`morley_ipra_constructive`](morley_ipra_constructive/) | `58087eb241` 2026-11-15 | `morley_ipra_constructive` | Morley's trisector theorem, stated over finite exact certificates. | 13 | 1 |
| [`pappus_centroid_ipra_2026-11-15`](pappus_centroid_ipra_2026-11-15/) | `7b3c755844` 2026-11-15 | `pappus_centroid_ipra` | Pappus's surface and volume centroid theorems, with τ = 2π presented by nested regular polygons. | 16 | 1 |
| [`pell_ipra_2026-11-15`](pell_ipra_2026-11-15/) | `b5a3ad0377` 2026-11-15 | `pell_ipra` | Pell equations for every nonsquare D ≥ 2, with an audit of their algorithms and induction invariants in iPRA. | 18 | 1 |
| [`platonic_solids_ipra`](platonic_solids_ipra/) | `58087eb241` 2026-11-15 | `platonic_solids_ipra` | Exactly five similarity classes of Platonic solids, for constructible-coordinate codes. | 25 | 2 |
| [`pnt_ipra_constructive_2026-11-14`](pnt_ipra_constructive_2026-11-14/) | `ea3f6066cf` 2026-11-14 | `pnt_ipra` | An explicit arithmetic prime number theorem with quantifier-free induction, and the passage to the logarithmic statement. | 14 | 0 |
| [`pnt_li_ipra_2026-11-15`](pnt_li_ipra_2026-11-15/) | `d72c8b2463` 2026-11-15 | `pnt_li_ipra` | Logarithmic-integral strengthenings of the prime number theorem: an explicit stretched-exponential bound on π(n) − Li₂(n), and the full asymptotic expansion with explicit remainders. | 23 | 0 |
| [`prime_reciprocal_ipra_2026-11-15`](prime_reciprocal_ipra_2026-11-15/) | `52eb7d907b` 2026-11-15 | `prime_reciprocal_ipra_2026-11-15` | Divergence of the reciprocal-prime sum in the explicit form ∑_{p ≤ 2^(2·4^k)} 1/p > k. | 11 | 0 |
| [`puiseux_ipra`](puiseux_ipra/) | `8c135f6f2a` 2026-11-15 | `puiseux_ipra` | Puiseux expansions for exactly presented algebraic coefficients, with explicit convergence radii and tail bounds. It bundles the FTA packet as a dependency. | 17 | 14 |
| [`stirling_ipra`](stirling_ipra/) | `38cafaa5be` 2026-11-14 | `stirling_ipra` | Stirling's formula, with finite rational estimates and an induction audit. | 10 | 1 |
| [`taylor_cauchy_ipra`](taylor_cauchy_ipra/) | `daade03000` 2026-11-15 | `taylor_cauchy_ipra` | Taylor's theorem with integral and Peano remainders, and Cauchy's integral formula. | 13 | 1 |
| [`three_impossibilities_ipra`](three_impossibilities_ipra/) | `a28886c88e` 2026-11-15 | `three_impossibilities_ipra` | The impossibility of doubling the cube, trisecting 60° and squaring the circle by straightedge and compass. It is stated as a proof architecture. | 12 | 1 |
| [`transcendence_ipra`](transcendence_ipra/) | `c5093c20b5` 2026-11-14 | `transcendence_ipra` | Transcendence of e and π as explicit apartness bounds for nonzero integer polynomials. | 18 | 1 |
| [`triangle_formulas_ipra`](triangle_formulas_ipra/) | `c1bda76f7f` 2026-11-14 | `triangle_ipra` | Heron's formula and the laws of sines and cosines, in explicit finite arithmetic versions. | 21 | 3 |
| [`zeta_functional_equation_ipra`](zeta_functional_equation_ipra/) | `db4b793b19` 2026-11-14 | `zeta_ipra` | Riemann's functional equation for ζ in quantitative form, with a formalization plan for its finite arithmetic content. | 31 | 0 |
| [`zeta_zeros_ipra_2026-11-15`](zeta_zeros_ipra_2026-11-15/) | `d72c8b2463` 2026-11-15 | `zeta_zeros_ipra` | Quantitative zero distribution of ζ: nonvanishing regions, trivial zeros, the Riemann–von Mangoldt estimate and local counts. It also certifies one critical-line zero near 1/2 + 14.1347i. | 25 | 5 |
