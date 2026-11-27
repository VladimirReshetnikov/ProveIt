# Generalized Riemann Hypothesis

Research packets on what lies beyond the generalized Riemann hypothesis for Dirichlet
L-functions. They are filed as delivered and are not formalized or checked here.

This directory holds the 61 archives that were delivered to
[`docs/incoming`](../../docs/incoming/README.md) on 25 and 26 November 2026, in 28 arrival
commits from `1e1728ad22` to `de7b92e9c3`. Each archive is one research packet: a LaTeX
report with its PDF, a delivery README, verification programs, their recorded outputs, and
source and provenance audits. In all, 1795 files are placed: 408 `.tex`, 88 `.pdf`, 272 `.lean`
and 1027 others.

By their own account, the packets start from the Lean development
[`lsernau/grh-lean`](https://github.com/lsernau/grh-lean), which they describe as a proof of
the Riemann hypothesis and of GRH for Dirichlet L-functions. Every packet cites its commit
`72fead102f663d5c7a407964a13dc0cf9d977207`. They ask what that theorem settles elsewhere, and
which of the methods inside the proof carry over to other problems. The subjects named in
the delivery READMEs include imaginary quadratic fields of class-group exponent six and
seven, sparse equations for singular moduli, densities of sets without geometric
progressions (several conjectures and questions of McNew), torsion specialization,
one-sided prime sums and prime races for nonabelian Galois groups, spanning-tree valuations
in graph towers, and Lubin–Tate jet recovery. Several packets state that a part of what
they aim at is a conditional route or an open target, not a proof.

Nothing in the packets was rerun, checked, compiled or edited for this placement. The
mathematical claims have not been independently reviewed, and the titles in the table
below only repeat each delivery README. The `.lean` files have not been built. They are not
part of ProveIt's Lake package: no library of the root `lakefile.toml` has its sources here.
Most of them are excerpts of the upstream development, which is under the Apache-2.0
licence. Its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` texts are in
[`Research/grh_transfer_analysis/licenses`](Research/grh_transfer_analysis/licenses/), as
`upstream_APACHE-2.0.txt`, `upstream_NOTICE.txt` and `upstream_ATTRIBUTION.txt`.

## Merged article

[`Article/article.pdf`](Article/article.pdf) merges all 61 reports into one article. Each
result is stated once, in the strongest form the reports prove; repeated material and results
implied by stronger or more general ones are left out, and the reports' many accounts of the
upstream proof are replaced by one section. Like the packets, the article is not an
independent check: its mathematics is that of the reports. Every result is marked as
unconditional, as using Dirichlet GRH, or as a reduction whose target estimate is open. The
[article README](Article/README.md) lists its sections, and the
[provenance tables](Article/provenance/README.md) record, for every section of every report,
where its material went and which result supersedes each omitted one.

## Layout

- [`Research/`](Research/) has one directory per archive, named after the archive without
  `.zip`. `grh_method_transfers_2026-11-25 (2).zip` is in `grh_method_transfers_2026-11-25_2`. `grh_method_transfers_2026-11-25(1).zip` is in `grh_method_transfers_2026-11-25_1`.
- 52 archives wrap their files in a single top directory. That directory is removed, so the
  archive member `<wrapper>/<path>` is the file `Research/<directory>/<path>` here. The table
  gives each wrapper, or `none` for the 9 archives without one.
- A file that a packet shares with an earlier packet is kept only in the earlier one (see
  [Files shared between packets](#files-shared-between-packets)), so 17 directories are
  not complete on their own.
- Text files are stored under the repository's `.gitattributes`, which normalizes line
  endings to LF; 35 placed files were delivered with CRLF line endings. Other bytes are as
  delivered.
- The largest file is `Research/grh_transfer_analysis/evidence/upstream_source_72fead1.tar.gz`
  (10.9 MB), that packet's copy of the upstream source tree.

## What is not placed

[`Research/OMITTED.tsv`](Research/OMITTED.tsv) lists every archive member that has no file
here, with the reason. Its directory column gives the directory under `Research/`, and its
member column the path inside that directory.

| Reason | Members | What they are |
|---|---:|---|
| `ignored` | 151 | The member matches the repository's `.gitignore`: 44 `SHA256SUMS` and 8 `SHA256SUMS.txt` checksum manifests, 67 `.log` files from LaTeX builds and from test and verification runs, 31 `.out` files and 1 `.fls` file. The `.out` files are recorded outputs of check programs in 6 packets; the rule for LaTeX auxiliary files matches their name. |
| `checksum-manifest` | 3 | The member lists SHA-256 digests of the packet's own files, under a name that `.gitignore` does not match: two `MANIFEST.sha256` files and one `evidence/UPSTREAM_SHA256SUMS.txt`. |
| `sibling-archive` | 2 | `grh_transfer_bridges_2026-11-25` bundles, under `prior/`, byte-identical copies of two delivered archives of this set. Their contents are in [`Research/grh_cm_four_terms_and_prime_bias`](Research/grh_cm_four_terms_and_prime_bias/) and [`Research/grh_sparse_singular_moduli`](Research/grh_sparse_singular_moduli/). |
| `sibling-packet` | 299 | The member is byte-identical to a file of an earlier packet of this set. The reference column gives that file, as `<directory>/<path>` under `Research/`. |
| Total | 455 | |

No checksum manifest is kept, and none was verified. A file counts as one when it is a
list of digests of the packet's own files. Digest lists of the upstream publication
(`evidence/source-files.sha256` and `evidence/exports.sha256` of `grh_lean_transfer_analysis`)
and the JSON, CSV and text provenance records that carry digests beside other content are
placed. Several packets still name an omitted file in a README, build script, source
manifest or check output.

Every omitted member is available from its delivered archive, which stays in the history:

```
git show <arrival>:"docs/incoming/<archive>.zip" > <scratch>/<archive>.zip
```

### Files shared between packets

Many packets carry excerpts of the upstream development under `upstream/`,
`evidence/upstream/`, `sources/upstream/`, `sources/grh-lean/` or `source_excerpt/`, and some
carry files of an earlier packet of this set, mostly under `prior/`, `previous/` or
`predecessors/`. Such a file is placed once, in the packet that arrived first (packets of
one arrival commit are taken in the order of their archive names). The 299 later copies in
17 packets are omitted as `sibling-packet`: 153 `.lean` files, 49 licence, notice and
attribution texts, and 97 other files. Each was compared byte for byte with the file
named in its reference column.

The rule has two limits. Identical files of under 64 bytes are treated as coincidences
and stay: 12 placed files (`lean-toolchain` pins and one `requirements.txt`) equal a file of
an earlier packet. Identical files inside one packet also stay.

## Packets

The table is in arrival order. Members = placed + omitted for every row.

| Directory | Archive | Arrival | Wrapper | Members | Placed | Omitted | Title in the delivery README |
|---|---|---|---|---:|---:|---:|---|
| [grh-lean-transfers](Research/grh-lean-transfers/README.txt) | `grh-lean-transfers.zip` | `1e1728ad22` | `grh-transfers` | 26 | 22 | 4 | Beyond Dirichlet GRH: Coefficient fields of CM newforms and one-sided prime estimates |
| [grh-transfer](Research/grh-transfer/README.md) | `grh-transfer.zip` | `1e1728ad22` | `grh-transfer` | 28 | 28 | 0 | What Dirichlet GRH settles |
| [grh_transfers](Research/grh_transfers/README.md) | `grh_transfers.zip` | `1e1728ad22` | `grh_transfers` | 17 | 17 | 0 | From Dirichlet GRH to class groups and prime races |
| [grh_transfer_analysis](Research/grh_transfer_analysis/README.txt) | `grh_transfer_analysis.zip` | `a92443f006` | `grh_transfer_analysis` | 25 | 22 | 3 | BEYOND DIRICHLET GRH: Transferable methods, established consequences, and a concrete Hecke target |
| [grh_transfer_analysis_2026-11-25](Research/grh_transfer_analysis_2026-11-25/README.md) | `grh_transfer_analysis_2026-11-25.zip` | `a92443f006` | `grh_transfer_report` | 15 | 14 | 1 | Beyond Dirichlet GRH: source audit and transfer analysis |
| [grh_lean_transfer_analysis](Research/grh_lean_transfer_analysis/README.txt) | `grh_lean_transfer_analysis.zip` | `b35eb211b8` | `grh_transfer_review` | 48 | 35 | 13 | WHAT CAN BE TRANSFERRED FROM GRH-LEAN? |
| [grh-arithmetic-transfers](Research/grh-arithmetic-transfers/README.md) | `grh-arithmetic-transfers.zip` | `981d2bff32` | `grh-arithmetic-transfers` | 39 | 32 | 7 | What Dirichlet GRH settles beyond the zero theorem |
| [grh_cm_prime_applications](Research/grh_cm_prime_applications/README.txt) | `grh_cm_prime_applications.zip` | `c59bde1a0f` | `grh_cm_prime_applications` | 37 | 28 | 9 | Applications of the Dirichlet GRH theorem in grh-lean |
| [grh-exponent-six-and-transfers](Research/grh-exponent-six-and-transfers/README.md) | `grh-exponent-six-and-transfers.zip` | `13c30b3b67` | `grh-exponent-six-and-transfers` | 39 | 33 | 6 | The 432 imaginary quadratic fields of class-group exponent six |
| [grh_beyond_dirichlet_grh_2026-11-25](Research/grh_beyond_dirichlet_grh_2026-11-25/README.md) | `grh_beyond_dirichlet_grh_2026-11-25.zip` | `b65aa62294` | `grh_beyond_transfer` | 251 | 244 | 7 | Beyond Dirichlet GRH |
| [grh_cm_four_terms_and_prime_bias](Research/grh_cm_four_terms_and_prime_bias/README.md) | `grh_cm_four_terms_and_prime_bias.zip` | `b65aa62294` | `grh_cm_and_prime_bias` | 27 | 26 | 1 | Sparse equations for singular moduli and the sign of weighted prime sums |
| [grh_method_transfers_2026-11-25](Research/grh_method_transfers_2026-11-25/README.txt) | `grh_method_transfers_2026-11-25.zip` | `432747f0a3` | `grh_method_transfers_2026-11-25` | 49 | 39 | 10 | BEYOND DIRICHLET GRH -- TRANSFER ANALYSIS |
| [grh_method_transfers_2026-11-25_1](Research/grh_method_transfers_2026-11-25_1/README.txt) | `grh_method_transfers_2026-11-25(1).zip` | `f103286429` | `grh_method_transfers_2026-11-25` | 59 | 41 | 18 | BEYOND THE DIRICHLET GRH ENDPOINT |
| [grh_cm_sparse_equations](Research/grh_cm_sparse_equations/README.md) | `grh_cm_sparse_equations.zip` | `59fdad3ee0` | `grh_cm_sparse_equations` | 46 | 28 | 18 | Sparse equations for singular moduli |
| [grh_sparse_singular_moduli](Research/grh_sparse_singular_moduli/README.md) | `grh_sparse_singular_moduli.zip` | `a5e5f65240` | `grh_sparse_singular_moduli` | 63 | 51 | 12 | Five-term equations for singular moduli |
| [grh_sylow_transfer_2026-11-25](Research/grh_sylow_transfer_2026-11-25/README.md) | `grh_sylow_transfer_2026-11-25.zip` | `a5e5f65240` | none | 11 | 10 | 1 | Beyond Dirichlet GRH: Sylow-filtered prime races |
| [dirichlet-grh-research](Research/dirichlet-grh-research/README.md) | `dirichlet-grh-research.zip` | `5cbdc86d13` | `dirichlet-grh-research` | 33 | 32 | 1 | Beyond Dirichlet GRH |
| [grh_relative_prime_races_2026-11-25](Research/grh_relative_prime_races_2026-11-25/README.md) | `grh_relative_prime_races_2026-11-25.zip` | `5cbdc86d13` | `grh_relative_prime_races` | 9 | 7 | 2 | Relative zeta zeros from compressed prime races |
| [psl2_grh_transfer](Research/psl2_grh_transfer/README.md) | `psl2_grh_transfer.zip` | `eefb831ae4` | none | 8 | 7 | 1 | Beyond Dirichlet GRH: sharp PSL2 transfer |
| [grh_reflection_transfer_2026-11-25](Research/grh_reflection_transfer_2026-11-25/README.md) | `grh_reflection_transfer_2026-11-25.zip` | `36d291a86b` | none | 9 | 8 | 1 | Reflection detectors for nonabelian Riemann hypotheses |
| [grh_cyclic_generator_transfer_2026-11-25](Research/grh_cyclic_generator_transfer_2026-11-25/README.md) | `grh_cyclic_generator_transfer_2026-11-25.zip` | `47eb73a0c7` | `grh_cyclic_transfer` | 11 | 10 | 1 | Beyond Dirichlet GRH: cyclic-generator prime races and linear auxiliary windows |
| [grh_a6_transfer_2026-11-25](Research/grh_a6_transfer_2026-11-25/README.md) | `grh_a6_transfer_2026-11-25.zip` | `6fe2c1bd45` | none | 11 | 11 | 0 | A6 nonabelian RH transfer |
| [grh_deficit_transfer_2026-11-25](Research/grh_deficit_transfer_2026-11-25/README.md) | `grh_deficit_transfer_2026-11-25.zip` | `6fe2c1bd45` | `grh_deficit_transfer` | 11 | 9 | 2 | Positive Frobenius deficits: a transfer beyond Dirichlet GRH |
| [grh_kummer_window_transfer_2026-11-25](Research/grh_kummer_window_transfer_2026-11-25/README.md) | `grh_kummer_window_transfer_2026-11-25.zip` | `6fe2c1bd45` | none | 8 | 7 | 1 | Polynomial auxiliary scales and Kummer prime races |
| [grh_method_transfers_2026-11-25_2](Research/grh_method_transfers_2026-11-25_2/README.md) | `grh_method_transfers_2026-11-25 (2).zip` | `6fe2c1bd45` | `grh_method_transfers` | 57 | 33 | 24 | Beyond Dirichlet GRH: Averaged zero detection and exact K-theory transfer tests |
| [grh_quantitative_twists_2026-11-25](Research/grh_quantitative_twists_2026-11-25/README.md) | `grh_quantitative_twists_2026-11-25.zip` | `6fe2c1bd45` | none | 8 | 7 | 1 | Beyond Dirichlet GRH: quantitative twisting |
| [grh-torsion-and-prime-sampling](Research/grh-torsion-and-prime-sampling/README.md) | `grh-torsion-and-prime-sampling.zip` | `274841c1cb` | none | 21 | 20 | 1 | Torsion specialization and sparse prime sums |
| [grh-torsion-and-zero-data](Research/grh-torsion-and-zero-data/README.md) | `grh-torsion-and-zero-data.zip` | `274841c1cb` | `grh-torsion-and-zero-data` | 23 | 22 | 1 | How far must a torsion selector search? |
| [grh_exact_torsion_transfer_2026-11-25](Research/grh_exact_torsion_transfer_2026-11-25/README.txt) | `grh_exact_torsion_transfer_2026-11-25.zip` | `274841c1cb` | `grh_exact_torsion_transfer` | 28 | 27 | 1 | BEYOND DIRICHLET GRH: EXACT TORSION SPECIALIZATION AND THE LIMITS OF TRANSFER |
| [grh_structural_transfers_2026-11-25](Research/grh_structural_transfers_2026-11-25/README.md) | `grh_structural_transfers_2026-11-25.zip` | `274841c1cb` | `grh_structural_transfers` | 49 | 29 | 20 | Beyond Dirichlet GRH: structural transfer analysis |
| [grh_transfers_singular_moduli_and_symmetric_powers](Research/grh_transfers_singular_moduli_and_symmetric_powers/README.md) | `grh_transfers_singular_moduli_and_symmetric_powers.zip` | `274841c1cb` | none | 17 | 16 | 1 | Sparse equations for singular moduli and optimal tests for symmetric-power zeros |
| [grh_transfer_synthesis_2026-11-25](Research/grh_transfer_synthesis_2026-11-25/README.md) | `grh_transfer_synthesis_2026-11-25.zip` | `28ad287a8d` | `grh_transfer_synthesis` | 121 | 65 | 56 | Beyond Dirichlet GRH: Validated arithmetic and transferable proof machinery |
| [grh-progression-densities-and-cubic-prime-race](Research/grh-progression-densities-and-cubic-prime-race/README.md) | `grh-progression-densities-and-cubic-prime-race.zip` | `d31039a48d` | `grh-research` | 19 | 18 | 1 | Geometric progressions and one-sided prime sums |
| [grh_method_transfers_sharp_torsion](Research/grh_method_transfers_sharp_torsion/README.md) | `grh_method_transfers_sharp_torsion.zip` | `d31039a48d` | `grh-method-transfers` | 24 | 24 | 0 | The optimal torsion window and one-sided prime tests |
| [grh_sharp_torsion_and_symplectic_blocks](Research/grh_sharp_torsion_and_symplectic_blocks/README.md) | `grh_sharp_torsion_and_symplectic_blocks.zip` | `d31039a48d` | `grh_sharp_transfers` | 19 | 18 | 1 | Beyond Dirichlet GRH |
| [grh-methods-polynomial-density](Research/grh-methods-polynomial-density/README.md) | `grh-methods-polynomial-density.zip` | `7af2d6e471` | `grh-methods` | 23 | 23 | 0 | Geometric-progression density over finite fields |
| [grh_fixed_field_transfer_2026-11-25](Research/grh_fixed_field_transfer_2026-11-25/README.md) | `grh_fixed_field_transfer_2026-11-25.zip` | `7af2d6e471` | `grh_fixed_field_transfer_2026-11-25` | 38 | 34 | 4 | Beyond Dirichlet GRH: sharp torsion specialization |
| [grh_method_transfers_research](Research/grh_method_transfers_research/README.md) | `grh_method_transfers_research.zip` | `7af2d6e471` | `grh_method_transfers_research` | 22 | 21 | 1 | Three transfers from the proof of Dirichlet GRH |
| [grh_sharp_transfers_2026-11-25](Research/grh_sharp_transfers_2026-11-25/README.md) | `grh_sharp_transfers_2026-11-25.zip` | `7af2d6e471` | `grh_sharp_transfers_2026-11-25` | 35 | 34 | 1 | Beyond Dirichlet GRH: sharp torsion selection and tensor detectors |
| [exponent_seven_and_grh_transfers](Research/exponent_seven_and_grh_transfers/README.md) | `exponent_seven_and_grh_transfers.zip` | `ff8161efa6` | `exponent_seven_and_grh_transfers` | 41 | 37 | 4 | The exponent-seven census and four transfers from the Lean proof of Dirichlet GRH |
| [grh_nonabelian_transfer_2026-11-25](Research/grh_nonabelian_transfer_2026-11-25/README.md) | `grh_nonabelian_transfer_2026-11-25.zip` | `48efe71a72` | `grh_transfer_2026-11-25` | 53 | 30 | 23 | Beyond Dirichlet GRH: optimal frames and an unramified nonabelian transfer |
| [grh_beyond_dirichlet_2026-11-25](Research/grh_beyond_dirichlet_2026-11-25/README.txt) | `grh_beyond_dirichlet_2026-11-25.zip` | `1667e16cee` | `grh_beyond_dirichlet` | 36 | 35 | 1 | BEYOND DIRICHLET GRH: Validated transfers, a sharper density certificate, and a concrete Hecke target |
| [grh_method_transfers_graph_towers_and_finite_rings](Research/grh_method_transfers_graph_towers_and_finite_rings/README.txt) | `grh_method_transfers_graph_towers_and_finite_rings.zip` | `1667e16cee` | `grh_method_transfers` | 31 | 30 | 1 | CYCLOTOMIC VALUATIONS IN GRAPH TOWERS AND PROGRESSION-FREE SETS OVER FINITE RINGS |
| [grh_transfer_bridges_2026-11-25](Research/grh_transfer_bridges_2026-11-25/README.md) | `grh_transfer_bridges_2026-11-25.zip` | `1667e16cee` | `grh_transfer_bridges_2026-11-25` | 32 | 27 | 5 | Beyond Dirichlet GRH |
| [grh_transfers_cycle_signings_and_lubin_tate](Research/grh_transfers_cycle_signings_and_lubin_tate/README.md) | `grh_transfers_cycle_signings_and_lubin_tate.zip` | `1667e16cee` | `grh_transfers` | 19 | 19 | 0 | Optimal signings of square cycles and sharp Lubin–Tate jet recovery |
| [grh_transfers_density_gaps_and_zero_tests](Research/grh_transfers_density_gaps_and_zero_tests/README.md) | `grh_transfers_density_gaps_and_zero_tests.zip` | `1667e16cee` | `grh_transfers` | 32 | 31 | 1 | Geometric progressions and nonabelian zero tests |
| [grh_dihedral_47_71](Research/grh_dihedral_47_71/README.md) | `grh_dihedral_47_71.zip` | `6799d49abd` | `grh_dihedral_47_71` | 27 | 26 | 1 | Beyond Dirichlet GRH at conductors 47 and 71 |
| [grh_method_transfers_2026-11-26](Research/grh_method_transfers_2026-11-26/README.md) | `grh_method_transfers_2026-11-26.zip` | `6799d49abd` | none | 23 | 22 | 1 | Beyond Dirichlet GRH |
| [mcnew_density_and_grh_transfers](Research/mcnew_density_and_grh_transfers/README.md) | `mcnew_density_and_grh_transfers.zip` | `6799d49abd` | `mcnew_density_and_grh_transfers` | 26 | 25 | 1 | A density separation for geometric progressions |
| [grh_arithmetic_transfers_2026-11-26](Research/grh_arithmetic_transfers_2026-11-26/README.txt) | `grh_arithmetic_transfers_2026-11-26.zip` | `d80526e421` | `grh_arithmetic_transfers` | 74 | 42 | 32 | TRACE CONGRUENCES AND ARITHMETIC TRANSFERS FROM GRH-LEAN |
| [grh_ideal_densities_and_transfer_conditions_2026-11-26](Research/grh_ideal_densities_and_transfer_conditions_2026-11-26/README.md) | `grh_ideal_densities_and_transfer_conditions_2026-11-26.zip` | `d80526e421` | `grh_ideal_densities_and_transfer_conditions` | 74 | 36 | 38 | Beyond Dirichlet GRH: Ideal Densities and Arithmetic Transfer Conditions |
| [grh_transfer_advances_2026-11-26](Research/grh_transfer_advances_2026-11-26/README.txt) | `grh_transfer_advances_2026-11-26.zip` | `d80526e421` | `grh_transfer_advances_2026-11-26` | 102 | 49 | 53 | BEYOND DIRICHLET GRH: Certified graph optima and quantitative local transfers |
| [Effective_Graph_Towers](Research/Effective_Graph_Towers/README.txt) | `Effective_Graph_Towers.zip` | `28bcd392fe` | `graph-tower-algorithm` | 19 | 19 | 0 | WHEN DOES THE SPANNING-TREE FORMULA START? |
| [mcnew-density-and-dirichlet-grh](Research/mcnew-density-and-dirichlet-grh/README.md) | `mcnew-density-and-dirichlet-grh.zip` | `28bcd392fe` | `mcnew-density-and-dirichlet-grh` | 16 | 15 | 1 | A counterexample to McNew's natural-density conjecture |
| [mcnew_counterexample_and_grh_transfers](Research/mcnew_counterexample_and_grh_transfers/README.md) | `mcnew_counterexample_and_grh_transfers.zip` | `bd8864aa31` | `mcnew_counterexample` | 36 | 35 | 1 | A counterexample to McNew's geometric-progression conjecture |
| [grh_method_transfers](Research/grh_method_transfers/README.md) | `grh_method_transfers.zip` | `de7b92e9c3` | `grh-method-transfers` | 26 | 26 | 0 | Beyond Dirichlet GRH |
| [grh_method_transfers_orthogonal_jets_2026-11-26](Research/grh_method_transfers_orthogonal_jets_2026-11-26/README.md) | `grh_method_transfers_orthogonal_jets_2026-11-26.zip` | `de7b92e9c3` | `grh_transfer_results` | 42 | 27 | 15 | Beyond Dirichlet GRH: orthogonal kernels and sharp p-adic recovery |
| [grh_prime_patterns_and_branch_precision](Research/grh_prime_patterns_and_branch_precision/README.md) | `grh_prime_patterns_and_branch_precision.zip` | `de7b92e9c3` | `grh_prime_patterns_and_branch_precision` | 29 | 28 | 1 | Prime-exponent patterns and p-adic branch precision |
| [grh_spanning_and_s5_2026-11-26](Research/grh_spanning_and_s5_2026-11-26/README.md) | `grh_spanning_and_s5_2026-11-26.zip` | `de7b92e9c3` | `grh_spanning_and_s5_2026-11-26` | 47 | 30 | 17 | Beyond Dirichlet GRH: sharper spanning and an S5 zeta quotient |
| [grh_transfer_extensions_2026-11-26](Research/grh_transfer_extensions_2026-11-26/README.md) | `grh_transfer_extensions_2026-11-26.zip` | `de7b92e9c3` | `grh_transfer_extensions_2026-11-26` | 61 | 35 | 26 | Beyond Dirichlet GRH |
| [grh_transfers_lubin_tate_and_graph_towers](Research/grh_transfers_lubin_tate_and_graph_towers/README.md) | `grh_transfers_lubin_tate_and_graph_towers.zip` | `de7b92e9c3` | `grh_transfers` | 20 | 19 | 1 | Sharp local bounds from methods in the Lean proof of Dirichlet GRH |
| Total | 61 archives | | | 2250 | 1795 | 455 | |
