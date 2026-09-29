# Source notes and scope

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt  
Inspected snapshot: `ae28ea2db3c01a0b777cffa6295b8fe9c4628f27`  
Inspection date: 29 September 2026.

The live GitHub connector was used to retrieve the following sources:

1. `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/README.md`.
2. `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/Transseries_And_Inversion/README.md`.
3. `Analysis/FabiusFunction/Lean/FabiusFunction/TransseriesWellBased.lean`.

The READMEs describe the consolidated calculus and its combinatorial companion, finite multiexponential inversions, and carefully scoped Lean coverage. The Lean source explicitly bridges Dickson and Neumann results to Mathlib and records order-dual conventions.

The canonical `transseries_and_inversion.tex` was identified but its complete content could not be retrieved through the available GitHub file interface because the file was too large/unsupported. Its returned blob SHA was `90b05af3237dde486c52db0c8ec8a874b09c494f`. No exhaustive reading or nonduplication audit of that volume is claimed. The inspected snapshot is stated as provenance, not as a guarantee that the repository has not subsequently changed.

## Primary external references consulted

- Gerald A. Edgar, *Transseries for beginners*, arXiv:0801.4877. https://arxiv.org/abs/0801.4877
- David Sauzin, *Nonlinear analysis with resurgent functions*, arXiv:1212.4477; Annales scientifiques de l'École normale supérieure 48 (2015), 667–702, DOI 10.24033/asens.2255. https://arxiv.org/abs/1212.4477
- Shingo Kamimoto and David Sauzin, *Nonlinear analysis with endlessly continuable functions*, arXiv:1509.01473. https://arxiv.org/abs/1509.01473
- Matthias Aschenbrenner and Lou van den Dries, *Analytic Hardy fields*, arXiv:2311.07352v3 (2025). https://arxiv.org/abs/2311.07352
- NIST DLMF, §10.32, integral representations, especially 10.32.8 and 10.32.10. https://dlmf.nist.gov/10.32
- NIST DLMF, §10.40, large-argument asymptotic expansions of modified Bessel functions. https://dlmf.nist.gov/10.40

The analytic Hardy-field paper explicitly establishes a realization of the abstract transseries field. The obstruction in this manuscript concerns prescribed actual analytic germs, not that abstract realization theorem. Existing nonlinear resurgence theorems are acknowledged rather than claimed as new. The Bessel identities used here are classical; the paper derives the specialized identity and remainder estimates used in its example.

## Novelty and verification boundaries

The article poses and answers specific research questions. It does not attribute these questions to a published open-problem list, assert exhaustive historical novelty, claim a general transseries conjecture has been settled, or label its proofs as machine-checked. The numerical program is a consistency supplement and uses no interval arithmetic. The general-power saddle expression in the research agenda is explicitly a proposed target rather than a proved complete expansion.
