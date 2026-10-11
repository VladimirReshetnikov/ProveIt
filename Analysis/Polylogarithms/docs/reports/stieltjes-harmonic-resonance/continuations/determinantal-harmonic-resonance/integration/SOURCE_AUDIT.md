# Source audit and limitations

Selected chapter reads were anchored to ProveIt commit
`87c7db629552afbc2e803001526debe3430a31b0`.

Read material:

1. `Analysis/Polylogarithms/docs/manuscript/README.md`.
2. `Analysis/Polylogarithms/docs/manuscript/chapters/07-mixed-dougall-identities.tex`, including its complete ending.
3. The first 240 lines of `Analysis/Polylogarithms/docs/manuscript/chapters/04-cyclotomic-quotients.tex`.
4. The `docs/incoming` directory inventory.
5. The first 180 lines of `docs/incoming/README.md`.
6. Targeted repository-search context for existing harmonic, Stieltjes,
   Gauss, tail, cyclotomic, and Selberg-related developments. Search
   snippets were not treated as full proof audits of other files.

The repository changed during retrieval. Later search results carried
another commit. The source anchor is not a claim that every retrieval
came from an immutable all-repository snapshot.

At inventory time the visible ZIP names were:

- Algebraic_Gauss_Centered_Harmonic_Reflection.zip
- ProveIt_Canonical_Digamma_Fifth_Moment_2026-10-11.zip
- ProveIt_Continuous_Depth_Lerch_2026-10-10.zip
- ProveIt_Higher_Digamma_Powers_2026-10-11.zip
- ProveIt_Mixed_Resolvents_Harmonic_Powers_2026-10-11.zip
- ProveIt_Tilted_Lerch_Binary_Cancellation_2026-10-10.zip

Those binary archives were **not unpacked or analytically audited**.
Their filenames are not mathematical evidence. The article does not
claim to review the whole canonical manuscript or to be disjoint from
all unseen incoming work.

No substantive false theorem was identified in the fully inspected
mixed-Dougall proof. The source's all-order Gauss/Choi correction and
quadratic tail results are acknowledged as prior repository material.
The report does not reclassify them as new discoveries.

The correction developed here concerns a possible transfer error:
identifying a spectral finite part with a hard-cutoff constant without
subtracting the derivative of the residue amplitude. The two-particle
example rigorously refutes that identification. No unseen source is
accused of making it.

Classical external inputs were checked against NIST DLMF sections 5.11,
5.12, 5.15, 15.4, 25.11, and 25.12. Krattenthaler's *Advanced Determinant
Calculus* is cited as method background. Global priority of the precise
new formulations has not been established by an exhaustive literature
audit.

No GitHub content was modified. No proof-assistant formalization is
claimed. S6 and S8 remain unresolved by this delivery.
