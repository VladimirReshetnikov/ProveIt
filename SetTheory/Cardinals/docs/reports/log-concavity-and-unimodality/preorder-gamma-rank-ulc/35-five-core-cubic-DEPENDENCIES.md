# Mathematical dependencies and replay boundary

The main paper is a proof with named, previously established mathematical
inputs, followed by an independently checked finite computation. The new replay
does not purport to rerun every earlier theorem's certificate archive. All
bundled source versions and approvals are pinned by `MANIFEST.json`.

## Ordinary reduction inputs

1. **R3: at most three active tail roles.** The arbitrary-relation role-rank
   corollary is `proof-dependencies/role-rank-three-source.md`. Its one-shore
   application here uses `three-active-tail-source.md` and its independent
   approval. The underlying three-core Rayleigh proof uses Wagner's rank-three
   matroid theorem, with the primary reference and exact theorem recorded in
   that approval. A zero-tail physical vertex can retain its head role. The
   general role-rank corollary also uses the approved two-by-two role-cover
   theorem. No assertion about arbitrary physical matching degree three is
   inferred from role-matching rank.
2. **C4: four-core universal sinks at all actual degrees.** Used only after
   showing that both roles of the fifth physical vertex are unusable. Its
   exact earlier article and article approval are copied byte-for-byte under
   `proof-dependencies/companion-statements/`.
3. **Universal first comparison.** The paper gives the weighted arc-disjointness
   Motzkin–Straus proof directly with the actual surviving degree. No finite
   certificate is needed for this step.
4. **D4 and D5.** The all-degree corollary applies the earlier five-core theorems
   only at actual degree four and actual degree five, respectively. Their exact
   articles and approvals are copied under `companion-statements/`. The D4
   appendix is included. These are existing theorem inputs, not a new replay of
   their old finite collections. Their archive identities are in
   `proof-dependencies/companion-archives.json`; copied-member identities are in
   `companion-statement-pins.json`. No old ZIP is needed to run `verify.py`.

## Finite two-sink structural inputs

The independent `replay/structural.py` reconstructs every recorded cover and
matroid application. Its exact input-source manifest is
`replay/dependencies/source-pins.json`.

- Two-tail/two-head role cover: arbitrary loopless directed relations, with
  physical overlap of the two role shores permitted. The exact theorem and
  independent approval are bundled. This contributes 43 selected classes.
- Physical vertex cover of size at most three: the established weighted
  physical-cover theorem, its article, and independent assembly/article
  approvals are bundled. This contributes 21 additional selected classes.
- One-tail/HPP-side: the established signed-monomer stability criterion for
  arbitrary directed relations, including a possible isolated uncovered head.
  The paper's coefficient c_x includes the arc indicator. The independently
  approved exact theorem source and approval are bundled. This contributes
  1,743 further classes. The checker independently rebuilds every side basis
  support and every required simplification, cover, reversal, and bijection.
- Preorders: the earlier independently approved weighted preorder theorem at
  actual degree at most three applies to the reflexive closures of the 139
  listed cores and their two-sink extensions. Fresh checks verify transitivity
  and the seven-physical-vertex bound. Exactly 49 cases are additional to the
  preceding structural branches. The theorem and global/release approvals
  are bundled. Its old certificates are not rerun here.

Some preserved historical notes say “proposed” or describe then-open portions.
The subsequent explicit approval records pin those same theorem bytes; the
current proof uses only their approved statements. In particular, the role-rank
source's historical comment about an unresolved general preorder program does
not alter its proved role-rank corollary or the later completed preorder input.

## Published HPP inputs

Kummer and Sert, *Matroids on Eight Elements with the Half-plane Property and
Related Concepts*, arXiv:2111.09610v4, 24 October 2023, Sections 5–6:
https://arxiv.org/pdf/2111.09610v4

Their published version-2 data:
https://doi.org/10.5281/zenodo.6108027

The exact bundled `n9r4Hpp.txt` has 4,125 proved-positive entries, each with 126
basis indicators. Its SHA-256 is
`a3c7a6eaebe02ef50998710282542be2751b218a6713853cdd2eecadbe1f1f86`.
The authoritative full hash is also checked directly by source-pins.json.
Only the proved-positive list is used; numerical candidates and unresolved
matroids are not admitted as positive evidence.

The 1,743 side applications split into 14 at most-seven-element cases,
201 eight-element nonmiddle-rank cases, and 1,528 explicit matches to the
nine-element positive list (with dualization when necessary). The replay
checks 192,528 basis indicators and 3,216 minors, including 411,648 rank-function
identities. This is a theorem-application and exact databank-membership check;
it does not rediscover the published HPP proofs or rerun published Gram searches.

## New exact algebraic and coverage replay

The full replay reconstructs Boolean endpoint supports by literal full-matching
checks and a separately implemented grouped Hall test. All 9,608 representatives
are compared. It verifies every available rational square certificate, including
149 redundant overlaps, and expands every square completely, even at monomials
absent from the target. The only multiplier is the sum U of five nonnegative
core-tail activities. Degree-eight direct and degree-nine multiplied formats
are checked explicitly. U > 0 permits division; U = 0 forces all positive-rank
coefficients to vanish, as proved in the paper.

All 120 permutations of each five-vertex representative are used to establish
a disjoint, exhaustive partition of the 2^20 labeled directed cores. The selected
ledger is disjoint and complete. No producer module is imported. Arithmetic
uses exact integers and rational numbers; floating-point searches are not proof
premises. Adversarial controls, sink symmetry, ordinary/multiplier parser
regression checks, and symbolic sharpness are freshly run.

This separation of existing ordinary theorem inputs, checked applications,
source identities, and newly replayed finite certificates is intentional.
