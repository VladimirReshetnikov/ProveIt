# Research reports

Reports `01`-`09` are nine independent continuations of `../research-plan/turing_degrees_unified.tex`, all attacking
its target **C1** (must every nonuniform coarse-equivalence class contain a representative of
least Turing degree? — the coarse instance of Gerdes's Question 7). They were delivered as zip
archives and are numbered by archive modification time. Each directory holds the report source,
its PDF, and whatever ancillary files shipped with it (finite checks, proof and source audits,
build scripts). The deduplicated synthesis is in
`../research-synthesis/Turing_Degrees_Synthesis.{tex,pdf}`.

Report `10` is a later follow-up on a different topic (see its row). All nine reports `01`-`09` answer C1 negatively, and all nine record that the bare negative answer already
follows from Hirschfeldt–Jockusch–Kuyper–Schupp (2016), Theorems 4.2/4.3. They differ in the
witnesses they construct and in the method:

| Dir | Main file | Method | Subject | Original archive : folder |
|---|---|---|---|---|
| `01` | `paper` | Baire category in the prefix-density metric | Exact partner `D` with `L(P) ∩ L(D) = Core_X` for a prescribed description `P`; robust-radius characterization of the core; self-contained proof that the core of a 1-generic is trivial; countable pairwise family; least-degree criterion | `Turing_Coarse_Counterexample.zip` : `coarse_counterexample_research` |
| `02` | `coarse_minimal_pair` | Finite extension, one-bit reserve | For every oracle `Z` and computable unbounded budget `b`: `A,B ≤ Z''`, individually 1-generic over `Z`, `|(A△B)∩[0,n)| ≤ b(n)`, relative minimal pair; no `Z`-computable null cover of `A△B`; every degree is an unattained spectral infimum | `coarse_minimal_pair_research.zip` : `coarse_minimal_pair` |
| `03` | `coarse_counterexample` | Finite extension, frozen dyadic columns | `R(A)(n) = A(ν₂(n+1))`: spectrum `{b : A ≤ b'}`; pair with `D' ≡ E' ≡ A ⊕ 0'`; countable family; order classification `R(A) ≤_uc R(B) ⇔ A ≤ B ⊕ 0'`; effective-dense spectrum `{b : A ≤ b}` | `turing_degrees_counterexample.zip` : `coarse_counterexample` |
| `04` | `coarse_jump_spectra` | Finite extension, column locks | Same dyadic spectrum; pair and perfect family below `A ⊕ 0'`; no computable null envelope; explicit degree-`0'` representative of the class of `R(0'')`; effective-dense contrast; HJKS route via `γ(R_A) = 1` | `coarse_jump_spectra.zip` : `coarse_jump_spectra` |
| `05` | `coarse_degrees` | Finite extension, computable reservoirs | Explicit c.e. diagonal set with no computable coarse description; general reservoir-fusion theorem (perfect family, two members `≤ 0''`); prescribed unattained infimum via `Block(Z) ⊕ B_Z`; least-representative characterization | `coarse_degree_counterexample.zip` : `coarse_degree_counterexample` |
| `06` | `coarse_minimal_pair_attack` | Finite extension, one-bit trilemma + global variation budget | Perfect family of 1-generics, pairwise minimal pairs, all agreeing off one set `V` with `|V∩[0,n)| ≤ h(n)`; tree `≤ 0''`; budget dichotomy; Hausdorff dimension zero; computable-mask obstruction | `coarse_minimal_pair_attack.zip` : `coarse_minimal_pair_attack` |
| `07` | `sparse_error_minimal_pairs` | Finite extension, one-bit bridge, weighted budget | `A,B ≤ 0''` 1-generic minimal pair with `Σ_{n∈A△B} 1/h(n) ≤ b`, hence `o(h(N))` errors; `A△B` bi-immune; relative version; every degree an unattained infimum | `Sparse_Error_Minimal_Pairs_Research.zip` : `Sparse_Error_Minimal_Pairs` |
| `08` | `coarse_degree_attack` | Baire category; Kuratowski–Ulam + Mycielski | Cone dichotomy and exact partners; cone-avoiding compactness recovered; explicit jump-complete c.e. set with trivial core; Cantor family of pairwise exact partners; principal-core classes `I(A) ⊕ X_A` with no least representative | `coarse_degree_attack.zip` : `coarse_degree_attack` |
| `09` | `coarse_degree_attack` | Baire category; direct ball fusion | Perfect exact-pair family with exact intersections against any countable family of oracles; approximability bounds the core (external-centre proof); many-one complete c.e. example; no countable coinitial family of representative degrees; arbitrary principal cores | `coarse_degree_attack (1).zip` : `coarse_degree_attack` |
| `10` | `coarse_hyperdegrees` | Forcing over L_{ω₁^CK} with budget conditions; elementary | Follow-up to plan Section 12, written in this repository: coarse classes with no least *hyperdegree* (hyperdegree minimal pairs `A ≈ B`, both Cohen generic, `ω₁ = ω₁^CK`); dyadic codes do have least hyperdegrees, so cone-avoiding compactness fails for `≤_h`; Martin's cone theorem fails for the coarse degrees (a `Π¹₁` invariant set splitting every cone) | — (not an archive) |
| `11` | `article` | HJKS compactness + relative generic core; affine sharing | Finite monotone coalition-core profiles; two-share synergy; generic access structures; verifies plan target C4 | `Coarse_Information_Profiles.zip` : `coarse_information_profiles` |
| `12` | `article` | Robust radius (Baire); row-finite normal form; ideal-protected fusion; dyadic insertion + Friedberg inversion | Merged from three manuscripts: every countable Turing ideal is a core (plan target C4, antecedent HJS 2021 Thm 3.11); whole-row spectrum; core-neutral joins; an upper cone in every core fibre; prescribed-jump exact pairs | `ProveIt_Coarse_Ideal_Realization.zip` (base), `ProveIt_Coarse_Core_Realization.zip`, `coarse_core_realization.zip` |
| `13` | `article` | Layered reservoirs; domination | Guarded set `≡_uc R(TOT)`; optimal exact partners with `D' ≡ ∅''` (plan target C6, guarded-set half); exact ideals with joint jump control | `Exact_Ideals_and_Optimal_Jumps.zip` : `exact_ideals_coarse` |
| `14` | `article` | Computable erasures; computable agreement | Plan target C2 answered negatively for 1-generics with computable agreement (all 2-generics, non-high 1-generics, low `Δ⁰₂` examples); the plan's route for high 1-generics stays open | `proveit_effective_dense_research.zip` : `proveit_effective_dense` |

Reports `11`–`14` are the programme's second round: six manuscripts that arrived through
ProveIt's [`docs/incoming`](../../../../../docs/incoming/README.md) as batch 37 and attack
plan targets C2, C4 and C6.  Three of them prove the same C4 spine and are merged into `12`.
These four follow the intake layout — `article.tex`, `article.pdf`, `README.md`, delivered
scripts in `code/` and recorded outputs in `data/` (prefixed by source in `12/`) — and each
README gives the provenance, what is and is not claimed, and the Lean declarations the report
builds on; none of their new theorems is formalized.  The synthesis has not yet been amended
for them.  The housekeeping note below concerns reports `01`–`09` only.

Housekeeping applied on extraction: the single top-level folder of each archive was flattened
into its numbered directory; five byte-identical copies of the research plan
(`input/`, `source/`, `source_material/` → `turing_degrees_unified.tex`) were dropped in favour
of `../research-plan/turing_degrees_unified.tex`, so the hash manifests in `06` and `09` still
list that one now-absent path; the archives themselves were removed after the extracted trees
were verified identical to their contents.
