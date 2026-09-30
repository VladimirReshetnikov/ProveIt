# A Reflexive Root-Polytope Model for Preorder h-Polynomials

**Simplicial-polytopal realization for all finite preorders; for height two, matching supports, nonreal-root families and crown obstructions; cactus rigidity for matching-support determinants; gamma-positivity for every finite preorder; ultra-log-concave support polynomials, palindromic cores and counting; stability of signed matching supports; the transversal matroid of a preorder; marked-tree stability for arbitrary apex neighbourhoods; and two-flow bijections with full-coordinate sampling of demand vectors and preorder lattice points**

This is a research report in nine parts. Part I is the original report of
20 September 2026. Part II was added on 28 September 2026 in batch 39 of
ProveIt's incoming-report intake, from a later manuscript that addresses the
three questions Part I left open in its Section 10 ("What remains unresolved"):
Conjectures 5.3, 5.2 and 5.1(d) of Athanasiadis–Chapoton. Part III was added
on 29 September 2026 in batch 42, from a further manuscript that answers
Part II's Research question 4, "Beyond the sixth-root cactus matrices". All
three were prepared for Vladimir Reshetnikov and are AI-assisted (the article
credits ChatGPT for Parts I and II; manuscript 05 calls itself AI-assisted).
Part IV was added on 29 September 2026 in batch 44, from two further
manuscripts merged into one addition (batch-44 manuscripts 06, the base, and
01), both prepared with ChatGPT for Vladimir Reshetnikov. Both prove
Conjecture 5.2 (gamma-positivity) for every finite preorder, which answers
Part II's Research question 1, "Extend the matching-support interpretation".
Parts V–VII were added on 29 September 2026 in batch 55, from four
manuscripts (sources 06–09 below; batch-55 manuscripts 01, 02, 04 and 05):
**Part V** merges sources 06 (the base) and 07, two independent proofs that
every bipartite demand-support enumerator and every `h_tau` is
ultra-log-concave, with palindromic cores, probability, approximate counting
and exact-counting hardness; **Part VI** merges source 08 (the base) with
the stability sections of source 09: stability of the signed support
polynomial is block-local, is classified for tree incidence–apex graphs (the
ADE trees), books and multi-theta graphs, and is strictly stronger than
real-rootedness; **Part VII** prints source 09's matroid sections: the
transversal matroid of a preorder determines it up to isomorphism. Sources
06, 07 and 09 credit ChatGPT on their title pages; source 08 calls itself
"AI-assisted" and names no assistant. All four were prepared for Vladimir
Reshetnikov. **Part VIII** was added on 30 September 2026 in batch 63, from
one manuscript (source 10 below; batch-63 manuscript 03), prepared for
Vladimir Reshetnikov with ChatGPT per its title page. It removes Part VI's
terminal convention for one apex over a tree: stability of the incidence
graph of a tree with one apex adjacent to an **arbitrary** set of tree
vertices is classified — a corollary of Part VI's theorems, which the
manuscript also proves directly — and it adds linear-time recognition,
exact polynomial-time counting, optimization and repair of the stable apex
neighbourhoods, a sharp diameter window, and a path-only real-rootedness
theorem for their size-counting polynomial. **Part IX** was added on
30 September 2026 in batch 64, from one manuscript (source 11 below;
batch-64 manuscript 01), prepared for Vladimir Reshetnikov with ChatGPT
per its title page. Two minimum-cost transportation problems with integer
margins and one cycle-generic cost system share an optimal spanning tree,
which gives explicit polynomial-time inverse bijections between the demand
vectors of a bipartite graph with a prescribed support and the supplier
sets matchable to it (the existence of such a correspondence is Oh's).
Composed with the matroid basis walk, this samples **actual lattice points**
of every finite preorder polytope, not only their supports, which answers
Part V's "Sampling boundary" and the bijection part of Research questions 2
and 20; its disjoint union is an elementary proof, without Ehrhart theory,
of the support-counting identity of Parts II, IV and V.

> **Priority.** Part II's headline counterexample to Conjecture 5.3 (real
> roots) is **not new**. The first counterexample known to this report, the
> eight-element height-two poset `P_{Theta_3}`, was posted earlier by
> **Shivam Patel** on MathDB
> (https://mathdb.com/p/374962/real-rootedness-conjecture-for-preorder-polytope-h-polynomia).
> The manuscript found that posting during its own source audit, revised its
> claims, and credits it throughout; it claims only the extension to all
> `Theta_m`. The posting's exact calendar date was not established (the page
> showed a relative date of about one month before 28 September 2026 and
> marked the claim unverified).

> **Priority (Part V).** The unweighted inequality of Part V's main theorem
> is **not new**: it is Theorem A of F. Röhrle and M. Ulirsch, *Logarithmic
> Concavity of Bimatroids*, Ann. Comb. 30 (2026), no. 2, 501–523 (online
> 14 August 2025), doi:10.1007/s00026-025-00780-z, arXiv:2402.15317, applied
> to the bimatroid of a relation (their Example 2.4), with the same
> normalization `binomial(min(m,n), k)`; their Theorem E contains Part V's
> intersection realization. Source 07 and source 09 credit this; source 06
> does not cite Röhrle–Ulirsch, and Part V prints its statement with a merge
> note. What is new in Part V is the composition with the published
> support-counting bridge (hence every demand enumerator and every
> preorder), the weighted two-shore form and the consequences. The mixing
> and FPRAS machinery is Anari–Liu–Oveis Gharan–Vinzant's, the #P input
> Colbourn–Provan–Vertigan's. Three batch-55 manuscripts (sources 06, 07,
> 09) proved the transfer independently on the same day. The Röhrle–Ulirsch
> record was checked in the write phase on 29 September 2026 against the
> arXiv abstract page (v1 23 Feb 2024, v3 6 Aug 2025, "to appear in Annals
> of Combinatorics") and the v3 HTML, which states Theorem A for regular
> `k × k` minors with that normalization and Example 2.4 for relations; the
> journal volume and pages are those recorded by source 07 and the batch-55
> dossier (Crossref), not re-fetched.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 20 Sep 2026 (*A Reflexive Root-Polytope Model for Preorder h-Polynomials*) | (Cardinals-era delivery, not committed as an archive) | (none) | sorted in `f0f61b70d`, in ProveIt since `dc54c3cb3` | Part I: Sections 1–10 (pp. 11–23) and Appendices A–C (pp. 273–275) |
| 02 | batch 39, manuscript 02 (*Height-Two Preorder Polynomials: Matching supports, nonreal-root families, and crown obstructions*, 28 Sep 2026, 26-page PDF as delivered) | `ProveIt_Height_Two_Preorder_Research.zip` (inner `Preorder_Matching_Research/`, main file `article.tex`) | no commit; blob `4c350f5652096b7db91d4a10075eb7905910f647` of Part I's `article.tex` | `e2b1f016a` (prefix `02-height-two-`) | Part II: Sections 11–25 (pp. 24–52) |
| 03 | batch 42, manuscript 05 (*Cactus Rigidity for Matching-Support Determinants: Exact classification, a sharp approximation gap, and stability beyond vertex determinants*, 29 Sep 2026, 24-page US-Letter PDF as delivered) | `ProveIt_Cactus_Rigidity.zip` (inner `ProveIt_Cactus_Rigidity/`, main file `article.tex`) | commit `9754e83603e223811b7515eb892f22c847144593`; blob `8739a224fa8956adab5d8df9f2d5012a6a220959` of this report's `article.tex` | `3609d0473` (prefix `03-cactus-`) | Part III: Sections 26–45 (pp. 53–77) |
| 04 | batch 44, manuscript 01 (*The Gamma-Vector of Every Finite Preorder: Disjoint matching supports, Boolean expansions, and sharp degree laws*, 29 Sep 2026, 22-page A4 PDF as delivered) | `ProveIt_Preorder_Gamma.zip` (inner `ProveIt_Preorder_Gamma/`, main file `article.tex`) | commit `077672c84f743ff5de82ce6becc3ad6b2ff8787a` (this report's `article.tex` there is blob `cd80088f04daeabdf6e320e08bdd1b61a5c9cf4c`, Parts I–III) | `203016015` (prefix `04-gamma-vector-`) | Part IV (merged with 05): Sections 46–65 (pp. 78–118) |
| 05 (base of Part IV) | batch 44, manuscript 06 (*Gamma-Positivity for Every Finite Preorder: Disjoint transport supports, Boolean expansions, block formulas, and a transitivity criterion for palindromicity*, 29 Sep 2026, 22-page A4 PDF as delivered) | `ProveIt_Preorder_Gamma_Research.zip` (inner **also** `ProveIt_Preorder_Gamma/`, main file `article.tex`) | commit `9b24a3a8d545af9624f6ac455f5b548be62818b6` (blob `8739a224fa8956adab5d8df9f2d5012a6a220959`, Parts I–II only) | `203016015` (prefix `05-gamma-positivity-`) | Part IV (merged with 04): Sections 46–65 (pp. 78–118) |
| 06 (base of Part V) | batch 55, manuscript 01 (*Beyond Real-Rootedness: Ultra-Log-Concavity and Approximate Counting for Preorder Support Polynomials*, 29 Sep 2026, 23-page A4 PDF as delivered) | `ProveIt_Lorentzian_Support.zip` (inner same, main file `article.tex`; arrival `08985ea78`, held from batch 54) | commit `e9a57d735db2177a8cca6aaecd95a3d53a0ba678` (this report's `article.tex` there is blob `d52a2633b58e74aa653e967eb56adc1aa41bc8ae`, Parts I–IV) | `26473dfa0` (prefix `06-lorentzian-support-`) | Part V (merged with 07): Sections 66–82 (pp. 119–168) |
| 07 | batch 55, manuscript 02 (*Beyond Real Roots: Ultra-Log-Concavity, Palindromic Cores, and Efficient Counting for Preorder Support Polynomials*, 29 Sep 2026, 23-page A4 PDF as delivered) | `ProveIt_Support_Polynomials_Research.zip` (inner `ProveIt_Support_Polynomials/`, main file `support_polynomials.tex`; arrival `23dd71d2d`) | commit `de2f8fa8c6f0107b1a0f1f77e2e25c343e562180` (article blob `d52a2633…` and README blob `846d9f19fadac9cd933b74370cdb8fafa2211c5d`, Parts I–IV) | `26473dfa0` (prefix `07-support-polynomials-`) | Part V (merged with 06): Sections 66–82 (pp. 119–168) |
| 08 (base of Part VI) | batch 55, manuscript 04 (*An ADE Threshold for Matching-Support Stability: Tree incidence–apex graphs, sharp book transitions, and a classification of bipartite multi-theta graphs*, 29 Sep 2026, 25-page A4 PDF as delivered) | `ProveIt_ADE_Stability.zip` (inner same, main file `article.tex`; arrival `2d4919838`) | commit `e1afd75e35a4de734d5aa47aec5cdb917b82ed3e`; blob `846d9f19…` of this report's **`README.md`** (it read the summary, not the article) | `26473dfa0` (prefix `08-ade-stability-`) | Part VI (with 09's stability sections): Sections 83–99 (pp. 169–202) |
| 09 | batch 55, manuscript 05 (*Preorders as Transversal Matroids: Reconstruction, Ultra-Log-Concavity, and Stability of Matching Supports*, 29 Sep 2026, 24-page A4 PDF as delivered) | `ProveIt_Matroid_Lifts.zip` (inner same, main file `article.tex`; arrival `2d4919838`) | commit `e1afd75e3…` (article blob `d52a2633…`, README blob `846d9f19…`, Parts I–IV) | `26473dfa0` (prefix `09-matroid-lifts-`) | Part VII: Sections 100–115 (pp. 203–219); stability sections in Part VI; coefficient sections credited in Part V |
| 10 | batch 63, manuscript 03 (*Marked-Tree Stability: Complete Apex-Neighborhood Classification, Exact Enumeration, and Optimal Repair*, 30 Sep 2026, 24-page A4 PDF as delivered) | `ProveIt_Marked_Tree_Stability.zip` (inner same, main file `article.tex`; arrival `a4268e78e`) | commit `b57c0b5ff112e1a08af8add12b2d687b8ece91d0` (this report's `article.tex` there is blob `920246d173bfbc708bcfdd6d67e0a6fc358cb3dc`, Parts I–VII) | `62f1ad07c` (prefix `10-marked-trees-`) | Part VIII: Sections 116–131 (pp. 220–246) |
| 11 | batch 64, manuscript 01 (*Two-Flow Bijections for Demand Polytopes: Full-coordinate sampling, exact certificates, restriction laws, and preorder applications*, 30 Sep 2026, 23-page A4 PDF as delivered) | `ProveIt_Two_Flow_Lattice_Sampling.zip` (inner `Two_Flow_Lattice_Sampling/`, main file `article.tex`; arrival `7747fcfdd`) | commit `6d04e1e385f2fe7d1cfbdbd8fd8d4e45bd6b6c72` (this report's `article.tex` there is blob `920246d173bfbc708bcfdd6d67e0a6fc358cb3dc`, Parts I–VII) | `3025c15df` (prefix `11-two-flow-`) | Part IX: Sections 132–151 (pp. 247–273) |

Manuscript 02 names no ProveIt commit. It records the Git blob of the
`article.tex` it consulted; that blob is Part I exactly as printed here
(unchanged from `f0f61b70d` through the placement commit `e2b1f016a`), so
Part II's statements about "the ProveIt report" refer to Part I. The archive
arrived in `74f7f5bdb`. Its manuscript, PDF and delivery README are not
shipped; they survive in the arrival commit. Its `SHA256SUMS.txt` was verified
(13/13) at placement and retired. Part II prints every result, proof, example,
remark, limitation, question and non-claim of the manuscript, plus its
abstract, status box and audit box; its Section k is Section k+11 here.
Section 11.4 of the article lists where the merge had to choose.

Manuscript 05 (batch 42) is pinned to commit `9754e8360` (the batch-41
arrival) and records the blob of this report's `article.tex`; that blob is
Parts I and II exactly as printed here (last changed by the batch-39 write
`6a354f52f`, unchanged at the pin and at the placement commit `3609d0473`), so
its "Section 19", "Section 24" and "Theorem 13.2" are this article's Sections
19 and 24 and Theorem 13.2. The archive arrived in `8315d24e3`. Its
manuscript, PDF and delivery README are not shipped; they survive in the
arrival commit. Its `SHA256SUMS.txt` was verified (10/10) at placement and
retired. Part III prints every result, proof, remark, limitation, question
and non-claim of the manuscript, plus its abstract and status note; its
Section k is Section k+26 here, its Appendices A and B are Sections 44 and 45,
and its nine research questions are Research questions 11–19. Section 26.4
of the article lists where the merge had to choose.

Batch 44's manuscripts 06 and 01 arrived in `ae28ea2db` and were placed in
`203016015`. Both archives wrap an inner directory of the same name,
`ProveIt_Preorder_Gamma/`, but they are different packages (no file
coincides). They prove the same main theorem by the same route and are
printed as **one** Part IV, with **06 as the base**: its transitivity theorem
covers every reflexive relation, not only preorders, and has a proof
independent of the imported counting identity. The base took the later local
number (`05-`), because the prefixes follow arrival order. Manuscript 06 is
pinned to `9b24a3a8d`, where this article was Parts I and II exactly as
printed (it did not read Part III); manuscript 01 is pinned to `077672c84`,
where it was Parts I–III exactly as printed. Their manuscripts, PDFs and
delivery READMEs are not shipped and survive in the arrival commit;
manuscript 01's `SHA256SUMS` was verified (7/7) at placement and retired, and
manuscript 06 shipped none. Part IV prints every result, proof, example,
remark, limitation, question and non-claim of both, plus both abstracts and
status boxes and manuscript 01's "shortest proof audit" box: a result proved
in both is printed once with both sources named, and genuinely different
proofs are kept as marked second routes (manuscript 01's path-decomposition
proof of overlap cancellation, its profile form of the block formula, its
initial-segment chain count and reflection proof of the Narayana formula).
The shared demand/support counting lemma is Part II's Lemma 14.1, which both
manuscripts reprove by the same reduction; it is printed once, in Part II.
Material only manuscript 01 contains (Boolean orbits of commuting toggles,
multivariate complement-duality, the second gamma coefficient, the leading
Taylor coefficient at −1, the induced-deck identity with odd-cardinality
reconstruction, an Ehrhart reinterpretation, three false variants, a
dependency graph, a compact proof certificate) is printed under its own
headings. The twenty research questions become seventeen (three pairs ask
the same question), numbered 20–36. Section 46.4 of the article lists where
the merge had to choose. Manuscript 06's own numbering, used in its shipped
notes, maps as follows: Theorem 2.2 → 48.2, Theorem 2.3 → 48.3, Lemma 3.1 →
49.1, Lemma 4.1 → 50.1, Lemma 6.1 → 53.1.

Batch 55's four manuscripts arrived in three commits: source 06 in
`08985ea78` (it was held over from batch 54 to be merged with source 07),
source 07 in `23dd71d2d`, sources 08 and 09 (with a manuscript for another
report) in `2d4919838`. All were placed in `26473dfa0`. This report did not
change from the earliest pin (`e9a57d735`) to the placement, so every
statement of the four about "the repository" or "the report" concerns
Parts I–IV exactly as printed; source 08 read only this README (blob
`846d9f19`), the other three read the article (blob `d52a2633`). None saw
another. The manuscripts, PDFs and delivery READMEs are not shipped; they
survive in the arrival commits. Checksum lists verified at placement and
retired: source 06 `SHA256SUMS.txt` 13/13, source 08 7/7, source 09 8/8;
source 07 shipped none.

- **Part V** merges 06 (base: held first, owner of prefix `06-`, and it
  states the corollaries for this report's questions and has the larger
  probabilistic and algorithmic layer) with 07 (palindromic cores, the
  intersection realization, convex order and the equality classification,
  exact-counting hardness, several examples, and the correct attribution).
  A result proved in both is printed once with both sources named; the
  genuinely different proofs are kept as marked second routes (07's import
  of the bridge through Dai et al. and Davis–Kohl with subset inversion;
  07's explicit factorial calculation of the Lorentzian criterion; 06's
  logistic ODE proof of the binomial bound beside 07's convex-order proof;
  07's Hessian variance bound; 07's explicit error allocation). Their
  eighteen research questions become seven numbered ones, 37–43 (three
  pairs merged), plus seven printed unnumbered next to the earlier question
  they repeat, or with the Part V theorem that answers them (Section 80.1).
  Section 66.4 lists where the merge had to choose.
- **Part VI** is source 08 in its own order, with source 09's Sections
  11–14.3 merged in: 09's bridge and induced-subgraph lemma after 08's
  bridge (Section 85.2), 09's vertex-sum theorem **in place of** 08's
  one-vertex gluing proposition (same formula and argument; 09's form covers
  all simple graphs and adds block localization; Section 93), 09's stable
  blocks and `K_{3,3} ∨ C_6` example as Section 94, and 09's Sturm chain and
  Rayleigh certificate beside 08's `ϑ(3,3,3)` discriminant (Section 92).
  08's nine questions and 09's two stability questions become Research
  questions 44–53 (one pair merged). Section 83.4 lists the choices.
- **Part VII** is source 09's Sections 1–2, 5–10, 14.4, 16–18, the first
  paragraph of its conclusion and its Appendices A–B, in its order. Its
  Sections 3–4 and the general part of 15 (ultra-log-concavity; binomial
  convex domination) are the same theorems as Part V's and are credited
  there, not reprinted (Section 100.4). Its Questions 5, 6, 8, 10 are
  Research questions 54–57; 1–2 are in Part VI; 3, 4, 7, 9 are printed
  unnumbered next to the earlier questions they repeat.

Batch 63's manuscript 03 (source 10) arrived in `a4268e78e` and was placed in
`62f1ad07c`, together with manuscripts for two other reports. Its pin
`b57c0b5ff` records the blob `920246d1…` of this report's `article.tex`,
which is Parts I–VII exactly as printed before Part VIII (last changed by
`8c6517c0f`, unchanged at the pin and at the placement), so its "Part VI"
and its line ranges refer to that text. Its manuscript, PDF and delivery
README are not shipped; they survive in the arrival commit. Its
`SHA256SUMS.txt` was verified (10/10) at placement and retired.

- **Part VIII** is source 10 in its own order, behind a merge section
  (Section 116). Source 10's Section k is Section k + 116 here (its
  Appendices A–B are Sections 130–131), and statement and equation numbers
  follow the section (Theorem 2.2 → 118.2); its Tables 1–2 and Figure 1
  are Tables 14–15 and Figure 4, and its eight questions are Research questions
  58–65. Its classification (Theorem 118.2) is printed with a **first proof
  assembled for the merge** from Part VI's Theorems 89.1, 93.2 and 84.3(ii)
  — source 10 itself calls the classification "a synthesis and extension of
  specific existing results" (Section 130) — and with its own direct proof
  as the second. Its four bridge lemmas, path-shortening lemma, resolvent
  lemma and ADE proposition duplicate Part VI (Lemmas 85.1, 85.4–85.6,
  89.2, 87.1, Proposition 85.2, Theorem 88.1): their statements and labels
  are kept, their proofs are replaced by pointers; its coefficient count for
  the `ϑ(3,3,3)` quartic is kept as a second route. Section 116.4 lists
  every choice.

Batch 64's manuscript 01 (source 11) arrived in `7747fcfdd` and was placed
in `3025c15df`, together with manuscripts for four other reports and one
Fabius-tree arrival. Its pin `6d04e1e38` records the same blob `920246d1…`
of this report's `article.tex` as source 10's: Parts I–VII exactly as
printed, before Part VIII was written, so its "Part V" and its line
interval 9510–9555 (the "Sampling boundary" box) refer to that text; the
box is unchanged and is now in Section 75. Its manuscript, PDF and
delivery README are not shipped; they survive in the arrival commit. It
shipped no checksum list.

- **Part IX** is source 11 in its own order, behind a merge section
  (Section 132). Source 11's Section k is Section k + 132 here (its
  Appendices A–B are Sections 150–151), and statement and equation numbers
  follow the section (Theorem 3.2 → 135.2); its two tables are Tables 17
  (claim ledger) and 18 (verification), its figure is Figure 5, and its
  eight questions are Research questions 66–73. Its first subsection, "A
  precise gap in the repository", which cited the pinned blob's line
  numbers, was rewritten as a pointer to Part V (Section 133.1). Its
  preorder reduction (Proposition 146.1) is Part V's Lemma 71.1 and keeps
  its statement and label with the proof replaced by a pointer; its lifted
  matroid, conditioning minor, Hall lemma, basis walk and cloning keep
  their short text with merge notes naming Part V's statements. Its
  counting identity (Corollary 139.2) is kept as a **second route**: the
  report's only proof of the support-counting identity of Parts II, IV and
  V that uses no Ehrhart theory. Section 132.4 lists every choice.

Section numbers of the sources that their shipped notes use:
source 09's `09-matroid-lifts-CLAIMS_AND_SOURCES.md` cites its Sections 4
(→ Part V, not reprinted: Corollary 67.2 and Proposition 71.5), 5 → 103,
6 → 104, 7 → 105, 8 → 106, 9 → 107, 10 → 108, 11 → 85.2, 12 → 93 (its
Lemma 12.1 → 93.1, Theorem 12.2 → 93.2, Corollary 12.3 → 93.3) and
13 → 94. Source 08's Sections 1–10 are Sections 84–93 here, and its
Sections 11–13 and Appendices A–B are Sections 95–99; statement numbers
follow the section (Theorem 1.1 → 84.1, Theorem 7.2 → 90.2) except in
Sections 85 and 93, where source 09's statements were inserted (source 08's
Proposition 10.1, the gluing, is Theorem 93.2). Source 07's
`PROOF_STATUS.md` uses no numbers. Source 11's `11-two-flow-PROOF_STATUS.md`
uses the delivered numbering: Theorem 3.2 → 135.2, Lemmas 4.1–4.2 →
136.1–136.2, Sections 5–7 → 137–139, Theorem 8.1 → 140.1, Corollaries
8.2–8.3 → 140.2–140.3, Propositions 9.1–9.2 → 141.1–141.2, Theorem 10.1 →
142.1, Propositions 12.1–12.2 → 144.1–144.2, Theorems 13.1–13.2 →
145.1–145.2, Proposition 14.1 and Corollary 14.2 → 146.1–146.2,
Proposition A.1 → 150.1.

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and no source claims otherwise. The
programs check finite instances; they do not prove the all-`n`, all-`m`,
all-`r` or all-graph statements. (Part IV: the programs check all labeled
preorders through `n = 5`; the all-preorder theorem rests on the written
proof and on two imported published root-polytope theorems. Parts V–VII:
the four programs check finite families, listed under "Data conventions";
the general theorems rest on the written proofs and on imported published
theorems — the support-counting bridge, the Lorentzian theory of matroid
bases, Röhrle–Ulirsch's Theorem A, the basis-walk mixing theorem, the
#P-completeness of transversal-base counting, the Ingleton–Piff
characterization of gammoids — which are cited, not reproved. Part VIII:
source 10's program checks every marking of every tree with at most nine
vertices; the general theorems rest on the written proofs, on Part VI's
theorems and on standard stable-polynomial closure properties and Perron
positivity. Part IX: source 11's program checks every bipartite graph with
both shores of size at most three and every 4 × 3 graph, all 390 labeled
preorders on at most four elements, 250 seeded random cases and two exact
Markov chains; the general theorems rest on the written proofs, and the
sampler theorem also on the imported Anari–Liu–Oveis Gharan–Vinzant mixing
theorem.)

## Results

For a finite preorder `tau` on `[n]`, `h_tau(t)` counts the integer points of
its preorder polytope by the number of nonzero coordinates (the support
polynomial of Athanasiadis–Chapoton, arXiv:2605.26916v1, Section 5).

**Part I** (unchanged apart from dated pointers) gives a proposed general proof
of Conjecture 5.1(c), hence (a) and (b):

1. The explicit n-dimensional lattice polytope
   `C_tau = conv({±e_i} ∪ {e_i − e_j : j ≤_tau i, i ≠ j})` is reflexive and
   `h*(C_tau, t) = h_tau(t)` (Theorem 1.1), by a unique integer-fiber
   decomposition of the augmented bipartite root polytope `B_tau`
   (Theorem 4.1, Corollary 4.2).
2. Every pulling triangulation of `∂C_tau` is the boundary of an
   n-dimensional simplicial polytope `S_tau` with `h(S_tau, t) = h_tau(t)`;
   hence palindromicity, unimodality and the full g-theorem conditions.
3. A second route through a diagonal special simplex and an exact interior
   translation of `B_tau` (Section 6), an exact gauge (4.4), Ehrhart and volume
   formulas (Section 7), and a hypertree reconstruction of the known root
   identity (Appendix A).

The higher-dimensional identity `h*(B_tau) = h_tau` and the duality
`h_(tau*) = h_tau` are prior results of Dai, Hou, Liu, Thawinrak and Wang
(arXiv:2608.16037v2); Part I credits them and does not claim them.

**Part II** (manuscript 02; unchanged apart from dated pointers to Part III)
works with posets of height at most two, written `P_G` for a bipartite
comparability graph `G` on `n` vertices. It proves:

1. **Matching-support formula** (Theorem 13.2): `h_{P_G}(t) = (1+t)^n p_G(t/(1+t)^2)`,
   where `p_G` counts perfectly matchable *vertex sets* (not matchings). Hence
   **gamma-positivity (Conjecture 5.2) for all posets of height ≤ 2**, with
   `gamma_k = |M_k(G)|`; real-rootedness of `h_{P_G}` is equivalent to that of
   `p_G` (Proposition 15.1).
2. **The Theta_m family** (Theorem 13.3, Section 16): a closed form for
   `p_{Theta_m}` and an exact real-root count — for `m ≥ 3`, `h_{P_{Theta_m}}`
   has exactly 2 real roots (m even) or 4 (m odd), so the nonreal proportion
   tends to one, at treewidth two. `m = 3` is **Patel's** eight-element
   counterexample (1,281 lattice points), checked here, not claimed.
3. **A 17-element counterexample** (Theorem 13.4, Section 17), transferred from
   the classical Stembridge–Ohsugi–Tsuchiya polynomial, with an exact Laguerre
   certificate `-5680 < 0` and a direct count of all 8,408,566 lattice points;
   neither first nor minimal.
4. **A height-two orthant proof** that `h*(C_{P_G}) = h_{P_G}` and that the
   one-sided model `D_G` is reflexive (Theorem 18.2) — a second route to
   Part I's Corollary 4.2 in height two.
5. **Bipartite cacti** (Section 19): a sixth-root-of-unity matrix `K` with
   `p_G(u) = det(I + u K K*)`, a real-stable multivariate refinement, weighted
   real-rootedness and deletion interlacing. Univariate real-rootedness is
   Ohsugi–Tsuchiya's (Theorem 7.2 of arXiv:2008.08621) and is credited.
6. **Crowns** (Sections 20–21): closed forms with all roots simple and
   negative; yet an induced crown on `2r ≥ 6` elements forces a minimal
   nonface of size `r` in **every lattice triangulation** of `C_tau` or of its
   boundary, and an indispensable toric binomial of degree `r`.

**Part III** (manuscript 05) asks when a bipartite graph `G` carries a
*faithful* matrix: unit complex entries on the edges, zeros elsewhere, and
every square minor of squared modulus exactly 1 or 0 according as its vertex
support is perfectly matchable or not (Part II's cactus matrix is one). It
proves:

1. **Classification** (Theorem 29.1): `G` has a faithful matrix iff it is a
   **cactus**; equivalently one with sixth-root entries; equivalently the
   signed support polynomial `Phi_G` equals `det(diag(z) − H)` for some
   Hermitian vertex-indexed `H`; equivalently `G` carries a support-exact
   matrix over `F_3` (no structurally nonzero minor vanishes). Over `F_2` the
   class is the forests (Theorem 35.1); real faithful matrices exist only on
   forests (Corollary 30.4); `K_{2,m}` is support-exact over `F_q` iff
   `m ≤ q − 1` (Proposition 35.3). The proof reduces an induced theta
   (Lemma 31.1) by a support-preserving Schur compression (Lemma 32.1) to
   three cores, `K_{2,3}`, `theta(1,3,3)` and `theta(3,3,3)` (= Part II's
   `Theta_3`).
2. **Rigidity** (Theorem 30.3): on a cactus of cycle rank `beta`, every
   faithful matrix is gauge-equivalent to exactly one of `2^beta` sixth-root
   matrices (both `(-1)^r zeta` and `(-1)^r zeta-bar` are allowed on each
   cycle); over `F_3` the gauge class is unique.
3. **Sharp gap** (Theorem 36.3): on every noncactus, every unit-phase matrix
   has a matchable minor whose squared modulus is off by at least
   `(sqrt(17) − 3)/2 = 0.5615…`, attained on `K_{2,3}`; the cores
   `theta(1,3,3)` and `theta(3,3,3)` are off by at least 3/5 (Lemmas 36.5,
   36.6); `d(theta(1,3,3)) = (sqrt(5) − 1)/2` exactly (Proposition 44.1).
4. **Strictly stronger than stability** (Theorem 37.1, Corollary 37.4):
   `Phi_{K_{2,3}} = abxyz − (a+b)(xy+xz+yz) + (x+y+z)` is real stable (three
   exact sums-of-squares Rayleigh certificates, via Brändén's Theorem 5.6),
   and so is `Phi_G` for every graph obtained from `K_{2,3}` by attaching
   trees — infinitely many connected noncacti with real-rooted `p_G` and no
   faithful matrix.
5. **No bounded-order test** (Theorem 38.1): for every `r` there is a
   connected subcubic treewidth-two noncactus (an odd theta of girth > 2r) on
   which every phase matrix passes all minor tests of order ≤ r.

**Part IV** (manuscripts 06 and 01 of batch 44, merged) works with an
arbitrary finite preorder `tau` on `n` elements: no height bound, and
equivalence classes of any size. Call an ordered pair `(U,V)` of disjoint
`k`-sets a *transport pair* if some bijection `f: U → V` has
`u ≤_tau f(u)`; a pair is counted once however many such bijections exist.
It proves:

1. **Gamma-positivity for every finite preorder** (Theorem 48.2, both
   manuscripts): `h_tau(t) = Σ_k gamma_k t^k (1+t)^(n−2k)` with
   `gamma_k = |T_k(tau)|`, the number of transport pairs of size `k`. So
   **Conjecture 5.2 of Athanasiadis–Chapoton holds in general.** A
   multivariate form counts lattice points by their exact support. The proof
   partitions lattice points by their *whole* zero set (Lemma 50.1). Each
   support fibre is then a bipartite demand set, which Part II's counting
   Lemma 14.1 turns into Boolean intervals. Part II's height-two theorem is
   the special case (Section 55.3). Strict unimodality and palindromicity
   follow without Part I's geometry (Corollary 50.3).
2. **Transitivity criterion** (Theorem 48.3, manuscript 06). For every
   reflexive relation `R`, the doubled matching-support polynomial `p_R` has
   coefficients `|R|` in degree 1 and `|closure(R)|` in degree `n−1`.
   Palindromic, gamma-positive, overlap-cancelling and transitive are all
   equivalent. This classifies the balanced bipartite graphs with a perfect
   matching whose matchable-set polynomial is palindromic (Corollary 53.2).
   It also explains Part I's nonpalindromic example (Section 8.5,
   `(1,5,6,1) = (1,|R|,|closure(R)|,1)`).
3. **Structure** (both manuscripts unless marked):
   - positive block formulas on the quotient poset, in signed form
     (Theorem 54.1, 06) and in profile form (Theorem 54.3, 01);
   - gamma-monotonicity under relation extension, strict in `gamma_1`
     (Theorem 55.1);
   - multivariate complement-duality (Theorem 55.2, 01);
   - sharp bounds, attained by the universal equivalence and by chains
     (Theorem 55.6);
   - `deg Gamma_tau = nu(Comp(tau))`, the matching number of the
     *undirected* comparability graph, and the multiplicity of `−1` as a
     root of `h_tau` is exactly `n − 2 nu` (Theorem 56.1), with the leading
     Taylor coefficient there (Corollary 56.2, 01);
   - commuting Boolean toggles on a support-pair model (Theorem 52.1, 01),
     *not* on lattice points;
   - the induced-deck identity `(1−t) Σ_v h_(tau−v) = n h_tau − 2t h_tau'`,
     which reconstructs `h_tau` from its deck for odd `n` (Theorem 57.1,
     Corollary 57.2, 01);
   - a centered-binomial mixture law for the support size, with exact
     variance and a Hoeffding-type tail bound (Theorem 58.1, 06);
   - the octopus formula of Athanasiadis–Xiao–Yan and Menon, recovered and
     credited (Section 55, 01).

**Part V** (sources 06 and 07, merged) works with a finite bipartite graph
`H = (X ⊔ Y, E)` and its demand vectors `c ∈ Z_{≥0}^Y` with
`c(S) ≤ |N_H(S)|`, counted by support; by the counting bridge the support
enumerator is `p_H`, which counts matchable support pairs. It proves:

1. **Ultra-log-concavity** (Theorems 67.1 and 70.1, both sources; source
   09 is a third proof): `a_k / binomial(min(m,n), k)` is log-concave with no
   internal zeros, positive exactly for `0 ≤ k ≤ nu(H)`, also with positive
   vertex weights on both shores (Theorem 67.3 states the order on the
   nonisolated core). The unweighted inequality is **Röhrle–Ulirsch's
   Theorem A** (see the priority box). Hence **every `h_tau` is
   ultra-log-concave of order `n`** (Corollary 67.2), for every positive
   integral dilation too (Corollary 71.3), and the **unimodality part of
   Problem 5.3 of Dai et al. holds for every bipartite graph** (Corollary
   70.2). The multivariate support polynomial is completely log-concave
   (Theorem 69.3); integer capacities are covered (Corollary 70.5).
2. **Height-two gamma vectors** (Corollary 71.6, 06): since
   `Gamma_{P_H} = p_H`, every height-two `gamma_k / binomial(min(m,n), k)` is
   log-concave.
3. **Palindromic cores** (Theorem 67.4, Section 72, 07): `p_H` is
   palindromic in its actual degree iff, after deleting isolated vertices,
   the graph is balanced, has a perfect matching, and the matched relation is
   a preorder; iff it is gamma-positive. Recognition takes a matching and a
   transitive closure. The top coefficient factors as `|L|·|R| ≥
   (a−r+1)(b−r+1)` (Proposition 72.1). This **answers Research question 23**
   and extends Part IV's Corollary 53.2.
4. **Intersection realization** (Proposition 73.1, 07): `p_H` is a
   normalized mixed-volume polynomial (the realizable case of
   Röhrle–Ulirsch's Theorem E).
5. **Probability** (Section 74): conditional complete log-concavity
   (Proposition 74.1, 06), a covariance-matrix bound `Cov(I) ⪯ diag(p) −
   pp^T/m` (Theorem 74.3, 06), same-mean binomial **convex-order**
   domination under every positive fugacity (Lemma 74.4, Theorem 74.5, 07;
   06's Theorem 74.6 by a second route), and equality in the variance bound
   **exactly for disjoint equal-strength stars** (Theorem 74.8, 07); for
   preorders exactly for antichains (Corollary 74.9).
6. **Approximate counting** (Section 75): an explicit matching oracle and
   basis walk (Theorem 75.1, 07) give FPRASes for partition functions,
   `|Q_tau ∩ Z^n|` (Theorem 75.2, both), a specified support fibre
   (Corollary 75.3, 06) and **every single coefficient** `[t^k] h_tau` and
   height-two `gamma_k` (Theorem 75.5, 06, by log-concave tilting).
7. **Exact counting is hard** (Section 76, 07): `|D_H|` and `h_tau(1)` are
   #P-complete under Turing reductions, already for posets of height two
   (Theorems 76.2–76.3); as a merge consequence, so is a specified
   `gamma_k` (Corollary 76.4).

**Part VI** (source 08, with source 09's stability sections) studies real
stability of Part III's signed support polynomial `Phi_G`. It proves:

1. **ADE criterion** (Theorem 84.1, 08): for a tree `T`, the incidence–apex
   graph `A(T)` has stable `Phi` iff `I − A_T/2 ⪰ 0` iff `rho(A_T) ≤ 2`,
   i.e. for the finite and affine ADE trees (the list is classical,
   Theorem 88.1), via the identity `F = det L + s·tr(adj(L) C_T)`
   (Theorem 86.3) and explicit rational Rayleigh certificates
   (Theorem 87.2); also after terminal subdivision (Theorem 89.1).
2. **Books** (Theorems 84.2, 90.2, 08): `Phi_{B_m}` is stable iff `m ≤ 4`,
   but `p_{B_m}` is real-rooted for every `m`; at `m = 5` the uniform basis
   measure has a positively correlated pair (covariance 1/576). So
   **stability of `Phi_G` is strictly stronger than real-rootedness of
   `p_G`**, which Part III left open; `ϑ(3,3,5)` is a second witness
   (equation 92.5). In Part II's labelling `B_m` is `Theta_m` plus one edge
   and `p_{B_m} = p_{Theta_m} + u` (merge note, Section 90).
3. **Multi-theta graphs** (Theorem 84.3, 08): all simple bipartite
   multi-theta graphs are classified (all-even: stable; all-odd without a
   direct edge: stable iff two paths; direct edge plus `m` odd paths: iff
   `m ≤ 4`), with an expected-determinant proof for even paths
   (Theorems 91.2, 91.4).
4. **Block locality** (Lemma 93.1, Theorem 93.2, Corollary 93.3, 09; the
   bipartite case also 08): `Phi` of a one-vertex sum is stable iff both
   pieces are, so stability is decided on 2-connected blocks. **Every
   `K_{l,r}` is a stable block** (Theorem 94.1, 09).
5. **Infinitely many induced-minimal obstructions** (merge observation,
   Section 92.6): every `ϑ(a,b,c)` with `a,b,c` odd ≥ 3 is unstable while
   all its proper induced subgraphs are cacti, so there is no finite
   obstruction set even for treewidth two and maximum degree three.

**Part VII** (source 09) studies the transversal matroid `M_tau` on two
copies `E^+ ⊔ E^-` of the ground set of a preorder (bases `I^+ ⊔ (E∖J)^-`
for matchable `(I,J)`; the dual convention to Parts V–VI's `𝖬_H`). It
proves:

1. for a reflexive relation, transitivity iff the paired copies are clones
   (Theorem 103.2; Part IV's Proposition 51.4 in matroid form);
2. a symmetric presentation and the upset rank formula (Theorem 104.1);
3. the clone classes are the doubled equivalence classes (Theorem 105.1),
   **`M_tau` determines `tau` up to isomorphism** (Theorem 105.2), and
   `|Aut M_tau| = |Aut(tau̅, m)| · Π_C (2 m_C)!` (Corollary 105.3);
4. `M_tau^* = M_{tau^op}` and induced restrictions are minors
   (Theorem 106.1);
5. a multivariate orbit polynomial and a transport-weighted palindromic,
   gamma-positive, ultra-log-concave `h_{tau,w}` (Theorems 107.1–107.2; the
   unweighted orbit statement is Part IV's Theorem 52.1);
6. every transversal matroid is an explicit minor of a height-two preorder
   matroid, so these generate exactly the finite gammoids under minors
   (Theorem 108.1, Corollary 108.2, with Ingleton–Piff's characterization).

**Part VIII** (source 10) studies the incidence graph `A(T;S)` of a tree `T`
with one apex adjacent exactly to a set `S` of tree vertices (a *marking*;
Part VI's `A(T)` is `S = V(T)`). With `K` the smallest subtree containing
`S` and `H(T,S)` the tree on `S` obtained by suppressing the unmarked
degree-two vertices of `K`, it proves:

1. **Classification** (Theorem 118.2): `Phi_{A(T;S)}` is real stable iff
   `S` is empty, or every vertex of degree ≥ 3 in `K` is marked
   (*branch-complete*) and `I − A_H/2 ⪰ 0`, i.e. `H(T,S)` is a finite or
   affine ADE tree. This **follows from Part VI** (Theorems 89.1, 93.2 and
   84.3(ii); first proof); source 10's direct proof is new: an unmarked hull
   branch forces an induced odd multi-theta graph (Theorem 120.2); a real
   symmetric matrix supported on `S` with connected-set energies
   `1_W^T C 1_W = [W ∩ S ≠ ∅]` exists iff `S` is branch-complete, and is
   then unique (Theorem 121.1, generalizing Proposition 86.2);
   `F_{T,S} = det L + s·tr(adj(L) C)` holds on the host with unmarked
   subdivisions and fringe (Theorem 121.3, generalizing Theorem 86.3); and
   indefiniteness gives a rational negative Rayleigh certificate on the
   host (Theorem 122.2, generalizing Theorem 87.2).
2. **Recognition and geometry** (Section 123): stability is decided in
   `O(n)` time (Theorem 123.1); a stable hull has at most four leaves
   (Corollary 123.2); the largest stable marking `alpha_st(T)` satisfies
   `diam(T) + 1 ≤ alpha_st(T) ≤ min(n, diam(T) + 3)`, all three offsets
   attained (Theorem 123.3); stable markings are neither up- nor
   down-closed, and all markings are stable iff `T` is a path
   (Proposition 123.4).
3. **Enumeration, optimization and repair** (Sections 124–125): an endpoint
   formula for the multivariate enumerator of stable markings over hulls
   with two, three and four leaves and six exceptional arm triples
   (Theorem 124.1); all coefficients of the weighted size enumerator in
   `O(n^5)` exact arithmetic operations (Theorem 124.2) and the exact
   probability that an independent random marking is stable
   (equation 124.7); a maximum-weight stable marking for arbitrary signed
   rational scores in `O(n^5)` (Theorem 125.1) and minimum-cost apex-edge
   repair (Corollary 125.2).
4. **The size enumerator of stable markings** (Section 126): path and star
   formulas (Proposition 126.1); `Z_T(t)` is real-rooted iff the
   multivariate enumerator is stable iff `T` is a path (Theorem 126.3, by a
   two-coefficient rigidity lemma, Lemma 126.2); for stars log-concavity
   fails from `m = 4` and unimodality from `m = 6` (equations 126.5–126.7).

**Part IX** (source 11) works with a bipartite graph `H = (X ⊔ Y, E)`, its
demand set `𝒟_H = {c ∈ Z_{≥0}^Y : c(A) ≤ |N_H(A)| for all A ⊆ Y}` (Part V's)
and the matchable support pairs `(I, J)` (Part V's `𝓜(H)`). With a dummy
receiver `0` joined to every supplier and cycle-generic edge costs (for
instance `2^i` on the `i`-th augmented edge), it proves:

1. **Two-flow correspondence** (Theorem 135.2): for `r = |J| > 0`, the
   minimum-cost flow with margins `m·1_{x∈I} + 1` on suppliers and `m` on
   `{0} ∪ J` and the one with margins `r + 1` on suppliers,
   `(r+1)c_0 + r` at the dummy and `(r+1)c_y − 1` at `y ∈ J` are unique,
   integral and supported on **the same spanning tree**; the forward map
   `c_y = 1 + #(unselected supplier leaves at y)` and the inverse map
   `I = {suppliers of degree 2}` are inverse bijections between the supplier
   sets matchable to `J` and the demand vectors with support `J`. Proofs use
   Hall's theorem, finite forests and strict tree potentials only (Sections
   136–139), so the **support-counting identity** (Corollary 139.2 = Part V's
   Proposition 68.3, Part IV's Proposition 49.3, Part II's Lemma 14.1)
   gets an elementary proof without Ehrhart theory — a second route, not a
   new identity.
2. **Core factorization and restriction laws** (Section 140): a flow of
   total value `r(r+1)` on the selected suppliers fixes prices, after which
   every other supplier independently attaches to its unique cheapest
   reduced-cost receiver or the dummy (Theorem 140.1); deleting or adding
   suppliers outside `I` changes the vector by one unit each, monotonically
   and commutatively (Corollary 140.2), and receivers outside `J` do not
   matter (Corollary 140.3).
3. **Perturbations and certificates** (Sections 141–143): explicit open
   ranges of margins and costs, dependence only on cycle-sign chambers,
   gauge invariance (Propositions 141.1–141.2); polynomial bit complexity
   and an `O(m+r)`-entry exact primal–dual certificate whose checker proves
   unique optimality (Theorem 142.1); a worked certificate (Section 143).
4. **Obstructions** (Section 144): no deterministic support-preserving
   bijection is equivariant under all automorphisms (`K_{2,1}`,
   Proposition 144.1); no bijection moves coordinates by a bounded amount
   per basis exchange (`K_{m,1}`, Proposition 144.2).
5. **Full-coordinate sampling** (Section 145): the bijection pushes the
   weighted basis law of Part V's matroid `𝖬_H` to the support-weighted law
   on `𝒟_H` and preserves total-variation distance **exactly**
   (Theorem 145.1); with the imported basis-walk mixing theorem this is a
   polynomial-time almost-uniform sampler of actual demand vectors
   (Theorem 145.2), also conditioned on prescribed zero and nonzero
   coordinates.
6. **Preorders** (Section 146): `𝒟_{H_tau} = 𝒬_tau ∩ Z^V` (Proposition
   146.1, Part V's Lemma 71.1), hence an almost-uniform sampler of the actual
   lattice points of every finite preorder polytope (Corollary 146.2), and
   of its integral dilations by cloning (pseudopolynomially).
7. **Inverse prices** (Section 150): the inverse tree's receiver potentials
   are the unique maximizer of an explicit concave function, at which
   exactly the selected suppliers have two minimizing receivers
   (Proposition 150.1).

**What Parts II–IX do to the open questions** (Sections 11.3 and 26.3;
Part II's dated pointers are in the abstract, the scope box, Sections 8 and
10 and Appendix C; Part III's in the title block, the abstract, the
reading-route box, Section 19 and Research questions 3 and 4 of Section 24;
Part IV's answers are in Section 46.3, and its dated pointers, marked
"Added 29 September 2026, batch 44", in the title block, the abstract, the
scope box, the reading-route box, Section 8.5, Section 10, Part II's status
box, Section 11.3 and Research questions 1 and 2, and Part III's Section 26.3
and Research question 18; Parts V–VII's answers are in Sections 66.3, 83.3
and 100.3, and their dated pointers, marked "Added 29 September 2026,
batch 55", are in the title block, the abstract, the scope box, the
reading-route box, Section 1, Part II's Research question 3, Part III's
Corollary 37.4, the containment paragraph of Section 39 and Research
questions 11 and 15, and Part IV's Corollary 50.3, Proposition
51.4, Theorem 52.1, the remark after Corollary 53.2, Theorem 58.1 and
Research questions 23, 24, 26, 28, 32 and 34):

- Conjecture 5.3 (real roots) is **false** — first counterexample credited to
  Patel. Part I never asserted it, so nothing is retracted.
- Conjecture 5.2 (gamma-positivity) is **proved in height ≤ 2 only**; open in
  general, including height-two posets blown up by nontrivial equivalence
  classes (Research question 1).
  [Updated 29 September 2026, batch 44: proved in height ≤ 2 and, by
  Part IV, in general — for every finite preorder, blowups included
  (Theorem 48.2; Example 54.2 is a height-two blowup). Research question 1
  is **answered**. Part III's Research question 18 ("Transfer beyond
  height-two posets") is answered in its aim, by transport pairs rather than
  stable signed-support methods. Research question 2 (a bijective counting
  bridge) **remains open**: both manuscripts use the same imported identity
  and re-pose it as Research question 20. See Section 46.3.]
- Conjecture 5.1(d) (a flag polytope) **remains open**. For every preorder
  with an induced crown on at least six elements, Part I's polytope `S_tau` is
  not flag, since its boundary is a pulling (hence lattice) triangulation;
  Part I's six-element crown is the smallest case. Some other flag polytope
  with the same h-vector is not excluded.
- Part II's Research question 4 ("Beyond the sixth-root cactus matrices") is
  **answered** by Part III: exactly the cacti, and strictly stronger than
  stability. Research question 3 (which graph structures preserve
  real-rootedness) is **re-scoped, still open**: Part III's `K_{2,3}` tree
  attachments are noncacti with real-rooted `p_G`. [Updated 29 September
  2026, batch 55: Part VI shows that vertex sums preserve and reflect
  stability, and that edge subdivision can restore real-rootedness without
  stability (`ϑ(3,3,3)` vs `ϑ(3,3,5)`); real-rootedness alone under vertex
  sums is not treated.]
- [Added 29 September 2026, batch 44.] Conjectures 5.3 and 5.1(d) are
  unchanged by Part IV: gamma-positivity does not imply real-rootedness, and
  Part IV constructs no flag polytope (Research question 22). Part IV proves
  Conjecture 5.1(a)–(b) (palindromicity, unimodality) again, by a route
  independent of Part I's unrefereed geometry. It refutes nothing in Parts
  I–III; nothing is retracted.
- [Added 29 September 2026, batch 55.] Part V strengthens unimodality to
  **ultra-log-concavity of every `h_tau`** and of every height-two gamma
  vector; **Research question 23 is answered** (palindromic support
  polynomials of all bipartite graphs); Research question 24 is answered in
  height two only; Research question 26's unrestricted complexity and
  Research question 32's "specified `gamma_k`" are answered (#P-hard already
  in height two, with FPRASes); Research question 28 gains binomial
  convex-order domination, not a limit law. Part VI proves that **stability
  of `Phi_G` is strictly stronger than real-rootedness of `p_G`** (Part
  III left this open), answers Part III's gluing target in Research
  question 11, and classifies two treewidth-two families; Research question
  11 stays open in general. Conjectures 5.3 and 5.1(d) are unchanged. Parts
  V–VII refute nothing in Parts I–IV; nothing is retracted.
- [Added 30 September 2026, batch 63.] Part VIII removes the "stated
  terminal convention" of Part VI's criterion (Section 93.4, "What these
  results do not imply") for one apex over a tree, and answers no numbered
  research question: its Research questions 58–60 re-pose Part VI's 45, 47
  and 48 with added detail, and 64–65 overlap 44, 52 and 53. Its answers
  are in Section 116.3; its dated pointers, marked "Added 30 September 2026,
  batch 63", are in the title block, the abstract, the scope box, the
  reading-route box, after Theorem 84.1, in Sections 89.2 and 93.4, and
  after Research questions 45, 47 and 48. Conjectures 5.3 and 5.1(d) are
  unchanged; nothing is refuted or retracted.
- [Added 30 September 2026, batch 64.] Part IX **answers Part V's
  "Sampling boundary"** (Section 75.7) and "Precisely what is sampled for
  a preorder" (Section 75.4): it samples actual demand vectors and preorder
  lattice points almost uniformly. It **constructs the bijection** asked
  for by Research questions 2 and 20 (and by the unnumbered source-06/07
  paragraphs of Section 80.1), support-preserving and with an elementary,
  Ehrhart-free proof; their compatibility clauses are answered only in
  part (deletion outside the selected sets, support weights), full
  equivariance is shown impossible, and the rest is Research question 71.
  Source 09's "Direct lattice-point bijections" (Section 112.1) is answered
  in its support-resolved part, not as a canonical or clone-compatible
  bijection. Research questions 39 (binary capacities; label added) and 43
  (formalization) stay open, extended by 68 and overlapped by 73.
  Conjectures 5.3 and 5.1(d) are unchanged; nothing is refuted or
  retracted. Its answers are in Section 132.3; its dated pointers, marked
  "Added 30 September 2026, batch 64", are in the title block, the
  abstract, the scope box, the reading-route box, after Part II's
  Lemma 14.1 and Research question 2, after Part IV's Remark 49.4 and
  Research question 20, in Part V's Sections 67.3 (claim table), 68.2,
  75.4 and 75.7, after Research questions 39 and 43 and in Section 80.1,
  and in Part VII's Sections 109 and 112.1.

## Not claimed

From Part I (see also `STATUS.md`, `PROOF_AUDIT.md`): no new proof of the
already settled duality (Conjecture 5.4); no claim that the support
polynomial is `h*(Q_tau)` (it is `h*(B_tau)` and `h*(C_tau)`); nothing about
arbitrary reflexive nontransitive relations (Section 8.5 gives a
nonpalindromic example); the finite computations are not size records.
[Added 29 September 2026, batch 44: Part IV's Theorem 48.3 now treats every
reflexive relation — palindromic exactly when transitive — and explains
Section 8.5's example.]

From Part II (see also `02-height-two-STATUS.md`, `02-height-two-sources.md`):

- No first disproof of Conjecture 5.3 and no minimum-size claim: the
  eight-element example is Patel's; the 17-element example is a transfer of a
  classical graph polynomial. Minimality of the eight-element example is not
  claimed beyond the authors' reported small-size tests (Research question 9).
- No gamma-positivity beyond height two, or for nontrivial block blowups.
  [Added 29 September 2026, batch 44: this remains Part II's scope; the
  property holds in height two and, by Part IV, in general.]
- No disproof of Conjecture 5.1(d); the crown obstruction concerns lattice
  triangulations and the toric configuration of `C_tau` only. Chordal
  bipartiteness is shown necessary for a flag lattice triangulation of `D_G`,
  not sufficient.
- No canonical bijection in the counting lemma (Lemma 14.1 equates
  cardinalities through two imported root-polytope theorems).
  [Added 30 September 2026, batch 64: Part IX constructs an explicit,
  support-preserving bijection — cost-dependent, hence not canonical
  (Proposition 144.1) — and its disjoint union proves the lemma without the
  two root-polytope inputs (Theorem 135.2, Corollary 139.2).]
- Part II itself gave no characterization of graphs admitting a cactus-style
  matrix (Part III now does); no claim that every noncactus graph fails
  real-rootedness (Part III shows some do not); no limiting root measure for
  `Theta_m`; no weighted preorder-polytope interpretation of the weighted
  cactus polynomial.
- No novelty for the univariate cactus theorem, the crown formula, or the
  matrix technique; no absolute publication priority for any extension (the
  source audit was targeted, not exhaustive). A withdrawn SSRN listing for an
  eight-element counterexample (abstract 7385158) was noted by the manuscript
  and is not used as evidence.
- No Lean verification; the staged formalization plan (Section 23) has not
  been started.

From Part III (see also `03-cactus-STATUS.md`, `03-cactus-SOURCES.md`):

- No novelty for the cactus sixth-root construction, its determinant
  factorization or cactus stability (Part II's), for univariate cactus
  real-rootedness (Ohsugi–Tsuchiya's), or for the height-two transform
  (Part II's); the binary (forest) observation and the general phenomenon of
  stability without a determinant representation (for example Vámos-type
  polynomials, Burton–Vinzant–Youm) are not claimed as new.
- No worldwide publication priority for the classification, the finite-field
  reformulations, the gauge count, the quantitative refinements or the
  stability formulations; the source audit was targeted, and a related earlier
  characterization of binary fundamental transversal matroids (Nakamura 1989,
  publisher abstract only) deserves further review.
- No general characterization of real-stable or real-rooted matching-support
  polynomials (Research question 11), and no claim that the containment
  "stable `Phi_G` ⇒ real-rooted `p_G`" is strict. [Updated 29 September
  2026, batch 55: strictness is proved in Part VI (books `B_m`, `m ≥ 5`;
  `ϑ(3,3,5)`); a general characterization is still not claimed, but two
  treewidth-two families are classified.]
- No nonexistence theorem for larger determinantal pencils, auxiliary
  variables, sums of determinants or powers (Research question 15); only the
  vertex-indexed diagonal pencil is excluded.
- No extension of the sharp gap to non-unit edge magnitudes (Research
  question 16); no claim that `d(theta(3,3,3))` equals its lower bound 3/5
  (Research question 12).
- No fixed-size minor test (Theorem 38.1 shows none can work); no
  gamma-positivity or flag-realization result for preorders; no exhaustive
  survey of the repository. [Added 29 September 2026, batch 44:
  gamma-positivity for every preorder is now Part IV's; flag realization
  remains open.]
- The `K_{2,3}` stability proof imports Brändén's multiaffine Rayleigh
  criterion (Theorem 5.6 of *Adv. Math.* 216 (2007)); the classification,
  gauge count, gap and bounded-order results use no unproved repository
  theorem.

From Part IV (see also `05-gamma-positivity-PROOF_STATUS.md`,
`05-gamma-positivity-SOURCE_AUDIT.md`; manuscript 01 shipped no notes):

- **Imported input.** The main theorem rests on the demand/support
  counting identity (Part II's Lemma 14.1). That identity is reduced to two
  published root-polytope theorems (Kálmán–Postnikov; Ohsugi–Tsuchiya, as
  stated by Davis–Kohl). These are cited inputs, not reproved. The theorem
  does not use Part I's unrefereed polytope theorem.
- **No bijections.** No canonical bijection between demand vectors and
  matchable support pairs is given. No natural Boolean action on the actual
  lattice points is given either: manuscript 01's toggles act on an
  auxiliary support-pair model. [Added 30 September 2026, batch 64: Part
  IX gives an explicit, support-preserving, non-canonical bijection
  (Theorem 135.2); the Boolean action on actual lattice points is still
  not given.]
- **Open conjectures and other statistics.** No flag-polytopal realization
  (Conjecture 5.1(d)). No real-rootedness, and no log-concavity or
  unimodality of the gamma vector. No identification of `h_tau` with the
  Ehrhart numerator of the original `Q_tau`. [Updated 29 September 2026,
  batch 55: Part IV's own scope. Part V proves ultra-log-concave height-two
  gamma vectors and ultra-log-concave `h_tau` for every preorder; gamma
  log-concavity beyond height two remains open.]
- **Limits of the reflexive-relation criterion.** It is no classification
  for unbalanced bipartite graphs, for balanced graphs without a perfect
  matching, or for graphs whose maximum matching is smaller than a shore.
  It is no real-rootedness criterion. [Added 29 September 2026, batch 55:
  Part V classifies palindromicity for every bipartite graph.]
- **Credited, not claimed.** Nothing new is claimed for:
  - the matching-support interpretation (Ohsugi–Tsuchiya, Davis–Kohl);
  - the hypertree volume count (Kálmán–Postnikov);
  - the support-enumerator identity and preorder duality `h_tau = h_(tau*)`
    (Dai–Hou–Liu–Thawinrak–Wang), which Part IV recovers and refines;
  - the octopus and lopsided-octopus results (Menon; the octopus formula is
    attributed there to Athanasiadis, Xiao and Yan);
  - the height-two theorem (Part II);
  - the classical chain (Narayana), binomial and universal-equivalence
    formulas;
  - the Patel and Stembridge–Ohsugi–Tsuchiya counterexamples, which Part IV
    cites and does not re-claim.
- **Priority.** No worldwide publication priority is claimed. The source
  searches of 29 September 2026 were targeted and partly uninformative. The
  relation of the endpoint-defect criterion to older matching and Gorenstein
  characterizations deserves further historical review.
- **Finite checks and formalization.** The finite checks do not prove the
  all-`n` statements. No Lean or Rocq formalization exists. Both
  manuscripts' formalization plans (Section 60) are unstarted.

From Part V (see also `06-lorentzian-support-SOURCES.md`,
`07-support-polynomials-PROOF_STATUS.md`, `07-support-polynomials-SOURCES.md`):

- **Imported, not reproved:** the support-counting bridge (Ohsugi–Tsuchiya
  and Oh for source 06; Dai et al. Theorem 1.2 and Davis–Kohl Theorem 3.10
  for source 07), the Lorentzian theorems of Brändén–Huh, Röhrle–Ulirsch's
  Theorems A and E, the Anari–Liu–Oveis Gharan–Vinzant mixing theorem, and
  Colbourn–Provan–Vertigan's #P-completeness. The transversal-matroid model
  is classical (Balas–Pulleyblank, as identified by Mori).
- **No normalization by the matching number** `nu(H)` in place of the
  smaller shore (Research question 37; a finite search found no
  counterexample, which is evidence only).
- **No gamma log-concavity beyond height two**; no real-rootedness
  classification; the Lorentzian conclusions do not upgrade to real
  stability (`Theta_3`); no flag realization; no limit theorem.
- **No bijection and no lattice-point sampler.** The samplers return
  supports or support pairs, not demand vectors or lattice points; no
  demand/support bijection is constructed. [Added 30 September 2026, batch
  64: this describes Part V. Part IX constructs the bijection
  (Theorem 135.2) and an almost-uniform sampler of actual demand vectors and
  preorder lattice points (Theorem 145.2, Corollary 146.2).]
- **No production FPRAS.** The coefficient FPRAS is a proved reduction;
  the shipped sampler is a reference implementation, and no exact
  polynomial-time counter or binary-capacity algorithm is claimed.
- **No worldwide priority** for the applications; the palindromicity
  classification re-proves Part IV's balanced case.

From Part VI (see also `08-ade-stability-SOURCE_AUDIT.md`):

- The ADE list of trees with spectral radius at most two is classical; the
  `ϑ(3,3,3)` obstruction is Part II's (priority Patel); even-cycle stability
  and tree attachments are not new; `K_{2,3}` stability without a faithful
  matrix is Part III's.
- No classification of all stable bipartite graphs, of all fundamental
  transversal matroids with the half-plane property, or of all real-rooted
  diagonals; source 08's Research question on tree diagonals is open (for
  this merge the diagonal was checked real-rooted for all 986 trees with
  `2 ≤ r ≤ 12`, evidence only).
- Weighted real-rootedness of the books with `m ≥ 5` is not claimed; the
  negative Rayleigh certificate is not a nonreal-root weighted diagonal.
- No flag-polytope consequence; no worldwide priority (the literature
  search was focused and found no earlier statement of the tree criterion);
  no formalization.

From Part VII (see also `09-matroid-lifts-CLAIMS_AND_SOURCES.md`):

- The gammoid characterization (Ingleton–Piff) and the extended-matroid
  construction (Röhrle–Ulirsch) are classical; the clone/transitivity
  criterion is Part IV's cancellation criterion in matroid form, and the
  orbit formula is Part IV's Boolean orbits with multivariate weights.
- Reconstruction is proved inside the image of `tau ↦ M_tau`; no intrinsic
  recognition of that image among all matroids (Research question 54).
- No lattice-point interpretation of the transport weights and no action
  of the clone group on lattice points; no gamma log-concavity; no
  classification of stable 2-connected blocks (Part VI's question).
- No Lean or Rocq verification; the staged formalization plan (Section 111)
  is unstarted.

From Part VIII (see also `10-marked-trees-SOURCE_AUDIT.md`):

- The classification (Theorem 118.2) is **not a new discovery of ADE
  stability**: it follows from Part VI's theorems, as source 10 says; its
  comparison table's "continuation developed here" carries a merge note.
  The ADE list, the half-plane-property framework, Brändén's Rayleigh
  criterion and the `ϑ(3,3,3)` example (priority Patel) are credited; the
  eight-vertex obstruction is not presented as a new small-matroid discovery
  (Kummer–Sert classify the half-plane-property matroids on at most eight
  elements).
- No classification of all stable bipartite graphs, of several apices or of
  hosts with cycles, and no answer to the individual support-diagonal
  question (Research question 58, which contains Part VI's 45).
- The finite enumeration (31,886 marked instances on 95 trees with
  `n ≤ 9`) tests the implementation of the structural classification; it
  is not an independent analytic stability test. Only the 133 small-order
  determinant identities enumerate matching supports independently.
- The `O(n^5)` bound is conservative and the code is a reference
  prototype, not a large-instance solver; the linear-time recognition claim
  concerns the structural decision, not the bit length of rationalized
  eigenvectors. Markings related by a tree automorphism are counted
  separately.
- No worldwide priority (the review was focused; principal extensions and
  transversal-matroid presentations deserve specialist comparison); no Lean
  or Rocq verification.

From Part IX (see also `11-two-flow-PROOF_STATUS.md`,
`11-two-flow-SOURCE_AUDIT.md`):

- **Prior, not claimed:** the existence of the demand/base correspondence
  and its leaf-count description (Oh; used by Ohsugi–Tsuchiya), the
  support-counting identity it implies (Corollary 139.2; Parts II, IV and
  V), rapid mixing of the basis walk (Anari–Liu–Oveis Gharan–Vinzant, whose
  Theorem 1.1 is imported), the preorder polytopes (Athanasiadis–Chapoton),
  and Part V's matroid, conditioning, preorder-reduction and cloning
  constructions. Loho–Smith's closely related lattice-point bijections were
  not audited in full, so no first priority is claimed for the min-cost-flow
  realization.
- **Not canonical, not local.** The maps depend on the cost chamber; no
  deterministic support-preserving bijection is equivariant under all
  automorphisms (Proposition 144.1), and none moves coordinates by a
  bounded amount per basis exchange (Proposition 144.2). Restriction
  compatibility holds only for receivers outside the support and suppliers
  outside the selected set; no arbitrary-minor compatibility is claimed.
- **Sampling scope.** The sampler is almost-uniform (total variation `η`),
  assumes ideal random bits, and covers support-product weights only: no
  exact independent uniform sampler, no magnitude-dependent weights
  (`Π q_y^{c_y}`), no polynomial-in-log-capacity sampler (dilations go
  through cloning), no production large-graph sampler, and no
  reimplementation of the matroid FPRAS. The reference sampler uses
  Python's pseudorandom generator and integer activities only; a smaller
  `steps` override voids the mixing guarantee. The rational-activity and
  support-conditioned samplers are proved but not packaged.
- **Checks and formalization.** The finite suites (4,785 bipartite graphs,
  390 preorders, 250 random cases, two exact chains) test the
  implementation; they are not proofs, and a certificate checker in Python
  can itself contain a bug. No Lean or Rocq formalization; the plan of
  Section 147.3 and Research question 73 are unstarted.

## Labels

Part I's 60 labels are bare (`sec:`, `eq:`, `thm:`, `lem:`, `prop:`, `cor:`,
`app:`) and are unchanged, with unchanged numbers. Part II's 87 labels carry
the prefix `htwo:` ("height two"): the manuscript's 76 labels, prefixed, plus
11 new ones (its conclusion and build subsection, two previously unlabelled
corollaries, and the provenance section's seven). Part III added **70**
labels, all with the prefix `cac:` ("cactus"): 60 of manuscript 05's 64
labels, prefixed (the other four labelled the displays that repeat Part II's
formulas, which are printed once, in Part II), plus 10 new ones (the
provenance section's six, the build subsection, the conclusion, the
dependency ledger, and `cac:q:beyond` on Part II's Research question 4).
Total: 217. No label was renamed or removed; the numbers of all 147 earlier
labels are unchanged (compared in the `.aux` files of the committed and the
new build). Part III begins at Section 26, after Part II and before Part I's
appendices, whose letters and numbers are unchanged.

Part IV added **129** labels, all with the prefix `gam:` ("gamma"). There
are 94 plain `gam:` labels and 32 `gam:gv:` ("gamma vector") labels in
Part IV, the latter for material only manuscript 01 contains. The other
3 are new labels on existing text, so that Part IV can cite it:
`gam:sec:reflexiveex` on Part I's Section 8.5, and `gam:q:extend` and
`gam:q:bridge` on Part II's Research questions 1 and 2. The manuscripts'
own labels (bare, with no prefix) were all renamed into `gam:` or
`gam:gv:` before anything cited them. New total: **346**. No label was
renamed or removed. The numbers of all 217 earlier labels are unchanged
(compared in the `.aux` files of the committed and the new build). Their
page numbers moved by one to three pages, because the table of contents and
the abstract grew; those in Part I's appendices moved by 42 pages, past
Part IV. Part IV begins at Section 46, after Part III and before
Part I's appendices, whose letters and numbers are unchanged. Its research
questions continue the report's numbering as 20–36. Its tables are Tables
3–5; they follow Part III's two tables, and Part I's appendices have none.

Parts V–VII added **340** labels. Part V has 157: 95 with `lor:`
("Lorentzian", source 06 and the merge's own), 56 with `lor:sp:` ("support
polynomials", source 07), and 6 `lor:hq:` labels added to Part IV's Research
questions 23, 24, 26, 28, 32 and 34 so that Part V can cite them. Part VI has
126: 100 with `ade:` (source 08 and the merge's own), 23 with `ade:mat:`
(source 09's stability sections), and 3 `ade:hq:` labels added to Part II's
Research question 3 and Part III's Research questions 11 and 15. Part VII has
57 with `mat:` (source 09). The sources' own labels (bare) were renamed into
these prefixes before anything cited them; labels of passages that are not
reprinted (source 07's duplicated statements, source 09's coefficient
sections) are not carried over, and references to them point to the
printed statements. New total: **686**. No earlier label was renamed or
removed, and the numbers of all 346 earlier labels are unchanged (compared
in the `.aux` files of the committed and the new build). Their page numbers
moved by three or four pages (the title block, abstract, scope box and
contents grew); those in Part I's appendices moved by 104. Parts V–VII begin
at Sections 66, 83 and 100, after Part IV and before Part I's appendices,
whose letters and numbers are unchanged. Their research questions continue
the numbering as 37–43 (Part V), 44–53 (Part VI) and 54–57 (Part VII). Their
tables are Tables 6–12 (notation tables 6, 8 and 12).

Part VIII added **95** labels, all with the prefix `mts:` ("marked-tree
stability"): source 10's 76 labels, prefixed before anything cited them
(three of them, `eq:C`, `eq:Q` and `thm:main`, equal bare Part I labels),
none dropped; 15 new ones (Section 116, its four subsections and its
notation table, the eight research questions, and `mts:app:certificate`); and 4
`mts:hq:` labels added to Part VI's previously unlabelled Research questions
45, 47, 48 and 52 so that Part VIII can cite them. New total: **781**. No
earlier label was renamed or removed, and the numbers of all 686 earlier
labels are unchanged (compared in the `.aux` files of the committed and the
new build). Their page numbers moved by one or two pages (the title block,
abstract, scope box, reading route and contents grew); those in Part I's
appendices moved by 28. Part VIII begins at Section 116, after Part VII and
before Part I's appendices, whose letters and numbers are unchanged. Its
research questions are 58–65; its tables are Tables 13–15 (notation table
13) and its figure is Figure 4.

Part IX added **96** labels, all with the prefix `tf:` ("two-flow"): source
11's 80 labels, prefixed before anything cited them (three of them,
`thm:main`, `eq:B` and `sec:limits`, equal bare Part I labels), none
dropped; 15 new ones (Section 132, its four subsections and its notation
table, the rewritten Section 133.1, and the eight research questions); and
`tf:hq:capacities` on Part V's previously unlabelled Research question 39,
so that Part IX can cite it. New total: **877**. No earlier label was
renamed or removed, and the numbers of all 781 earlier labels are
unchanged (compared in the `.aux` files of the committed and the new
build). Their page numbers moved by one or two pages (the title block,
abstract, scope box, reading route and contents grew); those in Part I's
appendices moved by 28. Part IX begins at Section 132, after Part VIII
and before Part I's appendices, whose letters and numbers are unchanged.
Its research questions are 66–73; its tables are Tables 16–18 (notation
table 16) and its figure is Figure 5.

## Notation

Table 1 (Section 11.2) fixes Part II's symbols against Part I's; Table 2
(Section 26.2) fixes Part III's against both; Table 3 (Section 46.2) fixes
Part IV's against all three. Watch in particular:

- `P_G`, `P_0`, `P_r`, `P_{Theta_m}` are **posets**; Part I's `P_tau` is a
  **lattice-point set**, which Part II writes `Q(P) ∩ Z^V`. With `tau = P`,
  Part II's `h_P`, `Q(P)`, `C_P` are Part I's `h_tau`, `Q_tau`, `C_tau`.
- `G = (A ⊔ B, E)` is the n-vertex comparability graph, **not** Part I's
  doubled 2n-vertex graph `G_tau` (and `E` is its edge set, not Part I's ground
  set). Remark 11.1, a merge note, shows that Part I's and Part II's imported
  inputs agree: `h_tau(t) = p_{G_tau}(t)` for every preorder, whereas
  `p_G` is the **gamma**-polynomial of `h_{P_G}`. (Checked by direct
  enumeration for all 390 labeled preorders with `n ≤ 4` in the batch-39
  write phase; that check is not shipped.)
- `p = |A|`, `q = |B|` are not Part I's `p(y)`, `q(y)`; `m` indexes `Theta_m`,
  not a dilation; `K` is the cactus matrix, not a triangulation; `S` is a
  subset or a random support size, not `S_tau`; `I` in Section 18 is an
  independent set, not an order ideal.
- **Part III renames one symbol:** manuscript 05's theta `Θ(a,b,c)` (three
  paths of lengths a, b, c) is printed `ϑ(a,b,c)`, because Part II's `Theta_m`
  has `m` paths of length three. Only `Theta_3 = ϑ(3,3,3)` is both — it is
  Part III's core `T`. No normalization was changed.
- Part III defines `Phi_G` for **every** bipartite graph by the signed
  support sum; Part II's `Phi_G = det(diag(z) − H_G)` is the same polynomial
  for cacti only. Part III's cores `E`, `D`, `T` (sans-serif) are not the edge
  set `E` or Part II's `D_G`, `T_G`; its defect `d(G)` is not the vertex `d`
  of `Theta_m`; its `p, q, r` in Lemma 36.6 are inner products and `q` in
  Proposition 35.3 is a field size, not shore sizes.
- **Part IV renames four symbols and retypesets one; no normalization was
  changed.**
  - Manuscript 06's transitive closure `R*` is printed `R̄` (overline):
    `tau*` is the *opposite* preorder in Part I and in manuscript 01.
  - Manuscript 06's opposite preorder `tau^op` is printed `tau*`.
  - Manuscript 01's comparability graph `C_tau` is printed `Comp(tau)`:
    Part I's `C_tau` is the polytope.
  - Manuscript 01's `g_k`, `D_k(tau)` and variables `t_v` are printed
    `gamma_k`, `T_k(tau)` and `z_v`.
  - Both manuscripts' `Q_tau` is printed as Part I's calligraphic `Q_tau`.
- **Part IV's doubled graph `G_tau`** has an edge `a_L b_R` iff
  `a ≤_tau b`. That is Part I's `G_tau` (edge `i_L j_R` iff `j ≤_tau i`)
  with its two shores exchanged. The polynomial `p_(G_tau)` is the same,
  but the receiver side recorded by Part IV's multivariate formulas is
  Part I's left side.
- **Transport pairs versus Part II's sets.** Part IV's transport pairs
  `T_k(tau)` are *ordered* pairs of disjoint sets. Part II's `M_k(G)` are
  *unordered* vertex sets. The two agree only in height two
  (Section 55.3).
- **Other letters.** `Gamma_tau` is the gamma polynomial. `Gamma(1/4)` in
  Section 58 is its value at 1/4, not Euler's Gamma function. `K`, `L`
  there are a mixing variable and the support size (Part II's `S`). The
  letters `d`, `D`, `P`, `B_{s,r}`, `A_{s,r}` and `m_i` of the block
  formulas are not Part I's or Part II's symbols of the same letter.
- **Parts V–VII (Tables 6, 8, 12).** Three renamings, no normalization
  changed. The transversal matroid of a bipartite graph with private copies
  of the left shore (sources 06, 07, 08) is printed `𝖬_H`/`𝖬_G` (sans
  serif), because `M_G(u)` is Part II's matching polynomial; source 09's
  matroid is printed `M_G`, `M_tau` as delivered and is the **dual**
  (`M_G = 𝖬_G^*`; bases `I ⊔ (B∖J)` versus `(U∖I) ⊔ J`). Sources 06 and 07's
  random support size `K` is printed `L`, as in Part IV's Theorem 58.1,
  where `K` is the mixing variable (source 07's bit length becomes
  `L_bit`). Source 08's thetas `Θ(a,b,c)` are printed `ϑ(a,b,c)`, extending
  Part III's rule to any number of paths. Both sources' `Q_tau` is printed
  `𝒬_tau`.
- In Part V the letters `r` and `d` are **not** renamed and depend on the
  source: in source 06's sections `r = min(m,n)` (isolated vertices kept);
  in source 07's `r = nu(H)` and `d` is the smaller shore after deleting
  isolated vertices; in Theorem 75.5 `d = nu(H)`. Source 06's `F_H` is
  source 07's `D_H`.
- Part VI's `L`, `B`, `T`, `C_T` are a pencil, an incidence matrix, a tree
  and `I − A_T/2`, not Part V's support size or Parts I–III's symbols of
  the same letters; `B_m` is a book.
- **Part VIII (Table 13).** Two renamings, no normalization changed:
  source 10's `G(T,S)` is printed `A(T;S)` (calligraphic; `A(T;V(T))` is
  Part VI's `A(T)`), and its `Theta_3` is printed `ϑ(3,3,3)`. Source 10's
  `n = |V(T)|` is Part VI's `r`. Its `K` is the **hull** of the marking, not
  a matrix or `K_{l,r}`; its `H(T,S)` is the terminal skeleton, not the
  half-plane `ℍ`; its `L` is the pencil in Sections 121–122 but a **leaf
  set** in Sections 124–125; its `Z_T` counts **stable markings**, not the
  supports `p_{A(T;S)}` of one marking; its `Q(R_1,R_2,R_3)` is not Part I's
  `Q_tau`.
- **Part IX (Table 16).** Four renamings, no normalization changed:
  source 11's `𝓑_H(J)` and `𝓑_H` (matchable supplier sets and pairs) are
  printed `𝓜_J(H)` and `𝓜(H)` — Part V's pair set — because Part V's `𝓑_H`
  is the **basis polynomial**; its `𝓓_H`, `M_H` and `Q_tau` are printed with
  Part V's `𝒟_H`, `𝖬_H` and the report's `𝒬_tau`. Its `Phi_w`, `Psi_w` are
  maps, not Part VI's polynomial `Phi_G`; its `r = |J|` is the support
  size, not Part V's `r = min(m,n)` or `nu(H)`; its `L = r + 1` is a margin
  scale, not Part V's random support size; its `T` is a spanning tree; its
  `q` counts augmented edges except in Section 146.1 (a dilation factor)
  and in `Π q_y^{c_y}` (magnitude weights); its preorder graph `H_tau` has
  Part V's orientation (`x` supplies `y` iff `x ≤_tau y`), which is Part I's
  `G_tau` with the shores exchanged.

## Files

```
article.tex                                  the report, standalone LaTeX with an internal bibliography
article.pdf                                  the compiled report, 277 pages, A4 (title p. 1, scope box and contents pp. 2–10,
                                             Part I pp. 11–23, Part II pp. 24–52, Part III pp. 53–77,
                                             Part IV pp. 78–118, Part V pp. 119–168, Part VI pp. 169–202,
                                             Part VII pp. 203–219, Part VIII pp. 220–246, Part IX pp. 247–273,
                                             Part I's appendices pp. 273–275, references pp. 275–277)
README.md                                    this guide
STATUS.md                                    Part I: literature and claim status, 20 Sep 2026
PROOF_AUDIT.md                               Part I: independent-review checklist
build.py                                     Part I: two-pass pdfLaTeX script (builds into build/ here; see below)
code/verify.py                               Part I: exact standard-library verifier
data/preorders_through_5.csv                 Part I: all 7,332 labeled preorders through n = 5 and their h-vectors
data/verification_results.json               Part I: detailed exact results and sample certificates
data/verification_log.txt                    Part I: console transcript of the recorded run
data/runtime.txt                             Part I: observed runtime and environment of that run
02-height-two-STATUS.md                      Part II: claim and verification status (delivered STATUS.md)
02-height-two-sources.md                     Part II: sources and priority audit (delivered sources.md)
code/02-height-two-verify.py                 Part II: graph, preorder, crown and cactus checks (standard library)
code/02-height-two-verify_theta.py           Part II: Theta_m formulas, direct enumeration, exact Sturm counts
code/02-height-two-direct_counterexample.cpp Part II: independent C++17 enumeration of the 17-element example
code/02-height-two-Makefile                  Part II: the delivered Makefile (do not run here; see below)
data/02-height-two-verification.json         Part II: recorded output of verify.py
data/02-height-two-theta_verification.json   Part II: recorded output of verify_theta.py (m = 1..20)
data/02-height-two-direct_counterexample.json  Part II: recorded C++ counts (8,408,566 points)
data/02-height-two-board_certificate.csv     Part II: all 90 polynomial states of the board recurrence (CRLF)
03-cactus-STATUS.md                          Part III: proof, priority and computational status (delivered STATUS.md)
03-cactus-SOURCES.md                         Part III: pinned repository source and literature audit (delivered SOURCES.md)
code/03-cactus-verify.py                     Part III: exact finite checks (standard library; Z[zeta], F_3, Q(sqrt 17))
code/03-cactus-Makefile                      Part III: the delivered Makefile (do not run here; see below)
data/03-cactus-verification.json             Part III: recorded output of verify.py (Python 3.13.5)
data/03-cactus-verification_log.txt          Part III: console output of that run (byte-identical to the JSON)
data/03-cactus-build_status.json             Part III: the manuscript's record of its own 24-page PDF build
code/04-gamma-vector-verify.py               Part IV (manuscript 01): exact finite checks (standard library)
code/04-gamma-vector-build.sh                Part IV (manuscript 01): the delivered two-pass build script (do not run here)
data/04-gamma-vector-verification.json       Part IV (manuscript 01): recorded output of verify.py (Python 3.13.5)
data/04-gamma-vector-verification.txt        Part IV (manuscript 01): console output of that run
05-gamma-positivity-PROOF_STATUS.md          Part IV (manuscript 06): theorem dependencies and verification boundary (delivered PROOF_STATUS.md)
05-gamma-positivity-SOURCE_AUDIT.md          Part IV (manuscript 06): source roles, pin and priority limits (delivered SOURCE_AUDIT.md)
code/05-gamma-positivity-verify.py           Part IV (manuscript 06): exact finite checks (standard library)
code/05-gamma-positivity-build.py            Part IV (manuscript 06): the delivered three-pass build script (do not run here)
data/05-gamma-positivity-preorders.csv       Part IV (manuscript 06): all 7,332 labeled preorders through n = 5, h- and gamma-vectors (CRLF)
data/05-gamma-positivity-verification.json   Part IV (manuscript 06): detailed results of the recorded run, with all 140 samples
data/05-gamma-positivity-verification.log    Part IV (manuscript 06): console transcript of that run
06-lorentzian-support-SOURCES.md             Part V (source 06): sources, theorem dependencies and limits (delivered SOURCES.md)
code/06-lorentzian-support-verify.py         Part V (source 06): exact finite checks (standard library)
code/06-lorentzian-support-support_sampler.py  Part V (source 06): reference basis-walk support sampler (imports verify)
code/06-lorentzian-support-test_sampler.py   Part V (source 06): seven unit tests (imports support_sampler, verify)
code/06-lorentzian-support-build.sh          Part V (source 06): the delivered build script (do not run here)
data/06-lorentzian-support-verification.json Part V (source 06): recorded output of verify.py (Python 3.13.5)
data/06-lorentzian-support-verification.log  Part V (source 06): console transcript of that run
data/06-lorentzian-support-sampler_smoke.json  Part V (source 06): 100-sample seeded sampler run on Theta_3
data/06-lorentzian-support-sampler_smoke.log Part V (source 06): console output of that run
data/06-lorentzian-support-sampler_tests.log Part V (source 06): unit-test transcript (7 tests)
07-support-polynomials-PROOF_STATUS.md       Part V (source 07): proof and novelty ledger (delivered PROOF_STATUS.md)
07-support-polynomials-SOURCES.md            Part V (source 07): primary sources and inspected versions (delivered SOURCES.md)
code/07-support-polynomials-support_tools.py Part V (source 07): graph, matroid-oracle and sampler library (standard library)
code/07-support-polynomials-verify.py        Part V (source 07): exact finite checks (imports support_tools)
code/07-support-polynomials-example_certificate.py  Part V (source 07): discriminant, Sturm and Theta_3 certificate (imports support_tools)
code/07-support-polynomials-build.sh         Part V (source 07): the delivered build script (do not run here)
data/07-support-polynomials-verification.json  Part V (source 07): recorded output of verify.py
data/07-support-polynomials-verification.log Part V (source 07): console transcript of that run
data/07-support-polynomials-example_certificate.json  Part V (source 07): recorded certificate
data/07-support-polynomials-example_certificate.log   Part V (source 07): its console output (byte-identical to the JSON)
data/07-support-polynomials-build_validation.json     Part V (source 07): record of the delivered 23-page PDF's build
08-ade-stability-SOURCE_AUDIT.md             Part VI (source 08): source and claim audit (delivered SOURCE_AUDIT.md)
code/08-ade-stability-verify.py              Part VI (source 08): exact checks (SymPy, NetworkX)
data/08-ade-stability-verification_results.json  Part VI (source 08): recorded output (Python 3.13.5, SymPy 1.14.0, NetworkX 3.6.1)
data/08-ade-stability-requirements.txt       Part VI (source 08): pinned versions (delivered requirements.txt)
09-matroid-lifts-CLAIMS_AND_SOURCES.md       Parts VI–VII (source 09): claim and dependency ledger (delivered)
code/09-matroid-lifts-verify.py              Parts VI–VII (source 09): exact finite checks (standard library)
code/09-matroid-lifts-Makefile               Parts VI–VII (source 09): the delivered Makefile (do not run here; see below)
data/09-matroid-lifts-verification_results.json  Parts VI–VII (source 09): recorded output of verify.py
data/09-matroid-lifts-verification_run.txt   Parts VI–VII (source 09): the same record (byte-identical)
10-marked-trees-SOURCE_AUDIT.md              Part VIII (source 10): pin, inspected line ranges, prior/new boundary (delivered SOURCE_AUDIT.md)
code/10-marked-trees-marked_trees.py         Part VIII (source 10): recognition, enumeration, optimization and repair library (NetworkX)
code/10-marked-trees-verify.py               Part VIII (source 10): exact finite checks (imports marked_trees; NetworkX, SymPy)
code/10-marked-trees-build.sh                Part VIII (source 10): the delivered three-pass build script (do not run here)
data/10-marked-trees-requirements.txt        Part VIII (source 10): pinned versions (networkx==3.6.1, sympy==1.14.0)
data/10-marked-trees-run.log                 Part VIII (source 10): console output of the recorded run (n = 1..9)
data/10-marked-trees-verification.json       Part VIII (source 10): recorded output (Python 3.13.5)
11-two-flow-PROOF_STATUS.md                  Part IX (source 11): proof, implementation and non-claim ledger (delivered PROOF_STATUS.md)
11-two-flow-SOURCE_AUDIT.md                  Part IX (source 11): pin, inspected passage, literature and priority audit (delivered SOURCE_AUDIT.md)
code/11-two-flow-transport_bijection.py      Part IX (source 11): exact flows, full/core maps, inverse, certificate checkers, sampler (standard library)
code/11-two-flow-verify.py                   Part IX (source 11): exhaustive and random finite checks (imports transport_bijection)
code/11-two-flow-build.sh                    Part IX (source 11): the delivered three-pass build script (do not run here)
data/11-two-flow-small.json                  Part IX (source 11): all 689 graphs with m, n ≤ 3 (5,880 support pairs)
data/11-two-flow-four_by_three.json          Part IX (source 11): all 4,096 graphs with (m, n) = (4, 3) (68,832 support pairs)
data/11-two-flow-preorders.json              Part IX (source 11): all 390 labeled preorders on ≤ 4 elements (12,709 lattice points)
data/11-two-flow-random.json                 Part IX (source 11): 250 seeded random graphs and cost orders (seed 20260930)
data/11-two-flow-chain.json                  Part IX (source 11): two exact 17-state Markov chains, exact TV after 8 steps
data/11-two-flow-example.json                Part IX (source 11): the worked certificate of Section 143 (zero-based labels)
data/11-two-flow-environment.json            Part IX (source 11): Python, platform and pdfTeX versions of the recorded run
data/11-two-flow-verification_run.txt        Part IX (source 11): console output of the recorded run (one JSON line per suite)
```

The ten `02-height-two-` files were staged in the placement commit
`e2b1f016a`, and the seven `03-cactus-` files in `3609d0473`, all
byte-identical to their deliveries. The board-certificate CSV is all-CRLF as
delivered (Python's `csv` writer) and is protected by a `-text` line in
`SetTheory/Cardinals/.gitattributes`; the `03-cactus-` files are LF text.
The four `04-gamma-vector-` and seven `05-gamma-positivity-` files were
staged in `203016015`, byte-identical to their deliveries (manuscript 01's
`results/` directory became `data/`). `data/05-gamma-positivity-preorders.csv`
is all-CRLF as delivered (7,333 lines) and has its own `-text` line in
`SetTheory/Cardinals/.gitattributes`; `data/05-gamma-positivity-verification.log`
was force-added past the root `*.log` ignore rule. The other Part IV files are
LF text.
The 30 files of Parts V–VII (ten `06-`, eleven `07-`, four `08-`, five
`09-`) were staged in `26473dfa0`, byte-identical to their deliveries
(source 06's `results/` and source 09's package-root outputs became
`data/`, programs and build files `code/`); all are LF text, and the five
`.log` files were force-added past the root `*.log` ignore rule. Two pairs
are byte-identical by delivery: source 07's `example_certificate.json` and
`.log`, and source 09's `verification_results.json` and
`verification_run.txt`.
The seven `10-marked-trees-` files of Part VIII were staged in `62f1ad07c`,
byte-identical to their delivery (its `results/` directory and
`requirements.txt` became `data/`, its programs and `build.sh` `code/`, its
`SOURCE_AUDIT.md` the report root); all are LF text, and the `.log` file was
force-added past the root `*.log` ignore rule.
The thirteen `11-two-flow-` files of Part IX were staged in `3025c15df`,
byte-identical to their delivery (its programs and `build.sh` became
`code/`, its `data/` directory `data/`, its `PROOF_STATUS.md` and
`SOURCE_AUDIT.md` the report root); all are LF text.

## Data conventions

**Part I.** The CSV fields are `n`, `principal_ideal_bitmasks` and
`h_coefficients`; the two vector fields use semicolons. Bit positions are
zero-based (row value 5 means {0,2}); row i is the set of j with
`j ≤_tau i` (a principal **ideal**, not a filter); coefficients are in
increasing degree; the `n = 0` row has an empty ideal field and polynomial 1.
Graph certificates in the JSON index both shores 0,…,n with 0 the added
universal vertex, offset by one from the bitmask indices. The run checks all
7,332 preorders through `n = 5` (symmetry, unimodality, duality, endpoints,
the `h_1` formula, special-simplex slacks) and all 35 through `n = 3`
independently (18,009 spanning trees, 399 matching-tree certificates); it
does not build a convex realization, test flagness or certify real roots.

**Part II.** Graphs are stored as bitmask neighbourhoods of the upper
vertices. The board CSV has columns `i`, `j`,
`coefficients_in_ascending_degree` (a JSON list) for the 90 cells
`0 ≤ i ≤ 9`, `0 ≤ j ≤ 8` of the recurrence (17.1). The recorded checks: all
512 labeled 3-by-3 bipartite graphs and 24 random 4-by-3 graphs (seed
20260928); crowns `2 ≤ r ≤ 8` (direct lattice checks `r ≤ 4`); 936 exact
square minors in six cactus configurations; `Theta_m` support enumeration
through `m = 9`, direct lattice enumeration through `m = 4`, exact Sturm
counts through `m = 20`; two graph-polynomial computations and a C++ count of
all 8,408,566 lattice points for the 17-element example. No floating-point
root finder is used.

**Part III.** Graphs with fixed labeled shores are binary edge masks;
sixth-root values are integer pairs `a + b·zeta` with `zeta^2 = zeta − 1`.
`data/03-cactus-verification.json` records: all 512 labeled 3-by-3 bipartite
graphs (460 cacti: 328 forests, 132 one-cycle) against 5,872 normalized
sixth-root assignments (7,792 ambiguous minors evaluated; 9,200 canonical
cactus minor checks); all 4,096 labeled 3-by-4 graphs (3,122 cacti: 1,856
forests, 1,248 one-cycle, 18 two-cycle) against 10,576 normalized ternary
assignments (14,717 ambiguous minors; 109,270 canonical cactus minor checks),
118,470 canonical checks in all; the three cores (36 sixth-root and 4 ternary
normalized assignments each, none valid); 3 Rayleigh identity classes
covering 10 pairs, 5 leaf attachments and 2 identities in `Q(sqrt 17)`; 100
augmented-minor norm/support comparisons on the thetas (2,2,4), (1,3,5),
(3,3,5); `"all_passed": true`. These are finite checks: enumerating sixth-root
phases does not exclude arbitrary complex phases, which the proofs do.

**Part IV.** The two programs use **opposite row conventions**.

- **Manuscript 06's CSV.** It has the same layout as Part I's CSV, with
  fields `n`, `principal_ideal_bitmasks`, `h_coefficients` and
  `gamma_coefficients`. Entry `i` of `principal_ideal_bitmasks` is
  `{j : j ≤_tau i}` (an ideal). Bits are zero-based, vector fields use
  semicolons, and coefficients are in increasing degree. Gamma vectors keep
  trailing zeros, and the `n = 0` row has polynomial 1.
- **Manuscript 01's JSON.** Its `rows` use bit `j` of row `i` for
  `i ≤_tau j`: principal *filters*, not ideals.

What the records show:

- **Manuscript 06** (`data/05-gamma-positivity-verification.json`,
  `"all_checks_passed": true`, seed 20260929):
  - all 7,332 labeled preorders through `n = 5`, with 228,075 support fibres
    and 1,774,841 equal-size doubled pairs (Table 5 of the article);
  - 689 bipartite graphs with shores of size at most 3 (5,880 feasible
    demand vectors);
  - all 4,166 reflexive relations through `n = 4` (the empty one included),
    with the number that satisfy common-support cancellation;
  - 140 deterministic, non-uniform samples on 6, 7 and 8 elements (46, 47
    and 47);
  - explicit-formula checks through `n = 20`.
- **Manuscript 01** (`data/04-gamma-vector-verification.json`,
  `"status": "ALL CHECKS PASSED"`, seed 20260929):
  - the same 7,332 preorders;
  - all bipartite graphs on shores (2,3), (3,3) and (3,4) (64, 512 and
    4,096), plus the empty-shore cases;
  - 119 distinct seeded closures (from 120 generated) on 6 or 7 elements;
  - 87 block-profile cases;
  - five named examples (Section 59.2 of the article).

Both are exact integer checks with no floating-point step. They are finite:
they do not prove the all-`n` theorems.

**Part V.** Source 06's JSON (`"finite_checks_only": true`, seed 20260929)
records all bipartite graphs with shores of size at most 3 (689) and all
4,096 on shores (3,4), 75 seeded graphs on (4,4), (5,4), (4,5) with their
adjacency rows, 14,021 nonempty conditioning events, 685 exact covariance
checks (principal minors), all 7,332 labeled preorders through `n = 5` by
direct ideal enumeration, and 64 integer-capacity examples; the sampler
JSON records 100 seeded supports (masks over four receivers) on `Theta_3`
with donor rows `14,3,5,9`. Source 07's JSON (`"status": "PASS"`, seed
20260929) records all 65,536 labeled 4×4 and 4,096 3×4 graphs (2,165,695 and
68,832 supports; 9,268 and 707 palindromic; the receiver-refined Hall
identity is checked on the 3×4 family only), the 390 labeled preorders
through `n = 4`, 300 weighted graphs at fugacities 1/3, 1, 7/2, 32 leaf-
transform identities, 30 sampler runs, and the `Theta_3` data (`p`,
`h`, 1,281 points) and the failed two-sided normalization. Graphs are
bitmask neighbourhoods; coefficients are in increasing degree.

**Part VI.** Source 08's JSON records, for each `r ≤ 9`, the unlabeled
trees, the number that are PSD/ADE and their types, the determinant-identity
evaluations, books `m = 0,…,8`, the even-theta expected-minor checks, the
contraction/deletion comparisons and the subdivision identities
(Table 11 of the article). It has no timing field; the version strings are
the only varying fields.

**Part VII.** Source 09's JSON (`"status": "PASS"`) records 4,690 bipartite
graphs, 4,165 reflexive relations and 389 preorders on 1–4 elements, 92,804
rank checks, 34 automorphism counts, 592 minor constructions, 16 vertex-sum
identities, and the `Theta_3` certificate (Rayleigh value −9 at the
recorded assignment; two real roots). Its `elapsed_seconds` varies.

**Part VIII.** Source 10's JSON (`"status"`: "All listed exact finite
checks passed; these are not formal proofs.", seed 20260930,
`max_tree_size` 9) records, for each `n ≤ 9`, the unlabelled trees
(NetworkX representatives), all their vertex subsets, the stable ones and
their skeleton types (`A`, `D`, `E`, `affine`), and the two failure modes
(`unmarked_branch`, `spectral_obstruction`) — Table 15 of the article,
31,886 marked instances on 95 trees, automorphic markings counted
separately; the check counts of Section 127 (21,237 PSD comparisons, 10,649
branch witnesses, 526 connected-energy instances, 133 identities with
24,534 minor coefficients, 190 enumerator, 285 optimization, 95 repair and
95 diameter comparisons); the `ϑ(3,3,3)` coefficients and discriminant
−5243; the two rational Rayleigh certificates (the fully marked `K_{1,5}`
and a nine-vertex subdivided tree with fringe); the star size enumerators
for `m = 3, 4, 6`; and 5 path and 11 star formula checks. All arithmetic is
exact. Its `elapsed_seconds` varies.

**Part IX.** Source 11's six suite records each carry `"suite"`,
`"passed": true` and `elapsed_seconds` (varies). `small` and
`four_by_three` count graphs and matchable support pairs by `(m, n)`
(689 graphs and 5,880 pairs; 4,096 and 68,832); `preorders` counts
labeled preorders and lattice points by `n` (1, 1, 4, 29, 355 preorders;
1, 2, 20, 376, 12,310 points; 390 and 12,709 in all); `random` records
seed 20260930, 250 graphs, 4,256 feasible-pair trials, 9,427
restriction/deletion and 8,512 chamber/gauge checks; `chain` records the
two 17-state chains (activities all one, and `(2,3,5)` on the receivers),
partition functions 17 and 144, the exact distances after eight steps
`15185263/1734623424` and `89267905200632003/10715864763905280000`, and
three rejected corrupted certificates; `example` is the worked certificate
of Section 143 in code labels: suppliers and receivers zero-based, the
dummy `-1`, flows as `[supplier, receiver, value]`, costs as
`[supplier, receiver, cost]`. `verification_run.txt` holds the same six
records, one JSON line each, in suite order. `environment.json` records
Python 3.13.5 on Linux and pdfTeX from TeX Live 2025/dev.

## Build the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Build in a scratch copy of `article.tex` so that no auxiliary files land here
(`build.py` writes a `build/` directory beside the source before copying
`article.pdf` back). The preamble needs Part I's packages (newpxtext,
newpxmath, tcolorbox, titlesec, fancyhdr, listings, hyperref, …) plus TikZ
and needspace for Part II; Part III adds only macros; Part IV adds macros,
an `example` environment and the TikZ library `arrows.meta` (for manuscript
01's dependency graph, Section 60); Parts V–VII add macros and the TikZ
library `positioning` (for source 06's dependency diagram, Section 67);
Part VIII adds only macros (`\Hull`, `\Leaf`, `\diam`, `\Stab`, `\Zpoly`,
`\pathin`) and does not load `cleveref`; Part IX adds one macro (`\TV`) and
likewise no `cleveref` or `float`. No image or font files are needed.
The shipped PDF (277 pages) was built on 30 September 2026 with MiKTeX
(pdfTeX 1.40.26) by `latexmk`: no errors, no undefined or multiply defined
references or citations, no duplicate destinations, no overfull boxes and
no other LaTeX warnings; five underfull boxes, the same five as the build of
the committed Parts I–VIII text (and of Parts I–VII before it): one (badness 1817) in Part II's
provenance-ledger table, which the committed builds before Parts III–VII and
the delivered manuscript 02's own build also show, and four (badness
1024–6625) in paragraphs of Parts V and VI that set long shipped file names
(Sections 78, 78.1 and 83.4). (The earlier builds of 29 September 2026 had
74 pages before Part IV, 116 before Parts V–VII and 220 before Part VIII;
the build of 30 September 2026 before Part IX had 249.)

## Rerun the checks

**Part I.** Its verifier needs no third-party packages; do not use `-O`.
Without `--output` it rewrites `data/preorders_through_5.csv` and
`data/verification_results.json` here, so pass a scratch directory:

```sh
py code/verify.py --output /path/to/scratch/part1      # or python3; ends with ALL CHECKS PASSED
```

Run this way on 28 September 2026 (Python 3.14.4, about 17 s), it passed, and
both outputs equal the shipped files apart from Windows line endings.

**Part II.** Its programs still use the delivered names. Run in this
directory, `02-height-two-verify_theta.py` fails with `ImportError`, because
its `from verify import …` loads Part I's different `code/verify.py`;
`02-height-two-verify.py` would write new unprefixed files
`data/verification.json` and `data/board_certificate.csv` here; and
`make -f code/02-height-two-Makefile verify` would run **Part I's**
`code/verify.py` and overwrite Part I's shipped data. Restore the delivered
layout in a scratch copy instead (Git Bash or another POSIX shell, from this
directory):

```sh
W=/path/to/scratch
mkdir -p "$W/02/code" "$W/02/data"
for f in code/02-height-two-*; do cp "$f" "$W/02/code/${f#code/02-height-two-}"; done
for f in data/02-height-two-*; do cp "$f" "$W/02/data/${f#data/02-height-two-}"; done
mv "$W/02/code/Makefile" "$W/02/Makefile"
cd "$W/02"
py code/verify.py          # writes data/verification.json, data/board_certificate.csv
py code/verify_theta.py    # imports code/verify.py of the copy; writes data/theta_verification.json
g++ -O3 -std=c++17 -Wall -Wextra -pedantic code/direct_counterexample.cpp -o direct_counterexample
./direct_counterexample > data/direct_counterexample.json
```

(`make verify` in the copy does the same with `python3`.) Run this way on
28 September 2026 (Python 3.14.4, g++ 16.1.0): all three passed; the board
CSV is byte-identical to the shipped file, the theta and C++ outputs are
identical apart from Windows line endings, and `verification.json` differs
only in its recorded run time (`seconds`) and line endings. Each run takes
about a second.

**Part III.** `03-cactus-verify.py` writes `data/verification.json` under the
parent of its own directory, so run in this directory it would add a new
unprefixed `data/verification.json` beside Part I's files (no file is
overwritten, but the tree is dirtied). `make -f code/03-cactus-Makefile`
would rebuild this whole article in place with `pdflatex` (leaving auxiliary
files here), its `verify` target would run **Part I's** `code/verify.py`,
which rewrites Part I's shipped data, and its `clean` target deletes
`article.aux`, `.log`, `.out` and `.toc` here. Use a scratch copy with the
delivered names:

```sh
W=/path/to/scratch
mkdir -p "$W/03/code" "$W/03/data"
for f in code/03-cactus-*; do cp "$f" "$W/03/code/${f#code/03-cactus-}"; done
for f in data/03-cactus-*; do cp "$f" "$W/03/data/${f#data/03-cactus-}"; done
mv "$W/03/code/Makefile" "$W/03/Makefile"
cd "$W/03"
py code/verify.py          # or python3; prints the JSON and rewrites data/verification.json of the copy
```

(`make verify` in the copy runs the same with `python3`.) Run this way on
29 September 2026 (Python 3.14.4, about 3 s): all checks passed, and
`data/verification.json` differs from the shipped file only in `python`
(3.14.4 vs 3.13.5) and `elapsed_seconds`. The program needs Python 3.10 or
later and only its standard library.

**Part IV.** Both programs are single standard-library files needing Python
3.10 or later, and neither imports a sibling module, so they run under their
shipped names. Their **default output paths are relative to the working
directory**. Run from this directory without arguments:

- manuscript 06's verifier would write unprefixed files `data/preorders.csv`
  and `data/verification.json` here, beside the prefixed copies;
- manuscript 01's verifier would create a stray `results/verification.json`.

Always pass an explicit scratch output (Git Bash or another shell, from this
directory):

```sh
W=/path/to/scratch
py code/05-gamma-positivity-verify.py --max-n 5 --out "$W/05"                      # prints the console record; writes preorders.csv, verification.json
py code/04-gamma-vector-verify.py --max-n 5 --output "$W/04/verification.json"   # prints the console record
```

Do not run manuscript 06's verifier with `python -O`: it exits, because it
relies on assertions. Neither delivered build script can build this article:

- `code/04-gamma-vector-build.sh` changes to `code/` and runs `pdflatex`
  on a nonexistent `code/article.tex`;
- `code/05-gamma-positivity-build.py` does the same after creating a stray
  `code/build/` directory.

Build this article as described above instead.

Run this way on 29 September 2026 (Python 3.14.4, Windows), both passed, in
about 19 s and 15 s. The regenerated CSV is byte-identical to
`data/05-gamma-positivity-preorders.csv`. The two JSON records differ from the
shipped ones only in timings, the Python version (the recorded runs used
3.13.5) and, for manuscript 06, the platform string. The console outputs
differ in the same fields and in the printed output path.

The batch-44 placement dossier also compared, independently of both
programs:

- for all 390 labeled preorders with `n ≤ 4`, a direct count of lattice
  points by support size with `Σ_k gamma_k t^k (1+t)^(n−2k)`;
- for all 4,165 reflexive relations with `1 ≤ n ≤ 4`, the endpoint
  formula `(|R|, |closure(R)|)` and the palindromic-iff-transitive
  criterion (Part I's Section 8.5 relation gives `(1,5,6,1)`).

There were no mismatches. The write phase recomputed the article's numerical
examples by brute force. None of these scratch checks is shipped
(Section 59.3).

**Parts V–VII: common hazards.** The four packages' programs are shipped
under prefixed names but still use their delivered names and layouts. Run
them only as below, from this directory in Git Bash or another POSIX shell,
with `W` a scratch directory outside the repository. On Windows every
program writes its JSON with CRLF line endings (Python's `write_text`
without `newline=`), so compare with the shipped LF files after
`tr -d '\r'`. Use `py` (or `uv run --no-project … python`); the delivered
READMEs and articles say `python` or `python3`. The delivered build scripts
and Makefile cannot build this article: `code/06-lorentzian-support-build.sh`
changes to `code/` and runs `pdflatex` on a nonexistent `code/article.tex`;
`code/07-support-polynomials-build.sh` creates `code/build/` and fails on
the unshipped `support_polynomials.tex`; `make -f code/09-matroid-lifts-Makefile`
run here would rebuild this article in place with `pdflatex` (target `pdf`,
leaving auxiliary files here), look for a nonexistent `verify.py` (target
`verify`), and delete `article.aux`, `.log`, `.out`, `.toc`, `.fls` and
`.fdb_latexmk` here (target `clean`). Do not run them here.

**Part V, source 06.** Standard library, Python 3.10 or later. The sampler
and the tests import `verify` and `support_sampler` under their delivered
names, so under the shipped names here `verify` would resolve to **Part I's**
`code/verify.py` (an `ImportError`, or a wrong module); and `verify.py`
without `--output` writes `results/verification.json` relative to the
working directory (in the delivered layout, its own recorded output).
Restore the delivered names in a copy:

```sh
W=/path/to/scratch
mkdir -p "$W/06/code" "$W/06/results"
for f in code/06-lorentzian-support-*.py; do cp "$f" "$W/06/code/${f#code/06-lorentzian-support-}"; done
cd "$W/06"
py code/verify.py --max-preorder 5 --output results/rerun.json     # ends with the JSON; compare with data/06-lorentzian-support-verification.json
py code/test_sampler.py                                            # 7 tests
py code/support_sampler.py --rows 14,3,5,9 --receivers 4 --samples 100 --epsilon 1/100 --seed 20260929 --output results/smoke.json
```

Run this way on 29 September 2026 (Python 3.14.4, Windows, on a shared
and loaded machine: about 150 s for the verifier; the recorded run took
11 s under Python 3.13.5), all three passed. After CR stripping,
`rerun.json` and the console output equal
`data/06-lorentzian-support-verification.json` and `.log` except `python`
and `elapsed_seconds`; the seven tests pass (the transcript differs only in
its time); `smoke.json` equals `data/06-lorentzian-support-sampler_smoke.json`
except `elapsed_seconds` (the same 100 supports for the seed). The shorter
check `--max-preorder 4 --skip-3x4` is the program's own option.

**Part V, source 07.** Standard library. `verify.py` and
`example_certificate.py` import `support_tools` under its delivered name, so
under the shipped names they fail with `ModuleNotFoundError`; `verify.py`
without `--output` writes `../data/verification.json` **relative to the
working directory** (from this directory that is
`enumerative-combinatorics/data/`, outside the report). Its checks are
`assert` statements: do not use `python -O`.

```sh
W=/path/to/scratch
mkdir -p "$W/07/code" "$W/07/rerun"
for f in code/07-support-polynomials-*.py; do cp "$f" "$W/07/code/${f#code/07-support-polynomials-}"; done
cd "$W/07"
py code/verify.py --output rerun/verification.json                 # compare with data/07-support-polynomials-verification.json
py code/example_certificate.py --output rerun/example_certificate.json
py code/support_tools.py
```

Run this way on 29 September 2026 (Python 3.14.4 on the loaded machine: the
verifier took 300 s; the recorded run took 22 s), all three passed. After CR
stripping, `verification.json` and the verifier's console output equal
`data/07-support-polynomials-verification.json` and `.log` except
`elapsed_seconds`; the certificate JSON and its console output are
byte-identical to the shipped `example_certificate.json` and `.log`;
`support_tools.py` prints the `Theta_3` coefficients, "Palindromic: False"
and one sampler step. Use `--quick` for the program's own 3×3 check.

**Part VI, source 08.** Needs SymPy 1.14.0 and NetworkX 3.6.1
(`data/08-ade-stability-requirements.txt`) and imports no sibling module.
Without `--output` it writes `data/verification_results.json` under the
parent of its own directory, which here is **Part I's recorded output**:
always pass `--output`.

```sh
W=/path/to/scratch; mkdir -p "$W/08"
uv run --no-project --with sympy==1.14.0 --with networkx==3.6.1 python code/08-ade-stability-verify.py --output "$W/08/ade.json"
tr -d '\r' < "$W/08/ade.json" | cmp - data/08-ade-stability-verification_results.json
```

Run this way on 29 September 2026 (uv with Python 3.13.5, SymPy 1.14.0,
NetworkX 3.6.1; about 25 s): "All exact checks passed", and the output is
byte-identical to the shipped JSON after CR stripping (it has no timing
field).

**Parts VI–VII, source 09.** Standard library; no sibling imports. Without
`--output` it writes `verification_results.json` in the working directory.

```sh
W=/path/to/scratch; mkdir -p "$W/09" && cp code/09-matroid-lifts-verify.py "$W/09/" && cd "$W/09"
py 09-matroid-lifts-verify.py --output out.json > console.txt
```

Run this way on 29 September 2026 (Python 3.14.4, about 11 s on the loaded
machine), it passed: after CR stripping, `out.json` and `console.txt` (the
program prints the JSON it writes) equal
`data/09-matroid-lifts-verification_results.json` and
`-verification_run.txt` except `elapsed_seconds`.

**Part VIII, source 10.** Needs NetworkX 3.6.1 (which requires Python ≥ 3.11)
and SymPy 1.14.0 (`data/10-marked-trees-requirements.txt`).
`10-marked-trees-verify.py` imports its library by the delivered name
`marked_trees`, so under the shipped names it fails with
`ModuleNotFoundError`; its default output `results/verification.json` is
relative to the working directory. Restore the delivered layout in a copy:

```sh
W=/path/to/scratch; mkdir -p "$W/10/code" "$W/10/results"
cp code/10-marked-trees-marked_trees.py "$W/10/code/marked_trees.py"
cp code/10-marked-trees-verify.py "$W/10/code/verify.py"
cd "$W/10"
uv run --no-project --with networkx==3.6.1 --with sympy==1.14.0 python code/verify.py --max-n 9 --output results/verification.json > console.txt
```

Pass `--max-n 9` explicitly: the program's default is 8 (see below). Run
this way on 30 September 2026 (uv with Python 3.13.5, on Windows, about
25 s; the recorded run took 10 s), it passed: `results/verification.json`
equals `data/10-marked-trees-verification.json` except `elapsed_seconds`,
and `console.txt` equals `data/10-marked-trees-run.log` except the path
separator in its last line ("Saved results\verification.json" on Windows).
That run wrote LF line endings.

**Part IX, source 11.** Standard library only (Python ≥ 3.10); use `py` or
`python3`. `11-two-flow-verify.py` imports its library by the delivered
name `transport_bijection`, so under the shipped names it fails with
`ModuleNotFoundError`; and it writes `data/<suite>.json` next to its own
`code/` directory, which in this report would add unprefixed files to
`data/`. Restore the delivered layout in a copy:

```sh
W=/path/to/scratch; mkdir -p "$W/11/code" "$W/11/data"
cp code/11-two-flow-transport_bijection.py "$W/11/code/transport_bijection.py"
cp code/11-two-flow-verify.py "$W/11/code/verify.py"
cd "$W/11"
py code/transport_bijection.py            # the worked example and one sample
py code/verify.py --suite all > console.txt
```

Run this way on 30 September 2026 (Python 3.14.4 on Windows, about 70 s;
the recorded run took about 29 s), it passed: after CR stripping, each
`data/<suite>.json` equals the shipped `data/11-two-flow-<suite>.json`
except `elapsed_seconds`, and `console.txt` equals
`data/11-two-flow-verification_run.txt` except `elapsed_seconds`. On
Windows both are written with CRLF line endings. The programmatic example
of the unshipped delivery README (sampling with `Random(20260930)`, a
three-element chain via `preorder_graph`) needs `code/` on the module path,
as in this copy.

None of these runs changed a file of this report (checked with
`git status` and by comparing a copy of `code/` and `data/`).

## Discrepancies and delivery names

- **Delivery names.** Part II's programs, Makefile and status notes use the
  delivered paths (`code/verify.py`, `code/verify_theta.py`,
  `code/direct_counterexample.cpp`, `data/*.json`, `data/board_certificate.csv`,
  `article.tex`, "the package"); the recipe above recreates them in a copy.
  The C++ source's header comment suggests running a binary at
  `/tmp/direct_preorder`. The article quotes the shipped names
  (Section 22.4). Likewise Part III's program says "Run from the package
  root" and writes `data/verification.json`, its Makefile names
  `code/verify.py` and `article.tex` in the package root, and
  `03-cactus-STATUS.md` / `03-cactus-SOURCES.md` speak of "this manuscript",
  "the article" and "this package" — the delivered 24-page manuscript and
  archive, which are not shipped (their content is Part III of
  `article.pdf`); the article quotes the shipped names (Section 40.3).
- **Unshipped files.** `02-height-two-STATUS.md` and `02-height-two-sources.md`
  speak of "the article" and "the package", meaning the delivered 26-page
  manuscript and archive, which are not shipped; their content is Part II of
  `article.pdf`. The delivered Makefile's `pdf` and `clean` targets name
  `article.tex` in the package root and a `build/` directory. Part III's
  delivery README (not shipped) lists `SHA256SUMS.txt` (verified and retired)
  and does not list `data/build_status.json`, which is shipped as
  `data/03-cactus-build_status.json`.
- **Part III's recorded outputs.** `data/03-cactus-verification_log.txt` is
  byte-identical to `data/03-cactus-verification.json` (the program prints the
  JSON it writes). `data/03-cactus-build_status.json` describes the delivered
  24-page US-Letter PDF ("final_compile_warnings": 0), not this article's
  build.
- **Stale delivered notes.** `02-height-two-STATUS.md` lists "A
  characterization of all graphs admitting the cactus-style matrix" as not
  established; Part III now gives it (Theorem 29.1). The file is delivered
  text and is left unchanged.
- **Part I's own files.** `STATUS.md` ("A proof of flag realizability,
  gamma-positivity, or real-rootedness" not claimed) and `PROOF_AUDIT.md`
  describe Part I at 20 September 2026 and are unchanged; for Conjectures
  5.2, 5.3 and 5.1(d) read Section 11.3 of the article. Part I's Appendix C
  describes Part I's original archive layout (with `build.py`).
  [Added 29 September 2026, batch 44: for Conjecture 5.2 read Section 46.3.]
- **Stale delivered status notes after Part IV** (all left byte-identical):
  - `STATUS.md` (Part I) lists gamma-positivity among what is not proved;
  - `02-height-two-STATUS.md` lists "General gamma-positivity for all
    preorders or for nontrivial block blowups" as not established;
  - `03-cactus-STATUS.md` lists "No solution of general preorder gamma
    positivity";
  - `02-height-two-sources.md` says the report leaves gamma-positivity
    unproved.

  Each was true of its own part, and of the report when it was written.
  Part IV now proves gamma-positivity for every finite preorder.
  `05-gamma-positivity-SOURCE_AUDIT.md` likewise describes the report at
  manuscript 06's pin, as Parts I and II only, "leaving general
  gamma-positivity and nontrivial equivalence-class blowups beyond its proved
  scope"; Part III already existed when the manuscript was placed.
- **Part IV's delivery names.**
  - `05-gamma-positivity-PROOF_STATUS.md` names "the article", its own
    theorem numbers (Theorem 2.2 → 48.2, Theorem 2.3 → 48.3, Lemma 3.1 →
    49.1, Lemma 4.1 → 50.1, Lemma 6.1 → 53.1) and `data/verification.json`
    and `data/verification.log` (shipped as `data/05-gamma-positivity-*`).
  - `05-gamma-positivity-SOURCE_AUDIT.md` speaks of "the present article",
    which is manuscript 06, printed as Part IV.
  - `code/04-gamma-vector-verify.py` gives the usage line
    `python3 code/verify.py --max-n 5 --output results/verification.json`,
    and `data/04-gamma-vector-verification.txt` ends "results written to
    results/verification.json".
  - Manuscript 06's program writes `preorders.csv` and `verification.json`
    into its output directory.
  - The two build scripts name `article.tex` beside themselves.
  - The unshipped delivery README of manuscript 01 lists `SHA256SUMS`
    (verified and retired), `article.pdf` and `article.tex`. The unshipped
    delivery README of manuscript 06 lists `article.pdf`, `article.tex` and
    `build.py` (the last shipped as `code/05-gamma-positivity-build.py`), and
    manuscript 06's Section 11.3 (Section 59.1 here, with a merge note) says
    the package contains `README.md`, the two notes, a build script and the
    PDF.
  - The article quotes the shipped names (Section 59).
- **Part IV's recorded outputs.** Manuscript 06's `verification.log` is its
  console transcript (it prints the 689-graph and cancellation summaries
  before the per-size lines). Manuscript 06's JSON counts 4,166 reflexive
  relations because it includes the empty relation at `n = 0`; the dossier's
  figure 4,165 excludes it. Manuscript 01's text file is its console output,
  not a copy of its JSON.
- **Part IV's two runs** were recorded under Python 3.13.5, manuscript 06's
  on Linux. Their stated times (about 11 s and 10 s) are properties of those
  runs.
- **Part I's equation numbers.** Part I prints two displays numbered (1.1)
  (a manual tag on the preorder polytope and the automatic number of the
  support polynomial); this predates the additions and is left as it was.
- **Self-citation.** Manuscripts 02 and 05 cited this report as an external
  repository report; those citations became internal references
  (Sections 11.4 and 26.4). Two of manuscript 05's section headings keep its
  wording "the repository". Batch 44's manuscripts 06 and 01 did the same;
  their citations became references to Parts I–III (Section 46.4), with the
  pins kept in Section 47.
- **Layout changes in the front matter.** Part III's abstract paragraph
  pushed Part I's scope box to page 2, so the page break between that box
  and the table of contents was removed (the contents now follow the box).
  Manuscript 05's equations, numbered (1)–(26) consecutively, are numbered by
  section here; its dependency ledger's second column is set ragged-right.

- **Parts V–VII's delivery names** (all shipped files left
  byte-identical):
  - `06-lorentzian-support-SOURCES.md` speaks of "the article" and "this
    package" (the delivered 23-page manuscript, printed in Part V), cites
    its own "Lemma 2.1" (Lemma 68.1 here) and "Section 7" (Section 75), and
    cites **Theorem 4.2** of Dai et al. for the augmented-root identity; the
    inspected arXiv v2 has it as **Theorem 1.2** (Section 66.4 of the
    article records the correction).
  - `07-support-polynomials-PROOF_STATUS.md` and `-SOURCES.md` speak of
    "the article", "this package" and "the predecessor" (Parts I–IV).
    `data/07-support-polynomials-build_validation.json` describes the
    delivered 23-page PDF's build (TeX Live 2025), not this article's.
  - `08-ade-stability-SOURCE_AUDIT.md` names `data/verification_results.json`
    (shipped as `data/08-ade-stability-verification_results.json`; the
    unprefixed name here is Part I's file) and "this delivery".
  - `09-matroid-lifts-CLAIMS_AND_SOURCES.md` cites the delivered section
    numbers (mapped above) and "the article".
  - The four programs' usage strings, console records and default paths use
    the delivered layout (`results/`, `data/`, package root); the article
    prints the delivered run commands, each followed by a merge note with
    the shipped names (Sections 78, 78.1, 95, 110).
  - The unshipped delivery READMEs list `SHA256SUMS.txt` (sources 06, 08,
    09; verified and retired), the manuscripts and the PDFs.
- **Parts V–VII's recorded outputs** were produced under Python 3.13.5
  (sources 06–09; source 07's and 09's JSON do not record the version) and
  contain an `elapsed_seconds` field (sources 06, 07, 09) that varies from
  run to run; source 08's JSON has version strings only.
- **Bylines.** Sources 06, 07 and 09 name ChatGPT on their title pages;
  source 08 names no assistant ("mathematical development and exposition
  with AI assistance"). The article's PDF metadata is unchanged.
- **Part VIII's delivery names and discrepancies** (all shipped files left
  byte-identical):
  - `code/10-marked-trees-verify.py` says in its docstring "Run: python
    code/verify.py --max-n 8 --output results/verification.json", and its
    `--max-n` default is 8; the delivery README, the article's table and the
    recorded run use `--max-n 9`.
  - It imports `marked_trees` (shipped as
    `code/10-marked-trees-marked_trees.py`), and `data/10-marked-trees-run.log`
    ends "Saved results/verification.json" (shipped as
    `data/10-marked-trees-verification.json`).
  - `code/10-marked-trees-build.sh` changes to its own directory, creates
    `code/build/` and runs `pdflatex` on a nonexistent `code/article.tex`,
    which fails: do not run it.
  - `10-marked-trees-SOURCE_AUDIT.md` gives line ranges of the pinned
    `article.tex`; Part VIII's preamble, front-matter and pointer additions
    moved Part VI's lines by 27 to 49 (Section 130 of the article maps the
    ranges to Part VI's sections). It names
    `code/08-ade-stability-verify.py` correctly and speaks of "the
    delivered article" (Part VIII).
  - The unshipped delivery README lists `article.pdf`, `article.tex`,
    `results/` and `SHA256SUMS.txt` (verified and retired), calls the PDF
    "the 24-page research article", and uses `python`; it notes that
    NetworkX 3.6.1 excludes Python 3.14.1.
  - The recorded run (Python 3.13.5) records `elapsed_seconds` 9.982.
- **Bylines (Part VIII).** Source 10's title page reads "Research prepared
  for Vladimir Reshetnikov / Mathematical development and exposition with
  ChatGPT", and its PDF metadata name ChatGPT; the article records this in
  Section 116.1 and does not reprint the byline.
- **Part IX's delivery names and discrepancies** (all shipped files left
  byte-identical):
  - `code/11-two-flow-verify.py` imports `transport_bijection` (shipped as
    `code/11-two-flow-transport_bijection.py`) and writes
    `data/small.json`, `data/four_by_three.json`, `data/preorders.json`,
    `data/random.json`, `data/chain.json`, `data/example.json` (shipped as
    `data/11-two-flow-<suite>.json`); `data/11-two-flow-verification_run.txt`
    itself names no paths.
  - `code/11-two-flow-build.sh` changes to its own directory and runs
    `pdflatex` three times on a nonexistent `code/article.tex`, which fails:
    do not run it. Source 11's file table called it a two-pass build; it
    runs three passes (a merge note in Section 151 records this).
  - `11-two-flow-PROOF_STATUS.md` numbers statements as in the delivered
    article (mapping above) and speaks of `data/`; `11-two-flow-SOURCE_AUDIT.md`
    gives the line interval 9510–9555 of the pinned blob (now Section 75.7,
    moved by the Part VIII and Part IX front-matter additions), speaks of
    "the delivered article", and its "Chapoton–Athanasiadis" heading
    reverses the author order of arXiv:2605.26916 (Athanasiadis–Chapoton,
    as the article prints it).
  - The unshipped delivery README lists `article.tex`, `article.pdf`,
    `README.md` and `data/*.json`, calls the PDF a "23-page article", and
    uses `python`.
  - The recorded run (`data/11-two-flow-environment.json`: Python 3.13.5,
    Linux) records `elapsed_seconds` per suite, which varies.
- **Bylines (Part IX).** Source 11's title page reads "Prepared for
  Vladimir Reshetnikov / Mathematical development and implementation:
  ChatGPT"; its PDF metadata read "AI-assisted research manuscript prepared
  for Vladimir Reshetnikov", and its delivery README "prepared for Vladimir
  Reshetnikov with ChatGPT". The article records this in Section 132.1 and
  does not reprint the byline.
- **Merge observations not in any source** are marked as such in the
  article: the #P-hardness of a specified height-two `gamma_k`
  (Corollary 76.4), the infinitely many induced-minimal unstable graphs
  (Section 92.6), `p_{B_m} = p_{Theta_m} + u` (Section 90), a finite search
  on normalization by the matching number (Research question 37), the tree
  diagonals for `r ≤ 12` (Section 96), and the comparison with the q-zeta
  report's matroid (Section 106). Their finite checks were run by the
  batch-55 dossier and write phase and are not shipped. Part VIII adds
  one: the first proof of Theorem 118.2, assembled from Part VI's theorems
  (Section 118). Its bibliography has a second McKee–Smyth entry: source 10
  cites arXiv:0907.0371, a different paper from Part VI's arXiv:2002.06082.

## Relation to neighbouring reports and to the formal projects

Three other preorder reports in `enumerative-combinatorics/` concern the same
paper of Athanasiadis–Chapoton but different polynomials and questions:
`preorder-polytope-reciprocity` (reciprocity and matrix duality),
`preorder-shellability` (a shelling for Question 4.6) and
`preorder-q-zeta-reciprocity` (support reciprocity and the q-zeta
polynomial). Each lists real-rootedness and gamma-positivity only as not
addressed, and none addresses Conjectures 5.1(d)–5.3 for the support
polynomial `h_tau` (the q-zeta report states that its `H_tau` is a different
polynomial), so no reciprocal note was written. Part III concerns bipartite
graphs and matrices only; none of those reports treats cactus matrices or
stability. Batch 42's manuscript 04, placed in
`ordinals-and-order-types/wqo-powersets-and-statures/cofinal-strata-of-finitary-powersets`,
also speaks of "height two" and of (uniquely restricted) matchings, but it
concerns ordinal heights of downsets and shares no theorem with this report.
Part IV (batch 44) proves gamma-positivity for every finite preorder. The
three neighbouring preorder reports' remarks that they do not establish
gamma-positivity describe their own proofs and stay accurate. The q-zeta
report's `H_tau` is a different polynomial, and none of those reports
states Conjecture 5.2 as open. So Part IV adds no reciprocal note there
either; the catalogue step may mention Part IV in the collection's entries.
Parts V–VII (batch 55) touch one neighbour: the q-zeta report's
transversal matroid `M_B` (its "Tutte evaluation" proposition) agrees, for
all 5,930 pairs `(tau, B)` with `n ≤ 4`, with the minor
`(M_{tau^op}/B^-) ∖ (E∖B)^-` of Part VII's matroid (a finite check recorded
in Section 106 of the article, not a theorem; no note was added to that
report in this batch). Part VI continues Parts II–III's stability questions
only; the other neighbours treat neither stability nor log-concavity.
Part VIII (batch 63) continues Part VI only; it touches no neighbouring
report, and no reciprocal note was written. Part IX (batch 64) continues
Parts II, IV, V and VII; its dated pointers are inside this report. The
neighbouring preorder reports sample no lattice points (their "samples"
are random test relations), and their bijection questions concern other
objects (the two binomial expansions of `preorder-polytope-reciprocity`,
the sets `B_tau(T)` of `preorder-q-zeta-reciprocity`), so no reciprocal
note was written.

The report sits in the research-report collection of the `SetTheory/Cardinals`
Lean project. That placement confers no formal status: no Lean or Rocq
declaration in ProveIt formalizes any statement of Parts I–III (a search of
the repository's `.lean` and `.v` files for Ehrhart, root-polytope,
matchable-set, support-polynomial, gamma-positivity and real-rootedness terms
finds nothing about preorder polytopes, and a search of the tracked `.lean`
and `.v` files for cactus, superregular, real-stable and matchable finds
nothing). Sections 23 and 41.3 record the formalization plans the manuscripts
propose; none of them has been started. The same holds for Part IV: a search
of the tracked `.lean` and `.v` files for gamma-positivity, Athanasiadis,
matchable, root-polytope, preorder-polytope and transport-pair terms finds
nothing, and Part IV's two formalization plans (Section 60) are unstarted.
The same holds for Parts V–VII: no declaration formalizes any of their
statements (a search of the tracked `.lean` and `.v` files outside `lib/`
for matroid, bimatroid, gammoid, Lorentzian, ultra-log-concave, Dynkin,
real-stable, matchable, incidence–apex and multi-theta finds nothing), and
their formalization plans (Sections 79.3 and 95.4, and Section 111) are
unstarted. The same holds for Part VIII: a search of the tracked `.lean` and
`.v` files for matching-support, incidence–apex, Dynkin and marked-tree
terms finds nothing, and its formalization boundary (Section 127.3) and
Research question 65 describe unstarted work. The same holds for Part IX:
a search of the tracked `.lean` and `.v` files outside `lib/` for
transportation-polytope, min-cost-flow, demand-vector, transversal-matroid
and Hall-marriage terms finds nothing (the only "hall" hits are unrelated
hypothesis names in `Algebra/PolynomialFormulas`), and its formalization
plan (Section 147.3) and Research question 73 are unstarted.

## Sources and attribution

- C. A. Athanasiadis and F. Chapoton, *Polytopes and posets associated to
  preorders*, arXiv:2605.26916v1 — the conjectures (Section 5).
- Z. Dai, Q. Hou, Z. Liu, W. Thawinrak and H. Wang, arXiv:2608.16037v2 — the
  support-enumerator/root-polytope identity and duality (credited in Part I).
- T. Kálmán and A. Postnikov, arXiv:1602.04449 — hypertrees and root polytopes.
- H. Ohsugi and A. Tsuchiya, arXiv:1810.12258 and arXiv:2008.08621; R. Davis
  and F. Kohl, arXiv:2207.14759 — the matching-support Ehrhart numerator, the
  classical nonreal-rooted graph polynomial, univariate cactus
  real-rootedness and the cycle formula (credited in Parts II and III).
- J. R. Stembridge, Trans. AMS 359 (2007) — the width-two poset behind the
  17-element example.
- **S. Patel, MathDB posting — the eight-element counterexample to
  Conjecture 5.3** (credited in Part II; see the box at the top).
- P. Brändén, Adv. Math. 216 (2007), arXiv:math/0605678 — the multiaffine
  Rayleigh criterion (Theorem 5.6) behind Part III's `K_{2,3}` stability.
- P. J. Almeida, D. Napp and R. Pinto, arXiv:1601.02960 (superregular
  matrices); M. Baker, C. Ding and X. Zhuang, arXiv:2308.11760 (sixth-root
  matroids); S. Burton, C. Vinzant and Y. Youm, arXiv:1411.2038 (stability
  without determinants); M. Nakamura, Graphs Combin. 5 (1989) (binary
  fundamental transversal matroids) — terminology and context for Part III.
- K. Menon, arXiv:2608.13247v1 — bijective gamma-positivity for octopuses and
  lopsided octopuses; the octopus formula, attributed there to Athanasiadis,
  Xiao and Yan, is recovered and credited in Part IV (Part I cites the paper
  as special cases of gamma-positivity).
- Part IV's inputs are the Kálmán–Postnikov, Ohsugi–Tsuchiya (arXiv:1810.12258v4,
  Propositions 3.3–3.4), Davis–Kohl (Theorem 3.10) and Dai et al.
  (Theorems 1.2–1.3, Problem 5.3) entries above, and Part II's counting lemma.

- Parts V–VII: F. Röhrle and M. Ulirsch, Ann. Comb. 30 (2026) 501–523,
  doi:10.1007/s00026-025-00780-z, arXiv:2402.15317 (Theorems A and E,
  Proposition 2.2, Example 2.4); P. Brändén and J. Huh, *Lorentzian
  polynomials*, Ann. Math. 192 (2020), arXiv:1902.03719v8; N. Anari, K. Liu,
  S. Oveis Gharan and C. Vinzant, arXiv:1811.01816 (basis-walk mixing and
  FPRAS); E. Balas and W. R. Pulleyblank, Networks 13 (1983), and K. Mori,
  Graphs Combin. (2023) (the transversal-matroid model); S. Oh, Electron.
  J. Combin. 20(3) (2013) P14; C. J. Colbourn, J. S. Provan and D. Vertigan,
  Combinatorica 15 (1995) (#P-completeness); Y.-B. Choe, J. G. Oxley,
  A. D. Sokal and D. G. Wagner, Adv. Appl. Math. 32 (2004) (half-plane
  property); J. McKee and C. Smyth, arXiv:2002.06082 (ADE context);
  A. W. Ingleton and M. J. Piff, J. Combin. Theory Ser. B 15 (1973)
  (gammoids).
- Part VIII: J. McKee and C. Smyth, *Integer symmetric matrices of small
  spectral radius and small Mahler measure*, arXiv:0907.0371 (spectral
  context); M. Kummer and B. Sert, *Matroids on eight elements with the
  half-plane property and related concepts*, SIAM J. Discrete Math. 37
  (2023) 2208–2227, arXiv:2111.09610; with Choe–Oxley–Sokal–Wagner and
  Brändén above.
- Part IX: S. Oh, Electron. J. Combin. 20(3) (2013) P14, doi:10.37236/2769
  (source 11 inspected arXiv:1005.5586v3, Section 4, Remark 4.4 and
  Proposition 4.5) — the demand/base correspondence; G. Loho and B. Smith,
  *Matching fields and lattice points of simplices*, Adv. Math. 370 (2020)
  107232, doi:10.1016/j.aim.2020.107232, arXiv:1804.01595v4 (new to this
  report; related lattice-point bijections); N. Anari, K. Liu, S. Oveis
  Gharan and C. Vinzant, Ann. of Math. 199 (2024) 259–299,
  doi:10.4007/annals.2024.199.1.4 (Theorem 1.1 of arXiv:1811.01816v3,
  imported); Ohsugi–Tsuchiya and Athanasiadis–Chapoton above.

No third-party papers or font files are included.
