# Aligned Fragments and Constrained Crossover

**Undecidability, exact generation depth, and rational growth of context-free recombination closures; with Part II, PSPACE-complete finite stabilization of regular seeds, and Part III, decidable regularity and exact stabilization of crossover closures**

This is a research report in three Parts, built from three manuscripts.
Part I (29 September 2026) answers a question that Charles E. Hughes left
open in arXiv:2608.27755v1: the complexity of deciding `L ⊗_c L = L` for a
context-free language `L`, where `⊗_c` is constrained crossover (see "Which
question of Hughes" below). Parts II and III (both 30 September 2026, batch
66) continue it: Part II locates finite stabilization of regular seeds
exactly (PSPACE-complete for NFA input), and Part III decides regularity of
the full closure of context-free seeds and classifies sparse one-marker
seeds. All three are AI-assisted research drafts; their title pages and PDF
metadata name ChatGPT as the drafting assistant and Vladimir Reshetnikov as
the person they were prepared for (Part I: "Research draft prepared with
ChatGPT for Vladimir Reshetnikov"; Part II the same; Part III "Research
manuscript prepared with ChatGPT for Vladimir Reshetnikov"). That wording
stays on Part I's title page and in this provenance record only.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 44, manuscript 02 | `ProveIt_Constrained_Crossover` (arrived in `ae28ea2db`; 23-page US-letter PDF) | `9b24a3a8d` | `203016015` | Part I: Sections 1-12 and Appendices A-D, apart from text marked `[write]` |
| 02 | batch 66, manuscript 01 | `ProveIt_Crossover_Stabilization` (*Finite Crossover Stabilization Is PSPACE-Complete: periodic interior universality, quadratic rank bounds, and linear-growth obstructions*; arrived in `9ad899cbe`; 23-page US-letter PDF) | `b8b0fa218` | `4fee1cd07` | Part II: Sections 13-28 |
| 03 | batch 66, manuscript 03 | `ProveIt_Crossover_Classification` (*Decidable Regularity and Exact Stabilization of Crossover Closures: arithmetic invariants, sparse-marker trichotomies, and immediate loss of context-freeness*; arrived in `9ad899cbe`; 23-page US-letter PDF) | `b8b0fa218` | `4fee1cd07` | Part III: Sections 29-45 |

The pins are ProveIt commits `9b24a3a8d545af9624f6ac455f5b548be62818b6`
(source 01, recorded in its Section 1.1 and in `provenance.md`) and
`b8b0fa2184a044d46ce9ed0f25f88d7bb60fa042` (sources 02 and 03, recorded in
Sections 14.1 and 30.1 and in their audit notes). At `b8b0fa218` Part I's
`article.tex` had the blob `eb4f427f`, which is also the blob at the
placement commit `4fee1cd07`, so everything the two batch-66 manuscripts
say about "the inspected report" refers to Part I as printed. They were
written in parallel and do not cite each other.

**Status.** AI-assisted and unrefereed. **Not formalized**: no statement of
any Part has a Lean or Rocq proof, and none of the manuscripts claims one.
The finite computations are exact audits of finite specializations, not
proofs of the universal statements. The report sits in a repository with
Lean and Rocq developments; that placement gives it no formal status (see
"Formal status" below).

```
article.tex        the report, standalone LaTeX with an internal bibliography (pdfLaTeX)
article.pdf        the compiled report, 78 US-letter pages (unnumbered title page, contents pp. 1-3,
                   Part I Sections 1-12 pp. 4-26, Part II Sections 13-28 pp. 27-49,
                   Part III Sections 29-45 pp. 50-73, Part I's Appendices A-D pp. 74-76,
                   references pp. 76-77)
README.md          this guide
provenance.md      Part I: the manuscript's source record and bounded novelty audit, as delivered
proof-audit.md     Part I: the manuscript's author-side proof and edge-case audit, as delivered
02-pspace-stabilization-proof-audit.md      Part II: claim-dependency and edge-case audit, as delivered
02-pspace-stabilization-source-ledger.md    Part II: pinned-repository and primary-source record, as delivered
03-closure-classification-proof-audit.md    Part III: dependency structure and boundary cases, as delivered
03-closure-classification-provenance.md     Part III: repository pin, literature and novelty audit, as delivered
code/verify.py     Part I: exact finite reference verifier (Python >= 3.10, standard library only)
code/Makefile      Part I: the delivered Makefile (pdf, check, clean; see below)
code/02-pspace-stabilization-verify.py      Part II: exact finite reference solver and audits (486 lines, standard library)
code/02-pspace-stabilization-example.py     Part II: small use of that solver (imports it as `verify`)
code/02-pspace-stabilization-build.sh       Part II: the delivered LaTeX build script
code/03-closure-classification-crossover_masks.py  Part III: exact ray analyzer (206 lines, standard library)
code/03-closure-classification-verify.py    Part III: exact finite audit (158 lines; imports the analyzer as `crossover_masks`)
code/03-closure-classification-Makefile     Part III: the delivered Makefile (pdf, check, examples, clean)
data/verification.json   Part I: the delivered receipt, PASS, 1,766,639 checks
data/verification.txt    Part I: console output of the delivered run
data/02-pspace-stabilization-verification.json  Part II: the delivered receipt, PASS (Python 3.13.5)
data/02-pspace-stabilization-verification.txt   Part II: console transcript of that run
data/02-pspace-stabilization-build-receipt.json Part II: the delivered PDF build record (23 pages, no formal verification)
data/03-closure-classification-verification.json    Part III: the delivered receipt, PASS, 12,867 checks (Python 3.13.5)
data/03-closure-classification-verification.txt     Part III: the same bytes as the JSON receipt (the delivered stdout copy)
data/03-closure-classification-artifact-validation.json  Part III: the delivered PDF/source validation record
data/03-closure-classification-<name>.json         Part III: five ray inputs (endpoint_cycle5,
data/03-closure-classification-<name>.result.json   finite_point_exception, five_markers,
                                                    incompatible_velocities, two_markers) and their analyses
```

All shipped code, data and notes files are byte-identical to the
deliveries. Delivery names and shipped paths:

- **Part I:** `notes/provenance.md` -> `provenance.md`,
  `notes/proof-audit.md` -> `proof-audit.md`, `Makefile` -> `code/Makefile`;
  `code/verify.py` and `data/verification.{json,txt}` keep their delivered
  paths. The package had no checksum ledger.
- **Part II:** `notes/proof-audit.md` -> `02-pspace-stabilization-proof-audit.md`,
  `notes/source-ledger.md` -> `02-pspace-stabilization-source-ledger.md`,
  `build.sh` -> `code/02-pspace-stabilization-build.sh`, `code/verify.py` and
  `code/example.py` -> `code/02-pspace-stabilization-{verify,example}.py`,
  `data/verification.{json,txt}` and `data/build-receipt.json` ->
  `data/02-pspace-stabilization-*`. The package had no checksum ledger.
- **Part III:** `notes/proof-audit.md`, `notes/provenance.md` ->
  `03-closure-classification-{proof-audit,provenance}.md`, `Makefile` ->
  `code/03-closure-classification-Makefile`, `code/crossover_masks.py` and
  `code/verify.py` -> `code/03-closure-classification-*`,
  `data/verification.{json,txt}` and `data/artifact-validation.json` ->
  `data/03-closure-classification-*`, `examples/<name>.json` and
  `examples/<name>.result.json` -> `data/03-closure-classification-<name>.json`
  and `...-<name>.result.json`. Its checksum list `SHA256SUMS` (21 entries,
  all verified at placement) was retired by repository policy.
- **Not shipped**, for all three: the delivered `article.tex` (printed in the
  report), `article.pdf` (this directory's PDF is a build of the written
  `article.tex`) and `README.md` (replaced by this file). They survive in the
  arrival commits `ae28ea2db` and `9ad899cbe`.

Delivered files whose text still uses delivery names or describes the
package rather than this report:

- `code/Makefile` runs `python3 code/verify.py` and `latexmk` on
  `article.tex` from the package root; see "Building" and "Rerunning".
- `code/verify.py` writes its receipt to `../data/verification.json`
  relative to its own directory, that is, **over Part I's shipped receipt**
  when run in place.
- **`code/02-pspace-stabilization-verify.py` has the same default output
  path, `../data/verification.json`, so run in place without `--output` it
  also overwrites Part I's receipt.** It uses `assert` for some checks (its
  delivered README says to run ordinary Python, not `python -O`).
- `code/02-pspace-stabilization-example.py` does `from verify import NFA,
  Periodic`, which fails beside the prefixed file; its comment calls the
  parity language "article Example 9.3", which is Example 22.3 here.
- `code/02-pspace-stabilization-build.sh` changes to its own directory
  (`code/`) and runs `latexmk` on an `article.tex` there; there is none.
- **`code/03-closure-classification-verify.py` always writes
  `../data/verification.json` relative to its own directory (over Part I's
  receipt) and imports `crossover_masks`, which fails beside the prefixed
  file.** `code/03-closure-classification-Makefile` runs `code/verify.py`
  (in this report Part I's verifier), `code/crossover_masks.py`,
  `examples/*.json` and `latexmk` on `article.tex`.
- `data/verification.txt` ends with the receipt path of the delivered run
  (`/mnt/data/ProveIt_Constrained_Crossover/data/verification.json`), and
  `data/02-pspace-stabilization-verification.txt` with
  `/mnt/data/ProveIt_Crossover_Stabilization/data/verification.json`.
- `data/02-pspace-stabilization-build-receipt.json` and
  `data/03-closure-classification-artifact-validation.json` describe the
  delivered 23-page PDFs, which are not shipped; the latter's `pdf_sha256`
  and `tex_sha256` identify the delivered PDF and source, not this report's
  files.
- `02-pspace-stabilization-proof-audit.md` cites "Section 2", "Section 3",
  "Sections 4-5" and `../data/verification.{json,txt}` of the delivered
  package. Section and theorem numbers of the manuscripts shift by a
  constant in the report: manuscript 02's Section `n` is Section `n + 13`
  (its Theorem 5.3 is Theorem 18.3), its Appendices A and B are Sections 27
  and 28; manuscript 03's Section `n` is Section `n + 29`, its Appendices A
  and B are Sections 44 and 45.
- `provenance.md`, `02-pspace-stabilization-source-ledger.md` and
  `03-closure-classification-provenance.md` speak of "this package" or "this
  delivery", say no repository file was edited (true of the deliveries, not
  of the write phase), and `03-closure-classification-provenance.md` says
  it was "Prepared ... for the user's request".
- The article's Section 10.2 lists Part I's delivered package layout, and
  Sections 23 and 45 those of Parts II and III; `[write]` notes there give
  the shipped paths.

## Labels

Every label carries the prefix `ccc:`; Part II's carry `ccc:ps:` and Part
III's `ccc:cl:`. **236 labels in total** (pattern `\label(\[[^]]*\])?\{`,
no `\label[...]` form occurs):

- **Part I, 80.** The 76 labels of the batch-44 write, unchanged: none was
  renamed or removed, and a comparison of the `.aux` files of the committed
  and the new build shows every one of them with the same number. Four
  labels were added in batch 66 to existing questions so that the new Parts
  can cite them: `ccc:q:regular` (Question 11.2), `ccc:q:grammar` (11.4),
  `ccc:q:series` (11.6), `ccc:q:restricted` (11.7).
- **Part II, 76** (`ccc:ps:`): all 71 labels of manuscript 02, prefixed,
  every `\ref` and `\eqref` updated; five new (`sec:provenance`,
  `sec:source`, `sec:abstract`, `sec:notation`, `sec:conclusion`).
- **Part III, 80** (`ccc:cl:`): all 66 labels of manuscript 03, prefixed;
  nine new on its nine unlabelled research questions (`q:nonsparse`,
  `q:grammarcomplexity`, `q:explicit`, `q:minimal`, `q:arithmetic`,
  `q:approx`, `q:markers`, `q:obstructions`, `q:certificates`) and five new
  sections as in Part II.

The raw manuscripts collided with each other (`app:audit`, `eq:hull`,
`sec:examples`, `sec:hardness`, `sec:questions`) but not with Part I; the
sub-prefixes remove the collisions. Before batch 66 the count was 76.

## Which question of Hughes

Charles E. Hughes, *Undecidability of Adjacent Equality for Insertion,
Shuffle, and Crossover Language Operations*, arXiv:2608.27755v1 (27 August
2026; 13 pages, printed page numbers equal to PDF page numbers). Checked
against that PDF when Part I was written:

- Section 2 ("Definitions and Notations", p. 2) defines unconstrained
  crossover `⊗_u` and constrained crossover `A ⊗_c B = {wz, yx : wx ∈ A,
  yz ∈ B, |w| = |y|, |x| = |z|}`, the operation of this report (same
  symbol).
- **Section 4 ("Foundational Results"), under "Single step equality"**:
  Theorem 1 and its Corollary make single-step equality undecidable for
  operators that contain concatenation (simple insertion, shuffle,
  unconstrained crossover). The note after the Corollary (p. 3) says that
  constrained crossover fails this criterion, so the complexity of the
  question "does L ⊗_c L = L?" is open; the list of open questions that
  follows repeats it for a context-free `L` (its second item, top of p. 4).
  This is the question Part I answers (its Theorem 4.2).
- Section 14 (p. 12) lists "Study constrained crossover" among its open
  directions without a specific question; Part I's `[write]` note after
  Question 11.9 says how its results bear on Hughes's other Section 13-14
  questions (for crossover only), and a batch-66 note there adds Parts II
  and III.

The delivered abstract of Part I says "Section 4", and its delivered README
and bibliography say "printed page 3"; both are correct. Parts II and III
cite the same version (v1) for the definition only; neither claims a second
answer to Hughes's question.

## What is claimed

Constrained one-point crossover: equal-length parents exchange suffixes at
the same cut (endpoint cuts allowed); `T(L) = L ⊗_c L`, parallel iterates
`L^[k]`, frozen-source iterates `Y_k` (one parent always from `L`).

**Part I** (source 01):

- **Exact rank calculus** (Section 3): the aligned-fragment rank satisfies
  `rank_{T(L)}(w) = ⌈rank_L(w)/2⌉` (Theorem 3.2); `L^[k] = {w : rank ≤ 2^k}`,
  depth `⌈log₂ rank⌉`, and the union of all generations is the coordinate
  hull (Theorem 3.3); the ranks on a slice have no gaps (Theorem 3.4); sharp
  slice stabilization by `⌈log₂ n⌉` (Corollary 3.5, Example 3.6,
  Corollary 3.7); frozen-source depth `rank − 1` (Theorem 3.8).
- **One-step undecidability** (Theorem 4.2): deciding `L ⊗_c L = L` for a
  context-free grammar is co-r.e.-complete, already over `{0,1,@}`, even on
  a family whose first generation is universal; no computable bound on
  shortest counterexamples (Corollary 4.3). This answers Hughes's question.
- **Finite stabilization** (Section 5): exact rank `r + 1` for `r` repeated
  forbidden blocks (Theorem 5.1); eventual stabilization undecidable over
  `{0,1,@,#}`, each fixed adjacent equality co-r.e.-complete (Theorem 5.2;
  frozen-source version Corollary 5.3); the eventual-stabilization set is in
  `Σ⁰₂` and `Π⁰₁`-hard (Proposition 5.4).
- **Fixed target** (Proposition 6.1): rank and generation of one word are
  computable in `O(g n^5)` time from a CNF grammar.
- **Regular inputs** (Section 7): a polynomial DFA one-step test with
  counterexamples of length at most `2s³ − 1` (Theorem 7.1); PSPACE-complete
  one-step problem for NFAs over a fixed ternary alphabet (Theorem 7.2); a
  distance automaton with at most `s·4^s` states whose value is rank − 1
  (Theorem 7.3); finite stabilization decidable, with an EXPSPACE upper bound
  for DFA input that is not claimed optimal (Corollary 7.4). *Batch 66:*
  Part II improves this bound to PSPACE for NFA and DFA input and proves
  PSPACE-completeness for NFA input (below; unrefereed, not formalized). The
  EXPSPACE bound remains a true, weaker statement; a dated note after
  Corollary 7.4 says so.
- **Counting** (Section 8): the full closure of every context-free seed has
  an effectively rational commutative generating function, commuting letter
  weights retained (Theorem 8.3, Corollary 8.4).
- **Non-context-free closure** (Section 9): the binary linear seed `S_q`
  (`q ≥ 3`) has a non-context-free closure `K_q` (Theorem 9.2) with
  `|(K_q)_n| = 4^⌊n/q⌋` and exact generation counts (Theorem 9.3); the
  minimal recurrence order of generation `k` is `q·2^k + 1`, and `q(k+1) + 1`
  for the frozen source (Theorem 9.4).
- **Audit** (Section 10.1): 1,766,639 exact checks, all passing: all 65,814
  binary seed sets of lengths 0-4 (1,050,698 target-rank queries), all 64
  complete two-state binary DFAs (8,128 queries), 255 guard repairs, block
  amplification for 1-64 blocks, the linear-seed family for `q = 3..7` up to
  length 12, and 25 recurrence pairs.

**Part II** (source 02), for a language given by an `s`-state NFA, with
`m = s+2`, `T_s = 2m² + 2m`, `p_s = lcm(1..m)`, `B_s = (2s+5)²`:

- **Main theorem** (Theorem 14.1): finite stabilization of parallel, and of
  frozen-source, self-crossover is in PSPACE and PSPACE-complete over a fixed
  binary alphabet, even for factorial languages with universal hull; if it
  stabilizes, every hull word has rank at most `B_s`, so the parallel clock
  stabilizes by `⌈log₂ B_s⌉` and the frozen one by `B_s − 1`; if not, the
  maximum rank is between `cn − C` and `n` on all large lengths of some
  residue class mod `p_s`; for DFA input a safe-core criterion decides it,
  with interior obstructions of length at most `p_s s²`.
- The steps: exact-length fragment criterion for NFAs (Lemma 16.1); common
  quadratic transient and period, from To's corrected unary theorem
  (Lemma 17.1); interior-universality criterion with `R(L) ≤ 2t + 1`
  (Theorem 18.3); pumping of one obstruction into linear rank
  (Theorem 18.4); residue-wise bounded/linear dichotomy (Corollary 18.5);
  short obstructions (Lemma 19.1), the PSPACE upper bound via Savitch
  (Theorem 19.2), the uniform cutoff (Corollary 19.3) and witness lengths
  (Corollary 19.4); binary hardness from Kao-Rampersad-Shallit's Lemma 6
  (Lemma 20.1, Theorem 20.2, Corollary 20.3: two letters is the least
  alphabet); a four-letter delimiter variant (Proposition 20.4); the safe
  core (Theorem 21.2, Corollary 21.3) and why it fails for NFAs
  (Example 21.4); the one-`1` family `L_m` showing that the `Θ(log s)` order
  of the parallel bound is sharp (Theorem 22.1); Examples 22.2-22.3.
- **Audit** (Section 23): PASS on all 4,096 two-state binary NFAs (3,720
  stabilizing, 376 not), all 5,832 complete three-state binary DFAs (5,768 /
  64), 258,048 independent rank comparisons and further families listed in
  its table; overlapping categories, not to be summed.

**Part III** (source 03):

- For context-free seeds: inclusion, equality and eventual equality of full
  closures are decidable (Theorem 32.1), as are Boolean-combination length
  sets (Theorem 32.3); the full closure is regular exactly when every
  position support has finite row type, which is decidable, with DFA
  synthesis (Theorem 33.1) or an effective infinite obstruction
  (Theorem 33.2).
- For binary one-marker seeds `L_R = 0* ∪ {0^i 1 0^j : (i,j) ∈ R}`: every
  generation is the set of hull words with at most `2^g` ones (frozen:
  `g + 1`), with exact depths and binomial slice counts (Theorem 34.3,
  Corollary 34.4); for semilinear `R`, finite stabilization holds exactly
  when the periods of each component are collinear, and `R` then normalizes
  to rays and points (Theorem 35.1); in that case the hull and generations
  are regular (endpoint velocities), linear context-free and non-regular (one
  co-occurring interior velocity), or not context-free from generation 1 on
  (two distinct compatible interior velocities) (Theorem 37.1,
  Corollary 37.2).
- For ray input: the maximum marker count is a clique number of a
  congruence graph (Theorem 38.2); every graph is realized by vertical rays
  with regular seed and hull (Lemma 39.1); deciding `K(R) ≥ k` is
  NP-complete and stabilization by an input depth coNP-complete, for
  binary-encoded rays (Theorem 39.2).
- A binary linear seed whose closure is reached in one step, is not
  context-free, and has the generating function `(1+z+4z²)/(1−z³)`
  (Theorem 40.1); a family realizing every finite depth (Theorem 40.2).
- **Audit** (Section 41.2): 12,867 exact checks, all passing, including all
  1,099 labelled graphs on 1-5 vertices.

## What is not claimed

**Part I**, kept from the manuscript: an unrefereed draft, not a
proof-assistant development; the bounded literature search is not a
priority claim, and equivalents in recombination, splicing or
genetic-algorithm literature have not been excluded; the coordinate-hull
(product) observation is not claimed as a first discovery; CFG universality,
effective Parikh semilinearity, Presburger counting (Woods) and
distance-automaton limitedness (Kirsten) are imported, not reproved; the
guard construction alone cannot prove undecidability of eventual
stabilization; `Σ⁰₂`-completeness is not claimed (Question 11.1); the
EXPSPACE bound is not claimed optimal (Part II now improves it; see above)
and the `O(g n^5)` bound not optimal; rationality of the commutative series
implies neither regularity nor context-freeness of the closure; the finite
audits do not implement a general CFG compiler, Presburger counting engine
or limitedness solver, and the executable verifier specializes to finite
seeds and DFAs; the research questions other than Hughes's are not asserted
to be new or globally open; the Lean section is a plan. Part I does not
solve the both-singleton insertion conjecture and does not reprove the
sibling report's spectrum realizations. Its results for crossover answer
none of Hughes's questions about insertion or shuffle.

**Part II**, kept from manuscript 02: unrefereed, no Lean or Rocq; priority
not asserted (targeted literature audit against a pinned revision); To's
corrected unary progression theorem, Kao-Rampersad-Shallit's Lemma 6 and
Savitch's theorem are imported, not reproved; Part I's rank calculus is
credited and reproved, not claimed; **the exact complexity for DFA input is
not determined** (Question 24.1), nor the optimal rank bound (24.2, known
only between `⌊(s−3)/2⌋` and `(2s+5)²`) or the residue-wise slopes; the
safe-core algorithm is polynomial only in the expanded period, not in the
DFA; the four-letter delimiter reduction is credited to Part I's amplifier;
the reference solver stores explicit graphs and is not an implementation of
the polynomial-space bound; finite audits prove no universal statement and
do not infer PSPACE-hardness.

**Part III**, kept from manuscript 03: unrefereed, no Lean or Rocq; global
priority not established; Parikh semilinearity, Presburger definability,
monadic decomposition and the slender-language (paired-loop) background are
classical, and CLIQUE hardness is imported; the regularity procedure has no
polynomial bound in the grammar; the closure procedures do not compare the
seeds themselves or solve eventual stabilization for arbitrary grammars;
**no general context-freeness decision for nonsparse Presburger hulls**
(Question 42.1); the NP/coNP results are for binary ray input and a variable
threshold, **not for explicit DFAs** or fixed depths; the analyzer implements
no CFG compiler, Presburger solver, semilinear normalization or DFA
synthesis; the global-regularity question is not attributed to a numbered
open question by the manuscript. (The write notes that it partly answers
Part I's Question 11.4; the manuscript itself makes no such claim.)

## Questions answered or re-scoped by the batch-66 Parts

Dated notes (`[Added 30 September 2026, batch 66: …]`) record these in the
article; no question is printed as open where a Part answers it.

- Part I's **Question 11.2** ("Sharp regular-input complexity"): answered for
  NFAs (PSPACE-complete over two letters, Corollary 20.3); for DFAs Part II
  gives PSPACE (Theorem 19.2) and a safe-core criterion (Theorem 21.2); the
  exact DFA complexity stays open (Part II's Question 24.1).
- Part I's **Corollary 7.4**: EXPSPACE improved to PSPACE (Theorem 19.2).
- Part I's **Question 11.4** ("Grammar classes preserving context-freeness"):
  partly answered by Part III (regularity decidable for every context-free
  seed; complete classification for finitely stabilizing semilinear
  one-marker seeds); open in general (Part III's Question 42.1).
- Part I's **Question 11.6** ("Which rational counting series occur?"): Part
  III adds examples only.
- Part I's Questions 11.1 and 11.7 stay open; Part II's Questions 24.6 and
  24.7 restate or extend them (24.6 is printed as a pointer to 11.1).
- Part III's **Question 42.3** (explicit automata versus succinct rays):
  answered for NFAs by Part II; its DFA part stays open. Part III's
  conclusion gains the same note.
- Part I's Hughes Sections 13-14 note, its conclusion, its title-page note,
  its Section 10.2 and Appendix D gain one dated note each.

## Notation

Article Section 1.5 has Part I's table (no symbol of manuscript 01 was
renamed). Sections 13.3 and 29.3 have the tables for Parts II and III. Ten
symbols of the batch-66 manuscripts were renamed, with no change of
normalization:

- Part II: the coordinate hull `𝓗(L)` is printed as Part I's `Rec(L)`;
  the regular delimiter languages `G(K)`, `B(K)` of Section 20.3 as
  `Ĝ(K)`, `B̂(K)`, because they are not Part I's `G_K`, `B_K`.
- Part III: the full closure `𝓗(L)` (`𝓗_R`) as `Rec(L)` (`Rec_R`), the same
  set by Theorem 3.3; the crossover map `𝓒(L)` as `T(L)`; the gap-ray
  language `T_s(a,d)` as `Gap_s(a,d)` and the finite union `T` of
  Lemma 36.1 as `𝒯`; the row equivalence `E_a(i,r)` as `Eq_a(i,r)` (Part I's
  `E_a` is the position support, Part III's `P_a^L`); the family `L_k` as
  `L^fam_k`; the threshold `T = 2^d + 1` in the proof of Theorem 39.2 as `θ`.

To watch: `⊗_c` is Hughes's constrained crossover (his `⊗_u` contains
concatenation); `L^[k]` is the parallel iteration, whereas Hughes's iterated
operations, read as for his iterated insertion, give the frozen-source `Y_k`
when both inputs are `L` (Part II writes `Y_{k+1} = Y_k ⊗_c L`, Parts I and
III `L ⊗_c Y_k`: the same set, since `⊗_c` returns both children);
`ρ_L(w)` (aligned-fragment rank) and `d_L(w)` (generation depth) are not
the sibling report's insertion degree `d_{A,B}(w)`; "no gaps" here concerns
ranks on a slice, not insertion spectra. Part II's `M_L(n)` is Part I's
`R_L(n)` on active slices, while Part II's `R(L)` is a supremum over all
lengths and Part III's `R ⊆ ℕ²` a marker mask. Part III's `P_a^L(i,j)` is
Part I's `(i,j) ∈ E_a`, and its zero-based `A_L(n,i)` is Part I's one-based
`P_{n,i+1}(L)`. Words are indexed with zero-based boundaries, `w[i:j]`
being positions `i+1..j` in Part I's one-based letter count.

## Relation to neighbouring reports

- **`automata-and-formal-languages/insertion-degree-spectra`** (*Gaps in
  Bounded-Shuffle Hierarchies*, the "ProveIt report" of Part I's
  Section 1.1, read at the pin; unchanged from the pin to the placement).
  Both reports start from Hughes's preprint, from different parts of it.
  That report answers questions of Hughes's Sections 10-11 on insertion
  degrees and iteration depth; its scope sentence says it addresses "the
  indicated no-gap questions, not the surrounding undecidability results",
  and it never names the crossover question. Part I answers one of those
  surrounding decision problems (Section 4), for crossover. No theorem is
  shared or used across the two. Part I's no-gap theorem for aligned rank
  (Theorem 3.4) is an analogue, for another operation, of that report's
  iteration-depth no-gap theorem (its Theorem 8.2); that report iterates
  with the inserted language held fixed, so its closest crossover
  counterpart here is the frozen-source iteration (Theorem 3.8). Hughes's
  singleton conjecture (that report's Question 21.1) stays open. Article
  Section 1.4 sets this out; that report carries a dated reciprocal remark
  under its scope sentence. Parts II and III concern crossover only and use
  nothing from that report; its remark has not been extended to them.
- No other report of the research-report or surreal collections treats
  crossover of languages or cites Hughes's preprint (searched: crossover,
  Hughes, 2608.27755; the other reports using the word "crossover" use it in
  unrelated senses). `shuffle-six-state-bound` in this category concerns the
  state complexity of shuffle and shares no theorem with this report.

## Formal status

ProveIt has no formal development of crossover, aligned rank, context-free
grammars, Post correspondence, Parikh images, semilinear sets, Presburger
counting, distance-automaton limitedness, finite automata, unary
arithmetic-progression normal forms or space complexity classes (no ProveIt
Lean or Rocq file mentions NFAs, DFAs, PSPACE or Savitch; the vendored
`lib/Coq-Library-Undecidability` snapshot contains no grammar or PCP
files). The nearest formal neighbour is `Logic/PresburgerArithmetic`, whose
Lean development proves Cooper quantifier elimination for Presburger
arithmetic over the integers:
`PresburgerArithmetic.Formula.holds_iff_quantifierEliminate` and the
decision procedure `PresburgerArithmetic.Formula.presburgerArithmetic_decidable`
(`Logic/PresburgerArithmetic/Lean/PresburgerArithmetic/Decision.lean`), with
an independent Rocq proof of the one-variable Cooper step
(`Logic/PresburgerArithmetic/Coq/Cooper.v`). Part I's Lemma 8.2 and
Appendix B, and Part III's Lemma 31.4 and Theorems 32.1-33.2, invoke
Presburger decision procedures of this kind as effectivity steps; Part III
names that development as a possible bridge; none of them is connected to
it, and the Parikh and counting theorems they need are not formalized.
**Not formalized:** every statement of all three Parts. No Lean build was
run for this report.

## Building

In a scratch directory holding a copy of `article.tex`:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

The committed PDF was built this way with MiKTeX pdfLaTeX (packages include
newtx, `shuffle`, fancyhdr, listings, tikz, hyperref; no BibTeX step): 78
US-letter pages, 0 errors, 0 warnings, 0 overfull or underfull boxes, no
undefined or multiply-defined references or citations and no duplicate
destinations. The title page is excluded from page anchors. All fonts are
embedded; the two Type 3 fonts are the `shuffle` package's bitmap symbol,
as in the batch-44 build. Do not run `make pdf` or `make clean`
(`code/Makefile`, `code/03-closure-classification-Makefile`) or
`code/02-pspace-stabilization-build.sh` in this directory: they would leave
`latexmk` auxiliary files here, or fail. GNU `make` is not installed on the
reference machine anyway.

## Rerunning the checks

Never run a verifier in place: Part I's and Part II's verifiers default to
`data/verification.json`, Part III's always writes it, and that file is
Part I's receipt; Part II's example and Part III's verifier also import
sibling modules under their delivered names. Run each on a copy that
restores the delivered layout (Python >= 3.10, standard library only; `py`
on Windows, `python3` elsewhere).

**Part I:**

    mkdir run1 && cd run1
    cp -r <report>/code <report>/data .
    py code/verify.py

It prints the lines of `data/verification.txt` and rewrites
`run1/data/verification.json`. When Part I was written it was rerun this
way with Python 3.14.4: PASS with 1,766,639 checks in about 36 seconds; the
rewritten JSON equals the shipped one except for `elapsed_seconds` (and is
written with CRLF line endings on Windows), and the console output differs
from `data/verification.txt` only in the elapsed time and the receipt path.
Checks raise exceptions rather than use `assert`, so they stay active under
`python -O`.

**Part II:**

    mkdir -p run2/code run2/data && cd run2
    cp <report>/code/02-pspace-stabilization-verify.py code/verify.py
    cp <report>/code/02-pspace-stabilization-example.py code/example.py
    py code/verify.py --output data/verification.json
    py code/example.py

When Part II was written this ran with Python 3.14.4 in about 33 seconds:
PASS, every count and verdict equal to the shipped receipt; the JSON
differs from `data/02-pspace-stabilization-verification.json` only in
`python` and `elapsed_seconds` (and CRLF line endings on Windows), and the
console output from `data/02-pspace-stabilization-verification.txt` only in
those two lines and the receipt path. The example reports no finite
stabilization for the parity language of Example 22.3, an obstruction `01`
at residue 1, and ranks 3, 5, 9 for 1, 2, 4 pumped copies. Run ordinary
Python, not `python -O` (some checks are `assert`s).

**Part III:**

    mkdir -p run3/code run3/data run3/examples && cd run3
    cp <report>/code/03-closure-classification-verify.py code/verify.py
    cp <report>/code/03-closure-classification-crossover_masks.py code/crossover_masks.py
    py code/verify.py > data/verification.txt
    cp <report>/data/03-closure-classification-two_markers.json examples/two_markers.json
    py code/crossover_masks.py examples/two_markers.json --output examples/two_markers.out.json

(and likewise for `endpoint_cycle5`, `finite_point_exception`,
`five_markers` and `incompatible_velocities`). When Part III was written
the verifier printed PASS with 12,867 checks in about a second; its JSON
receipt differs from the shipped one only in `python` (3.14.4 instead of
3.13.5) and CRLF line endings; the five analyses equal the shipped
`.result.json` files after CRLF normalization. The analyzer alone imports
nothing from the package and may also be run in place on a shipped input,
printing to standard output.

## Other discrepancies

- The delivered PDFs were 23 pages each; this build is 78, because the three
  are one document with `[write]` text (Part I's Sections 1.4-1.5, its notes
  on the title page, in Sections 1.1, 2, 7, 10, 11 and 12 and in Appendices A
  and D; Sections 13 and 29; notes in Parts II and III). The page size stays US letter. The
  contents list Parts II and III by section only (`tocdepth` 1 from Part II
  on); Part I's appendices are listed under "Appendices to Part I".
- Part I's manuscript cites the sibling report by its article title, *Gaps in
  Bounded-Shuffle Hierarchies*; its directory is `insertion-degree-spectra`.
- Part II's and Part III's bibliographies cited Part I as `Repo`, which in
  Part I's own bibliography is the sibling report; those citations were
  replaced by internal references. Part III's `Esparza` entry is Part I's
  `EGKL` (same paper); the other new entries (To, Kao-Rampersad-Shallit,
  Savitch, Parikh, Ginsburg-Spanier, Barceló et al., Hague et al.,
  Ganardi-Ricros, Raz, Karp, Rosser-Schoenfeld) follow Part I's.
- Part III's Lemma 31.4 (effective Presburger supports) is Part I's
  Lemma 8.1, which manuscript 03 does not cite; the write added the credit,
  and the manuscript's transducer proof is kept as a second route.
- Parts II and III each reprove Part I's coordinate-hull theorem
  (Theorem 3.3): printed once, in Part I, with Part II's
  Proposition 15.2 / Corollary 15.3 and Part III's Lemma 31.3 kept as marked
  restatements with second and third proofs.
- Part II's tikz library `fit` (loaded by the manuscript, unused) and Part
  III's `lmodern` and `amssymb` packages are not loaded; the report keeps
  Part I's newtx fonts.
- `data/verification.json` records the delivered Part I run's
  `elapsed_seconds` (11.498) and `data/02-pspace-stabilization-verification.json`
  Part II's (8.272): machine timings.
