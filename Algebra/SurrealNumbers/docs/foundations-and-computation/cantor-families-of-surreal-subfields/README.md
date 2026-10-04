# A Cantor Space of Surreal Subfields

**Finite supports, universal embeddings, and two generic regimes**

A research report dated 3 October 2026, built from one manuscript on the
descriptive set theory of countable real closed subfields of `No`, prompted by
Elliot Glazer's *A Topological Tennenbaum Theorem* (arXiv:2311.13699). Its
author lines read "Research article prepared for Vladimir Reshetnikov" and
"AI-assisted mathematical draft".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 90, manuscript 04 | `Surreal_Subfield_Cantor_Research.zip` (544,930 bytes, nine members; inner directory `surreal_subfield_cantor/`, main file `article.tex`, 1843 lines, 27-page A4 PDF), arrival commit `a162e4386` | `7c0f2d9f9` (`7c0f2d9f92c3d51ec85703bed1022924a4b7359b`, 3 October 2026, "New research reports"; quoted in Section 12.2 and in the bibliography entry for ProveIt) | `12076b2e8` | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration states any theorem of this report (one finite algebraic input,
Lemma 3.1, is an instance of a Lean theorem; see *Relation to the
repository*), and its place in the surreal collection confers no formal
status. Its finite checks were executed (by the package and again at the
write); its infinite theorems rest on the written proofs only. **Historical
priority is not established.**

## The question

Let `k` be the real algebraic numbers, `B = {1} ∪ {√p : p prime}`,
`I = Q × B`, and `x_{q,b} = ω^(b ω^q)` (Conway's omega-map, not Gonshor's
exponential). For `A ⊆ I`, `K_A` is the relative real closure in `No` of
`k(x_i : i ∈ A)`, a countable set, and `K* = K_I`. The family `C* = {K_A}` is a
set of subsets of the countable field `K*`, with the Cantor topology, and
`C^(1) = {K^(1)_S = K_{S×{1}} : S ⊆ Q}` is its rank-one subfamily. The
unrestricted complexity of countable real-closed-field embeddability is known
(Calderoni–Marker–Motto Ros–Shani). The manuscript asks *local refinement
questions*, and says they were not previously published as open problems: can
the complexity be confined to actual subfields of one explicit countable
surreal field, in a compact family with finite-coordinate membership tests?
Can one fixed source already give a non-Borel existence problem? How do
transcendence degree and generic sampling affect it?

## What it proves

- **Lemmas 3.1–3.2, Theorem 3.3, Lemma 3.4:** squarefree radical monomials are
  `Q`-independent; the `x_{q,b}` are algebraically independent over `k`
  (a re-proof, see below); `K_A` has value group
  `Γ_A = ⊕_q H_A(q) ω^q` and residue field exactly `k`, with rank chain
  `{q : H_A(q) ≠ 0}`; every field embedding induces maps of value groups,
  rank chains and Archimedean components.
- **Theorem 4.1 (unique finite support),** a general field-theoretic lemma:
  every element `a` has a unique finite `D(a)` with `a ∈ K_A ⇔ D(a) ⊆ A`.
  **Theorem 4.3:** `A ↦ K_A` is a homeomorphism of `2^I` onto a closed Cantor
  family of elementary subfields of `K*`, with clopen membership tests;
  **Corollary 4.4:** a complete Boolean coordinate lattice.
- **Theorem 5.1:** in the rank-one family, `K^(1)_S ↪ K^(1)_T` iff
  `(S,<) ↪ (T,<)`, and likewise for isomorphism. **Corollary 6.1:**
  isomorphism on `C^(1)` and `C*` is Borel complete for countable structures.
- **Theorem 6.3:** for the fixed source `P_- = K^(1)_D`, `D` of type `ω*`,
  the embedding locus `E^(1)_{P_-}` (the non-well-ordered `S ⊆ Q`) is
  analytic-complete, already on targets of transcendence degree `ℵ0`;
  **Lemma 6.4, Theorem 6.5:** an integer-sum tree transform makes the source
  `K^(1)` (copies of `Q`) analytic-complete too; **Corollary 6.6:** no total
  Borel witness solver.
- **Lemma 7.2, Theorems 7.3–7.4:** the ordered groups `Q(√p_n)` form an
  antichain; colored countable orders are coded exactly into fields `M_L ⊆ K*`
  without color predicates; embeddability on `C*` is a **complete analytic
  quasiorder**, bi-embeddability a complete analytic equivalence relation
  (with Louveau's theorem as external input). Together these give
  **Theorem 1.1**.
- **Theorem 8.1, Proposition 8.2:** a source of finite transcendence degree
  has an open locus; an infinite one has empty interior.
- **Theorem 9.1, Corollary 9.2:** in the rank-one family a comeager conull
  set of parameters gives fields isomorphic to `K^(1)`; the analytic-complete
  locus of `P_-` is comeager and conull.
- **Theorem 10.1, Proposition 10.2, Lemma 10.3, Theorem 10.4, Corollary
  10.5:** category and measure zero–one laws for translation-invariant loci in
  `2^I`; `E*_{P_-}` is analytic-complete, comeager and conull, while `E*_{K*}`
  is analytic-complete and dense but meager and null. Together with Sections
  6–9 these give **Theorem 1.2**.
- Section 11: examples and interpretation; Section 12: a sampling warning, the
  repository snapshot and a staged formalization plan (a proposal);
  Section 13: twelve research questions; Appendix A: a proof-dependency ledger;
  Appendix B: the finite checks.

## What is not claimed

- The unrestricted theorem that embeddability of countable real closed fields
  is a complete analytic quasiorder (and bi-embeddability a complete analytic
  equivalence relation) is Calderoni–Marker–Motto Ros–Shani's (arXiv:2010.08049,
  Corollary 7.3), credited, not claimed new. Colored-order completeness
  (Louveau), surreal normal forms, real-closure theory, quantifier elimination
  for RCF, completeness of ill-founded trees and Borel completeness of
  countable-order isomorphism are external inputs. The proposed contribution
  is the common explicit countable surreal ambient field, the compact
  finite-support localization, the fixed-source threshold and the comparison
  of generic regimes; its worldwide priority is not established.
- No published open question of Glazer's is claimed solved; the connection
  to his work is descriptive, and nothing settles his questions on
  uncountable topological arithmetic (the Cantor topology is on parameters,
  not on `No` or on a field's domain).
- No universal field for all countable real closed fields is claimed (the
  residue field is fixed to `k`); embeddings are not assumed to preserve the
  displayed generators; no closure under `exp` or a derivation; no topology or
  measure on the proper class `No`; no explicit or optimal birthday cutoff; no
  effective algorithm from an open or Borel locus; the no-solver result is
  about total Borel solvers, not about non-Borel choice; analytic-completeness
  of a set and completeness of a quasiorder are kept apart (uncolored order
  embeddability alone does not give quasiorder universality); generic collapse
  is asserted only for the rank-one family.
- No Lean proof, repository build or kernel check of any new result; the
  finite Python checks test conventions and implementation, not the infinite
  theorems.

## Checks made at the write

On 4 October 2026:

- **Repository claims.** The pin `7c0f2d9f9` is an ancestor of the placement.
  The three Lean files the manuscript names are byte-identical at the pin and
  at the write: `Surreal/Foundations/SignSequenceRealClosed.lean` (blob
  `a0d30d424`; `signSequenceIsRealClosed` is an `instance`, line 36),
  `Surreal/HahnSeries/RealClosed.lean` (`632c027e9`; real closedness of
  set-sized Hahn fields) and `SurrealAudit.lean` (`e9b72519e`), all under
  `Algebra/SurrealNumbers/`. The surreal README separates formal declarations
  from unrefereed reports. The self-embedding report's README (blob
  `554357db9` at the pin) has since gained a batch-89 cross-reference and a
  page count, without changing what the manuscript says of it. No repository
  statement is contradicted; nothing needed retraction.
- **Prior work.** arXiv:2010.08049 (Calderoni, Marker, Motto Ros, Shani,
  *Anti-classification results for groups acting freely on the line*) has
  v1 of 15 October 2020 and v2 of 13 January 2023, the version cited; its
  record notes acceptance in *Advances in Mathematics*. In v2, Section 7
  ("ODAG and other o-minimal theories") states Theorem 7.1 (colored-order
  embeddability is a complete analytic quasiorder, "observed by Louveau",
  citing Marcone–Rosendal, Theorem 3.2), Proposition 7.2 (a Borel reduction
  from colored orders to ordered divisible abelian groups through
  finite-support reverse-lexicographic groups with pairwise non-embeddable
  Archimedean components) and Corollary 7.3 (the real-closed-field statement,
  via real closures of `k(t^g)`) on PDF pages 33–35; Lemma 2.2 is Hion's
  lemma. Every citation of it in the manuscript matches. Theorems 7.3–7.4
  here compose Proposition 7.2 and the construction of Corollary 7.3 inside
  one fixed field with explicit components `Q(√p_n)`. Rast–Sahota, Miller's
  lecture notes, Marcone–Rosendal and Laver were not rechecked.
- **Delivered files.** `SHA256SUMS.txt` (eight entries) matched the delivery
  at placement; it is not shipped. No file of the package was already in the
  repository.
- **Finite checks** rerun on a scratch copy (Python 3.14.4, Windows, under
  20 seconds): `"status": "PASS"`, 25,378 checks, seed 20261003; the report
  equals `data/finite_checks.json` except for `python_version` (3.14.4
  against the delivered 3.13.5), after removing the CR bytes Windows adds.
- **Personal data.** No e-mail address, LinkedIn URL or other personal data in
  any shipped file. The audit cites Glazer's public papers and states that no
  current employment or model-performance claim is inferred.

## Relation to the repository

**Formal status.** No statement of this report is formalized. One finite
algebraic input is: Lemma 3.1 (distinct squarefree radical monomials are
`Q`-linearly independent) is the instance `M = Q`, `a_i = p_i`, roots in `R`,
of `tail:lem:signs` of
[`tail-spans-and-differential-transcendence`](../../surreal/tail-spans-and-differential-transcendence/),
proved in Lean as `Surreal.TailSigns.linearIndependent_mono`
(`Algebra/SurrealNumbers/Surreal/Algebra/MultiquadraticSigns.lean`) with the
prime hypothesis `Surreal.AlgebraicClosurePart.independentSquareClasses_prime`
(`Algebra/SurrealNumbers/Surreal/HahnSeries/AlgebraicCoefficientClosure.lean`);
the specialization is not itself a declaration. The manuscript's own Lean
pointers (`signSequenceIsRealClosed`, the Hahn-field real-closedness
instances) are background: they prove real closedness of the ambient fields,
not any theorem here. The four-stage formalization plan of Section 12.3 is a
proposal. No `csf:` label has a Lean mapping in the
[formalization ledger](../../FORMALIZATION.md).

**Review in the Hilbert's-tenth research tree.** Another session inventoried
all six batch-90 archives at their arrival (commit `bcc1a4438`,
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_polish_partx_c9bc70d8f.md`,
with its JSON receipt). For this archive it read the delivered README in full
(lines 1–86) and hashed the other eight members without reading them. Its
routing result: "Analytic-complete embeddability inside a countable surreal
field and finite-support topology; descriptive complexity is not finite
arithmetic universality". It ran no program, made no correctness finding and
needed no scope correction; the Hilbert's-tenth programme's 84-operation
universal polynomial is unaffected.

**Re-proof.** Lemma 3.2 (double-monomial independence) is the case
`K = k`, `G = {0}`, `g_{q,b} = b ω^q` of Lemma 8.1 (`dsn:lem:cosets`,
"Disjoint support cosets") of
[`definable-surreals-and-omnific-integers`](../definable-surreals-and-omnific-integers/);
Part VII of
[`birthday-cutoffs-and-hereditary-sets`](../birthday-cutoffs-and-hereditary-sets/)
proves the coefficient-one analogue over `R` (`hset:kw:thm:double`,
Theorem 43.1) by the same leading-term argument, and records in Remark 40.4
(`hset:kw:rem:other`) that it too is a case of `dsn:lem:cosets`. Both are
credited in a dated note after Lemma 3.2; the proof is printed as the
manuscript's own. Part VII otherwise proves different theorems (choiceless
coding and free-algebra universality of `No` over ZF).

**Neighbouring reports.**

- [`surreal-self-embeddings`](../../surreal/surreal-self-embeddings/) (`sse:`),
  cited by the manuscript as background: Lemma 3.4 is the subfield form of its
  `sse:prop:valueaction` (note after the lemma). Its questions concern
  self-embeddings of `No`; none is answered here.
- [`independent-surreal-copies`](../../surreal/independent-surreal-copies/)
  (`isc:`): `isc:thm:boolean` realizes a Boolean lattice of full Hahn fields
  (`E_J ∩ E_T = E_{J∩T}`, full Hahn join `E_{J∪T}`), the analogue of
  Corollary 4.4 for full Hahn fields, proved through normal-form supports;
  no shared result (note after the corollary).
- [`polish-models-of-omnific-arithmetic`](../polish-models-of-omnific-arithmetic/)
  (`pma:`), Part II: its `pma:bor:lem:KB` contains the Kleene–Brouwer Lemma 6.2
  and shows `WO(Q)` is `Π¹₁`-complete, which by Theorem 5.1 is the
  complement form of the analytic-completeness in Theorem 6.3 (the reduction
  here adds a fixed well-ordered prefix so all targets have transcendence
  degree `ℵ0`). Its `pma:bor:thm:dichotomy` (Theorem 18.4: `WO(L)` Borel iff
  `L` scattered) gives, as an observation of the write, that on parameters
  restricted to subsets of a fixed countable `L ⊆ Q` the locus of `P_-` is
  Borel exactly when `L` is scattered; this bears on, but does not answer,
  Question 13.1 (note after Theorem 6.3).
- [`surreal-fields-across-universes`](../surreal-fields-across-universes/)
  (`univ:`), Part VIII: `univ:gs:thm:boolean` also indexes real closed fields
  by subsets of a set (the class fields `No^{M_A}` of Cohen extensions), but
  there embeddability is exactly inclusion `A ⊆ A'`, while here it is
  embeddability of colored rank orders. Different objects, no shared proof.
- [`omnific-notations`](../omnific-notations/) (Part IV: `Π¹₁`-complete
  support validity) uses the same ill-founded-tree toolkit on different
  objects; [`computable-surreals`](../computable-surreals/) builds effective
  countable real closed subfields of `No` with value group `Q`, background for
  Question 13.4, no shared theorem.
- Batch-90 siblings, written concurrently from the same arrival: manuscript
  06 became source 04 of
  [`discrete-initial-subgroups-and-omnific-normalization`](../../surreal/discrete-initial-subgroups-and-omnific-normalization/)
  (`isg:ptg:`) and also cites arXiv:2311.13699; 01 and 03 became Parts XI–XII
  of `polish-models-of-omnific-arithmetic`, 05 Part VIII of
  `birthday-cutoffs-and-hereditary-sets`, and 02 Part II of
  `SetTheory/Cardinals/docs/reports/ordinals-and-order-types/measurable-box-games`.
  None shares a theorem with this report.

**Stale claims.** None. The manuscript's repository statements are true at
the pin and at the write, and it claims no gap in the repository.

## Notation

`k` (real algebraic numbers, fixed), `B`, `I`, `x_{q,b}`, `t_q`, `K_A`, `K*`,
`K^(1)_S`, `C*`, `C^(1)`, `rc_No` (a set-sized relative real closure),
`D(a)` (finite *generator* support, not normal-form support), `D` (the order
`{−n}` of type `ω*`) with `P_- = K^(1)_D`, `D_A` (complete-column ranks),
`A_q`, `J_A` (defined twice, by `H_A(q) ≠ 0` and by `A_q ≠ ∅`; the two
agree), `H_A(q)`, `Γ_A`, `H_n = Q(√p_n)`, `H = span_Q B`, `v`, the loci
`E*_P` and `E^(1)_P` (sets of parameters), boldface `Σ¹₁`/`Π¹₁` (not
σ-algebras), `KB`, `IF`, `WF`, `S_L`, `S_T`, `Z(L)`, `R_T`, `N`, `M_L`, `G`,
`W_P`, `τ_r`, `μ`, `β` and the birthday `b(a)` (not the coefficient
`b ∈ B`). `ω^x` is Conway's omega-map throughout. The table of Section 1.5
fixes each one with the tempting false reading, and lists the clashes with
neighbouring reports (`K_A` is not `isc`'s `E_J`, `univ`'s `No^{M_A}` or
`hset` Part VII's `T_X`, `U_κ`; `E*_P` is unrelated to the enumeration
predicate `E` of `hset` Parts VI and VIII). No symbol was renamed.

## Labels

Every label carries the prefix `csf:`. The manuscript's 56 labels were
prefixed before anything cited them and every reference updated (63 `\cref`
keys, 15 `\eqref`); the write added `csf:sec:provenance`, `csf:sec:notation`
and twelve question labels `csf:q:fixedsource` … `csf:q:certified` (the
delivered questions had none): 70 labels. No section, theorem, equation or
question number of the manuscript moved (checked against a build of the
delivered source); the two new subsections are 1.4 and 1.5.

The writing step also:

- added dated `[write]` notes: Section 1.4 (provenance, pin and repository
  claims, formal status, the Hilbert's-tenth review, the prior-work check,
  neighbouring reports), Section 1.5 (notation table), after Lemma 3.1 (Lean
  instance), after Lemma 3.2 (the re-proof), after Lemma 3.4 (`sse`), after
  Corollary 4.4 (`isc`), after Theorem 6.3 (`pma`), at the end of Section 7.2
  (the prior-work check), in Section 12.2 (formal status), after Question
  13.12 (status of the questions) and in Appendix B (shipped layout and
  rerun);
- added a one-line `[write]` pointer on the title page and wrapped the title
  page in `\hypersetup{pageanchor=false}` … `=true`;
- added cleveref type hints (`\label[lemma]{…}` and so on) to the labels of
  the 8 lemmas, 4 corollaries, 2 propositions and 12 questions, with a
  `\crefname` for `question`. These environments share the theorem counter,
  and in the delivered build every reference to them printed as "theorem"
  (for example "theorem 3.2" for Lemma 3.2). Only the printed names change.

No statement, proof, number or non-claim of the manuscript was changed.

## Files

```text
README.md                    this guide (replaces the delivered README.md, staged under this name)
SOURCE_AND_CLAIM_AUDIT.md    delivered source and claim audit: sources used, pin, files inspected, external inputs, excluded claims
article.tex                  the report (delivered article.tex; labels prefixed, type hints, [write] notes)
article.pdf                  compiled report, 32 pages (unnumbered title page, then pages 1-31)
code/build.sh                delivered build: runs the finite checks, then three pdfLaTeX passes, in its own directory
code/finite_checks.py        exact finite checks with integers and fractions (standard library)
data/finite_checks.json      recorded run of finite_checks.py (Python 3.13.5, 25,378 checks, seed 20261003)
data/build_audit.json        delivered build record: engine, 27 pages, no warnings, visual inspection, pin
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery; placement moved `build.sh` to `code/`. Not
shipped: the delivered 27-page `article.pdf` (518,033 bytes), the delivered
README (this file replaces it) and the checksum manifest `SHA256SUMS.txt`
(verified at placement; repository policy drops checksum manifests). Nothing
was excluded as heavy. All three survive in the archive:
`git show a162e4386:docs/incoming/Surreal_Subfield_Cantor_Research.zip > <scratch>/Surreal_Subfield_Cantor_Research.zip`.

Delivered text that names the delivery layout or a file not shipped:

- `code/build.sh` changes to its own directory and then runs
  `python3 code/finite_checks.py --output data/finite_checks.json` and
  `pdflatex article.tex` there: in place it would look for
  `code/code/finite_checks.py` and `code/article.tex` and fail; run it on a
  copy (below). Even on a copy it rewrites the copy's
  `data/finite_checks.json`.
- `data/build_audit.json` describes the delivered 27-page PDF (not shipped)
  and "no warnings"; the delivered source also builds without warnings under
  MiKTeX (27 pages).
- The article's Appendix B lists `article.pdf`, `build.sh` and
  `SHA256SUMS.txt` among the archive's files and gives commands for the flat
  delivery layout; a note there gives the shipped layout.
- `SOURCE_AND_CLAIM_AUDIT.md` refers to "the ZIP" and the compiled PDF, says
  the repository was inspected "through the connected GitHub tools" at the
  pin, and names repository paths only.
- `data/finite_checks.json` names no paths.

## Rerun the checks

`finite_checks.py` without `--output` only prints its report, so it can run in
place; with `--output` it writes the file named, so never point that at
`data/`. Python 3, standard library only. From this directory, in Git Bash (on
a POSIX host use `python3` for `py`):

```sh
py code/finite_checks.py > /dev/null          # read-only; the report says "status": "PASS"
T=$(mktemp -d)
py code/finite_checks.py --output "$T/finite_checks.json" > /dev/null
tr -d '\r' < "$T/finite_checks.json" | diff - data/finite_checks.json
```

At the write (4 October 2026, Python 3.14.4, Windows) the run took under 20
seconds and the only difference was the `python_version` line (3.14.4 against
3.13.5). The recorded run covers all 5,914 labeled linear orders of size at
most 7 (rational placement), 2,400 colored and 2,400 uncolored finite chain
embeddings, 5,461 multiquadratic character-orthogonality checks up to rank 6,
5,000 ordered-group reindexing and additivity checks, 4,200 polynomial
product, sign and reindexing checks, two explicit cancellations and one
negative control for reversed rank order.

## Build the PDF

pdfLaTeX with lmodern, microtype, geometry, amsmath/amssymb/amsthm/mathtools,
booktabs/longtable/array/enumitem, xcolor, fancyhdr, hyperref, cleveref and
listings; the bibliography is inline. Build in a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The delivered `build.sh` needs the delivered layout. On a POSIX host:

```sh
B=$(mktemp -d); mkdir "$B/code"; cp article.tex code/build.sh "$B/"
cp code/finite_checks.py "$B/code/"; cd "$B"; sh build.sh
```

It was not run at the write. The committed PDF was built the first way with
MiKTeX: 32 pages; no errors or warnings, no undefined references or
citations, no multiply defined labels, no duplicate PDF destinations, no
overfull or underfull boxes.

## Provenance

- Sources cited by the manuscript: Glazer, arXiv:2311.13699; Glazer et al.,
  arXiv:2411.04872 (FrontierMath, cited for research direction only);
  Calderoni–Marker–Motto Ros–Shani, arXiv:2010.08049v2; Rast–Sahota, JSL 82
  (2017); Marcone–Rosendal, JSL 69 (2004); Friedman–Stanley, JSL 54 (1989);
  Laver, Annals 93 (1971); Miller's lecture notes; Gonshor; van den
  Dries–Ehrlich; Marker; and the ProveIt files above at the pin.
- Repository input: the pin `7c0f2d9f9` (3 October 2026), an ancestor of the
  placement.
- Batch 90 of `docs/incoming`, manuscript 04 of six; arrival `a162e4386`,
  placement `12076b2e8`, written in the batch-90 write phase (4 October 2026).
  Single source, so the write made no merge choices. Filed under
  `foundations-and-computation/` (descriptive set theory about subfields of
  `No`); `surreal/` would also have fitted.
