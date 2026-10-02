# Groups as Diophantine Substrates

**Arithmetic van Kampen certificates and three commutative phases: quartic certificates through the integral Heisenberg group**

This is a research report dated 2 October 2026, built from two manuscripts
of batch 76 of ProveIt's incoming reports. Both are AI-assisted research
manuscripts "prepared for Vladimir Reshetnikov". They are called *source 03*
and *source 05* after their batch-76 manuscript numbers, which are also the
file prefixes of their shipped programs and data.

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 03 (base) | batch 76, manuscript 03 | `arithmetic_van_kampen.zip` (`6914ccca6`); *Arithmetic van Kampen Certificates: Quartic equations, exact filling area, and optimal proof-DAG compression*, main file `arithmetic_van_kampen.tex`, 29-page PDF | `c58206ca1` | `2a04b60f2` | Part I (Sections 2–17) and Appendices A–C |
| 05 | batch 76, manuscript 05 | `three_commutative_phases_research.zip` (`6914ccca6`); *Three Commutative Phases Are Diophantine-Universal: A fibre-preserving Heisenberg compiler and a proposed resolution of the three-subgroup problem*, main file `article.tex`, 22-page PDF | `433df1be3` | `2a04b60f2` | Part II (Sections 18–31) and Appendices D–F |

Every result, proof, example, remark, limitation, research question and
audit of the two manuscripts is printed. They share no theorem and neither
cites the other: source 03 treats a finitely presented group as a
proof-producing substrate and uses the Heisenberg group as an *area
detector*; source 05 treats an ordered product of three abelian subgroups
of a Heisenberg power as the substrate and uses the Heisenberg group as the
*ambient group*. The shared setup — the integral Heisenberg group, its
multiplication, inverse and power laws — is printed once, in Section 1.2,
with a table of every letter the two Parts use differently (Table 1).

**Status: AI-assisted, unrefereed, not formalized.** Part II's main theorem
is a **proposed resolution, unrefereed**, of a published open problem; its
priority is not certified. Nothing in the report is formalized in Lean or
Rocq.

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 62 pages (unnumbered title page, then pages 1–61)
README.md                                            this guide
03-van-kampen-SOURCES.md                             source 03's dependency, provenance and novelty notes, as delivered
code/03-van-kampen-van_kampen.py                     source 03's exact matrix routines, Sanov decoder and symbolic compilers (SymPy)
code/03-van-kampen-verify.py                         source 03's deterministic exact-arithmetic tests (imports van_kampen)
code/05-three-phases-build.sh                        source 05's three-pass pdflatex script (delivered layout; see below)
code/05-three-phases-heisenberg_compiler.py          source 05's standard-library exact-integer three-phase compiler
code/05-three-phases-verify.py                       source 05's 190,826-assertion verification (imports heisenberg_compiler)
data/03-van-kampen-commutator_budget_1.json          the one-budget compiler for [a,b]: 11 variables, 13 quadratic residuals
data/03-van-kampen-grid_1_1.json                     the shared dyadic grid compiler for [a^2,b^2]: 12 variables, 16 residuals
data/03-van-kampen-grid_1_1_witness.json             a satisfying assignment of the grid example (all values)
data/03-van-kampen-receipt.json                      source 03's recorded run: all checks passed (Python 3.13.5, SymPy 1.14.0)
data/03-van-kampen-render_check.json                 source 03's record of its own 29-page PDF build
data/03-van-kampen-export_check.json                 source 03's record of 4 + 4 sparse-polynomial evaluations
data/03-van-kampen-requirements.txt                  source 03's pin, sympy==1.14.0
data/05-three-phases-circuit.json                    compiler data and generator lists for the circuit example (Section 25.2)
data/05-three-phases-circuit_input.json              its quadratic specification
data/05-three-phases-multiplication.json             compiler data for xy − z = t: all fourteen basis matrices (Section 25.1)
data/05-three-phases-multiplication_input.json       its quadratic specification
data/05-three-phases-profinite_obstruction.json      compiler data for F(x) = 6x² − 5x in H × Z (Section 28)
data/05-three-phases-profinite_obstruction_input.json  its quadratic specification
data/05-three-phases-verification_receipt.json       source 05's recorded run: PASS, 190,826 assertions in 30 families
```

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md`
is byte-identical to the delivery. Delivered name → shipped name:

- Source 03: `code/van_kampen.py`, `code/verify.py` →
  `code/03-van-kampen-*.py`; `examples/commutator_budget_1.json`,
  `examples/grid_1_1.json`, `examples/grid_1_1_witness.json`,
  `verification/receipt.json`, `verification/render_check.json`,
  `verification/export_check.json`, `requirements.txt` →
  `data/03-van-kampen-*`; `SOURCES.md` → `03-van-kampen-SOURCES.md`;
  `arithmetic_van_kampen.tex` → the base of `article.tex` (Part I).
- Source 05: `build.sh`, `code/heisenberg_compiler.py`, `code/verify.py` →
  `code/05-three-phases-*`; `examples/*.json` and
  `verification_receipt.json` → `data/05-three-phases-*`.

Not shipped: source 05's manuscript (`article.tex`, printed as Part II),
both PDFs and both delivered READMEs (this text and `article.tex` replace
them), and source 03's checksum ledger `SHA256SUMS.txt` (verified, 13 of 13
files, at placement; source 05 shipped none). They survive in the archives of
the arrival commit; for example
`git show 6914ccca6:docs/incoming/three_commutative_phases_research.zip > tcp.zip`
recovers source 05's package, and
`git show 6914ccca6:docs/incoming/arithmetic_van_kampen.zip > avk.zip`
source 03's.

## Labels and numbering

Every label carries the prefix `gts:`. Source 03's 89 labels are
`gts:vk:` plus their delivered names, and source 05's 64 are `gts:tp:` plus
theirs; no source label was dropped or renamed apart from the prefix. Source
05's three Heisenberg equation labels (`gts:tp:eq:Hmult`, `gts:tp:eq:Hinv`,
`gts:tp:eq:Hpower`) sit on the common Section 1.2, where the formulas are
printed once. The merge added 36 labels, 189 in all: twelve `gts:` labels of
the front section, the two Parts and the provenance appendix
(`gts:sec:front`, `gts:sec:parts`, `gts:sec:heis`, `gts:eq:commutator`,
`gts:sec:notation`, `gts:tab:notation`, `gts:sec:relation`,
`gts:sec:status`, `gts:sec:questions`, `gts:part:vk`, `gts:part:tp`,
`gts:app:provenance`); `gts:vk:q:*` on source 03's twelve research
questions and `gts:tp:q:*` on source 05's nine research directions;
`gts:vk:sec:problem` on source 03's first section; `gts:tp:rem:credit` on
the credit remark after source 05's two-phase theorem; and
`gts:tp:app:sources` on source 05's source-audit appendix.

Each Part keeps its source's numbering of statements, by section: source
03's Section *n* is Section *n* + 1 here (Sections 2–17), and its Theorem
*n.m* is Theorem (*n* + 1).*m*; source 05's Section *n* is Section *n* + 17
here (Sections 18–31), and its Theorem *n.m* is Theorem (*n* + 17).*m*. Source 03's appendices A–C keep their letters;
source 05's appendices A–C are Appendices D–F. Appendix G is the
provenance. Text written in the merge is marked `[write]`; text without a
marker is the source's own.

## Setting and notation

Both sources use the integral Heisenberg group with the same convention,
`h(a,b,c)h(a',b',c') = h(a+a', b+b', c+c'+ab')`. Source 03 wrote it as
`H = Z^3` with `(x,y,z) = h(x,y,z)`; the report writes `𝖧` in both Parts,
because Part I also uses `H` for a height bound. This is the only renamed
symbol, and no normalization changed. Every other letter keeps its source's
meaning inside its Part; Table 1 (Section 1.3) lists the letters used
differently, among them:

- `A, B` — Part I: the shear matrices `[[1,2],[0,1]]`, `[[1,0],[2,1]]` (and,
  in software words, `A`, `B` mean `a⁻¹`, `b⁻¹`); Part II: the phase
  homomorphisms `A(x,u)`, `B(y)`.
- `C, D, E, L, N, q, m, n, s, t` — Part I: relator matrix or constant, DAG
  or fixed conjugator, chart equation, relator length, witness count,
  label count `2s+1`, area budget, word length, number of relators, chart
  coordinate; Part II: normal-form matrix, linear part, reverse quartic `E_t`,
  linear-form matrix, `n+q` binomial coordinates, number of mixed pairs,
  number of equations, number of variables, an index, the target.
- `λ` — Part I: a label index; Part II: the integral logarithmic coordinate
  `2c − ab`.

Watch for these readings (Section 1.3):

- **Phase** (Part II) is one commuting factor of an ordered product of
  subgroups or submonoids — not a complex phase, a Fabius/Rvachev phase, or
  the "four-phase zero test" of `canonical-diophantine-certificates`
  Part XIII.
- **History-free** (Part I's subtitle) means that no conjugator *word* is
  stored, only four chart integers. It is not the sense of
  `canonical-diophantine-certificates` Part XIV ("history-free routing
  certificates", outcomes instead of executions).
- **Compiler** in both Parts is unrelated to the sparse-machine "universal
  compiler" with arithmetic-operation counts in the Hilbert-tenth-problem
  research notes; no operation record is claimed.
- **Slice**: Part I's Corollary 7.4 is a bounded-*area* slice; Part II's
  Corollary 20.3 is a *central* slice of `𝖧^N × Z^m`.

## Status: what is claimed, and what is not

The report claims conventional mathematical proofs, by its sources, for:

- **Part I (source 03).** Sanov's chart (classical; proof included): the
  free group on two letters is exactly the integral points of
  `x + t + 4xt − yz = 0`. A fixed-itinerary quartic with `8m − 4` witnesses
  and `5m` residuals, and an all-label area-budget quartic with
  `(2s+13)m − 4` witnesses and `(2s+11)m` residuals, whose zeros are in
  bijection with (padded) factorizations and which accept exactly the words
  of area at most `m`. A small-witness height bound (from the
  Cornulier–Tessera bounded-conjugator lemma, imported) and a
  primitive-recursive decision of bounded-area slices. The compiler's
  minimal allocated arity equals `(2s+13)·Area − 4`, and the Dehn function
  correspondingly; the computable-cutoff equivalence with the word problem
  (classical, reproved through the compiler). A proof-DAG quartic with
  `4p + 8h + 4j + 4h_c − 4` witnesses. For `[a^(2^k), b^(2^ℓ)]` in
  `⟨a,b | [a,b]⟩`: area `2^(k+ℓ)`, exactly `k+ℓ` product gates (optimal in the
  stated calculus), and an `8(k+ℓ) − 4`-witness quartic. An addition-chain
  sandwich for rectangular commutators; no computable sharing bound; infinite
  native fibres.
- **Part II (source 05).** An integral binomial normal form of quadratic
  maps; three injective phase homomorphisms into `𝖧^N × Z^m` whose ordered
  product realizes every integral quadratic system with an exact
  fibre bijection; central embeddings into a pure power `𝖧^(N+m)`; with
  MRDP, three fixed free abelian subgroups of `𝖧^d` with computably
  enumerable complete product membership, even on a central affine cyclic
  line (**proposed** negative answer to the three-subgroup question of
  König–Lohrey–Zetzsche, Remark 6.7, and Roman'kov); decidability of two
  commuting phases for integer, natural and mixed exponents; free
  commutative monoid versions; an explicit quartic reverse compiler with
  `2n + 2N` parameters; exact counting, weights and height bounds; no
  computable search bound; an explicit three-subgroup product in `𝖧 × Z`
  (from `F(x) = 6x² − 5x`) that is not closed in the profinite topology.

**Credit for the two-phase theorem (Remark 23.2).** For
*integer* exponents, source 05's two-phase decidability is a special case of
known results, which source 05 does not cite for it: König, Lohrey and
Zetzsche, Remark 6.7 (a product of two subgroups of a polycyclic group is
profinitely closed, hence has decidable membership), and Roman'kov, J. Group
Theory 28 (2025) (the product of two subgroups membership problem is
decidable in every finitely generated nilpotent group of class two). What
source 05 adds: a direct, elementary decision procedure for commuting lists
through the integral logarithmic coordinate `λ = 2c − ab`, reducing
membership to one integer linear system; and the natural and mixed exponent
domains, i.e. ordered products of two finitely generated commutative
submonoids (or of such a submonoid and an abelian subgroup), which are not
subgroup products. No priority is claimed for the latter; the literature on
submonoid products beyond those two papers was not searched.

The report does **not** claim:

- historical priority for either Part (both sources say so); for Part II's
  main theorem, the placement check found no earlier resolution (the arXiv
  text of König–Lohrey–Zetzsche and the abstract of Roman'kov, which still
  states the three-subgroup case open), but that does not certify novelty,
  and Roman'kov's full paper was not read by source 05;
- a finite-fold or single-fold Diophantine representation of c.e. sets or of
  group word problems; Part I's native fibres are generally infinite, and Part
  II transfers fold bounds only conditionally (the four-square conversion can
  change multiplicities);
- a universal arithmetic-operation record, an improvement of the universal
  degree-four bound, an optimized ambient dimension, an instantiated universal
  presentation, polynomial or matrix table;
- that its variable counts are minimal: they are the literal counts of the
  stated compilers; Part I's lower bound is a lower bound in its stated
  proof calculus, not for arbitrary Diophantine representations;
- one fixed-arity polynomial: Part I's budget and circuit shape are external
  data, and MRDP's fixed-arity polynomial preserves neither fibres nor the
  area ledger;
- that Part II answers the open question of the repository note
  `heisenberg_two_generator_membership.md` (do three generators of a
  Heisenberg *submonoid* suffice for undecidability?) — it does not; it
  concerns ordered products of three *subgroups*;
- any Lean or Rocq verification. The finite checks illustrate; they do not
  prove.

## Relation to neighbouring reports and to the formal project

This is the fourth report of the collection's `hilbert-tenth-problem`
category; the other three are organized by substrate family, and finitely
presented and nilpotent groups form a fourth. No result of the three
neighbours is re-proved here.

- **[`probabilistic-quantum-and-continuous-computation`](../probabilistic-quantum-and-continuous-computation)**,
  Part VI (its sources 11 and 16; `pqc:dr:thm:main`): Mihailova's
  fibre-product compiler from finite presentations to rotation gates in
  `SO(4, Z[1/5])`, c.e.-complete membership of a fixed finitely generated
  subgroup, and quartic certificates for bounded *words*. Part I has the same
  input (finite presentations) but certifies relator area and proof-DAG size
  in a free subgroup of `SL_2(Z)`; Part II has a statement of the same kind
  for a product of three abelian subgroups of a unitriangular group. The
  bounded-search argument of its `pqc:qm:cor:nobound` recurs, for different
  statements, in Part I (Corollary 8.3, Theorem 13.2) and Part II
  (Proposition 27.1).
- **[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)**:
  executions compiled to canonical arithmetic zeros. Part I's native compiler
  is explicitly not canonical; Part II compiles in the reverse direction
  (arithmetic to group). Its Part XIV uses "history-free" in another sense
  (above); its research-question remark on four-squares conversions is Part
  II's four-square caveat.
- **[`liveness-beyond-halting`](../liveness-beyond-halting)**: no overlap.
- **The Hilbert-tenth-problem research programme** (read-only for this
  report), `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`:
  `group_commutator_universal_substrate.md` (universal subgroup membership in
  `SL(4,Z)` along a fixed quadratic curve; the same kind of statement as Part
  II's Theorem 22.1, for a different object); `group_unipotent_input_loaders.md`
  (a different faithful free pair in `SL_2(Z)`, without the arithmetic image
  that Part I's chart uses); `heisenberg_two_generator_membership.md` (the
  same coordinate `2c − ab`; two-generator submonoids decidable; its commuting
  case is a special case of Part II's two-phase theorem, and its
  three-generator question is **not** answered by Part II);
  `group_projective_label_aligned_lanes.md` (source 03's own comparison).
- **The formal project.** The report sits in the collection, not in
  `Computability/HilbertTenthProblem`, and **placement beside a Lean/Rocq
  development confers no formal status**. Both Parts import MRDP only as a
  classical theorem; the project's formal endpoint is `Diophantine.mrdp`,
  `Diophantine.mrdp_iff` and `Diophantine.mrdp_dioph_iff`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`, lines 33,
  42, 26), described by `Lean/MRDP.md` (cited by source 03) and
  `Lean/Diophantine/Common/MRDPCore.lean` (cited by source 05); both files
  are unchanged from the sources' pins to the write. The project has
  formalized none of this report's statements: its Hilbert-tenth-problem Lean
  development has no free-group chart, Heisenberg-group, Dehn-function or
  subgroup-product module.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (Latin Modern, AMS,
microtype, booktabs, longtable, enumitem, fancyhdr, needspace, listings,
xurl, hyperref). The committed build has 62 pages: no undefined references
or citations, no multiply defined labels, no duplicate destinations.
There are no overfull boxes; the log's only box message is one underfull
line (badness 3118) in the `[write]` note on shipped file names at the
start of Section 14.

## Rerunning the programs

Both verification programs import their companion module by its delivered
name, and both write into their delivered paths: source 03's `verify.py`
writes the receipt path given on its command line, and its
`van_kampen.py` exports overwrite `examples/*.json`; source 05's `verify.py`
rewrites `verification_receipt.json` and all six `examples/*.json` relative
to its own directory's parent. **Never run them in place.** Copy `code/` and
`data/` to a scratch directory and recreate the delivered layout there
(`py` is the Python launcher on this machine; the delivered texts say
`python`):

```sh
# source 03 (needs SymPy 1.14.0)
mkdir -p r03/code r03/examples r03/verification
cp code/03-van-kampen-van_kampen.py r03/code/van_kampen.py
cp code/03-van-kampen-verify.py r03/code/verify.py
cd r03
uv run --no-project --with sympy==1.14.0 python code/verify.py --receipt verification/receipt.json
uv run --no-project --with sympy==1.14.0 python code/van_kampen.py budget 1 --relator abAB --output examples/commutator_budget_1.json
uv run --no-project --with sympy==1.14.0 python code/van_kampen.py grid 1 1 --output examples/grid_1_1.json
cd ..
# source 05 (standard library only)
mkdir -p r05/code r05/examples
cp code/05-three-phases-heisenberg_compiler.py r05/code/heisenberg_compiler.py
cp code/05-three-phases-verify.py r05/code/verify.py
cd r05 && py code/verify.py   # writes r05/verification_receipt.json and r05/examples/*.json
```

At the write (Windows; `PYTHONUTF8=1`) both passed. Source 03's run (uv
selected Python 3.13.5) reproduced the receipt and both exported
polynomials, and source 05's (Python 3.14.4) the receipt and all six
example files, each equal to the shipped file apart from line endings: the
Windows runs write CRLF, and the shipped files are LF. The other three
files of source 03 — `grid_1_1_witness.json`, `render_check.json` and
`export_check.json` — are not written by any shipped program; the witness
was rechecked at placement (all 16 residuals of `grid_1_1.json` vanish at
it). To compile a quadratic specification with source 05's compiler, run
`py code/heisenberg_compiler.py examples/multiplication_input.json out.json`
in `r05`.

## Discrepancies and disclosures

- The shipped `code/05-three-phases-build.sh` keeps the delivered layout: it
  changes to its own directory (`code/`) and runs pdflatex three times on
  `article.tex`, which is not there; it would not build this report. Use the
  build command above.
- Source 03's `SOURCES.md` and the reproduction section of Part I (Section
  14.3) name delivered paths (`code/verify.py`, `verification/receipt.json`,
  `examples/*.json`, `requirements.txt`, `arithmetic_van_kampen.tex`), and
  Part I's software section names `verification/receipt.json` and
  `code/van_kampen.py`; Part II names `code/heisenberg_compiler.py`,
  `code/verify.py`, `examples/multiplication.json` and
  `multiplication_input.json`. These are delivered names (map above);
  `[write]` notes at those places give the shipped names.
  `03-van-kampen-render_check.json` describes source 03's own 29-page PDF,
  which is not shipped.
- Source 03's `SOURCES.md` and both sources' repository sections describe
  the repository at their pins (`c58206ca1`, `433df1be3`). Every repository
  file they cite is unchanged from the pin to the write. Neither source knew
  the related repository material listed above; the report adds it (Section
  1.4 and `[write]` notes in Sections 2.2 and 29.4).
- The bounded-conjugator lemma of Part I is imported from
  Cornulier–Tessera (Lemma 2.D.2), not proved; it is needed only for the
  height bound and the bounded search. Part II's description of Roman'kov's
  paper rests on its abstract (source 05 did not read the full paper); the
  report's credit sentences rest on the same abstract and on the arXiv text of
  König–Lohrey–Zetzsche.
- The delivered title pages are replaced by one title page; each source's
  title, subtitle, abstract and status statement open its Part verbatim. The
  author line "Research report/manuscript prepared for Vladimir
  Reshetnikov" is kept, with "AI-assisted" added.
