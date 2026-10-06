# Bounded-Width Power-Set Compression

**Exact finite thresholds, choiceless infinite obstructions, and a defect
extension of Glazer's chain-fiber theorem: maps `f : 𝒫(X) → X` whose fibers
contain no `(r+1)`-element antichain, solved exactly for finite `X` and under
Choice, with the `ZF` case for `r ≥ 2` left open**

A research report dated 5 October 2026, built from one manuscript. It is an
**AI-assisted, unrefereed external manuscript**: its status box says so, and
its title page reads "Prepared for Vladimir Reshetnikov / Research manuscript
prepared with ChatGPT" (PDF author field "Research manuscript prepared for
Vladimir Reshetnikov with ChatGPT"). It contains no e-mail address, no
"prepared for private review" line and no personal data.

| Source | Batch | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 114 (non-bundle arrival) | `Bounded_Width_Power_Set_Compression.zip` (302,418 bytes, SHA-256 `f8481786…f06292`; six files at the archive root, no wrapper directory, 350,606 bytes unpacked), arrival commit `2399df2bd` ("New research reports", 5 October 2026); main file `article.tex` (1,288 lines, 21-page PDF) | `b71545625` (`b71545625fedc631edc2ead542abbfba72eb6063`, title page and bibliography entry `ProveIt`; it is the batch-98B write commit of this repository) | `99053b5d1` (batch 114) | the whole report |

**Status:** unrefereed, not formalized: no Lean or Rocq declaration exists
for any statement of this report, and its place in the collection confers no
formal status. **One statement is wrong as printed** and is corrected in a
numbered remark (Remark 9.10; next section). The delivered program checks
finite instances only; everything else rests on the written proofs.

## Trust boundaries

- **Wrong as printed, repaired.** Definition 9.1 (antichain code) asks only
  that the *range* of `Θ : 𝒫(U) → 𝒫(X)` be an antichain, not that `Θ` be
  injective. With that definition Lemma 9.2 ("`f ∘ Θ` is at most
  `r`-to-one"), Theorem 9.4 (antichain transfer) and the abstract's sentence
  that the theorem "converts any antichain code" into a finite-to-one map are
  false. Counterexample (Remark 9.10, checked in full): `X = {0,1,2}`, `r = 1`,
  `U = ℕ`, `p : X → ℕ` the inclusion, `Θ ≡ ∅`. The hypotheses hold (the range
  `{∅}` is an antichain; `p` is finite-to-one), `SC_1(X)` holds (the chains
  `∅ ⊂ {0} ⊂ {0,1} ⊂ {0,1,2}`, `{1} ⊂ {1,2}`, `{2} ⊂ {0,2}` partition
  `𝒫(X)`), and hence `SC_r(X)` for every `r`, yet the theorem says it fails
  for every `r`; `f ∘ Θ` is constant. Repair: require `Θ` injective
  (equivalently `Θ(A)`, `Θ(B)` incomparable for `A ≠ B`). Injectivity is used
  only in the proof of Lemma 9.2. The only code the manuscript constructs,
  that of Lemma 9.5, is injective, so Theorem 9.6, Corollaries 9.7–9.8,
  Theorem 10.1 and the complete `ZFC` classification stand. The printed
  statements are kept as delivered, with pointer notes at each.
- **Imported, not proved.** Glazer's `r = 1` theorem (Theorem 7.1), from his
  accepted MathOverflow answer of 2 December 2025, which the write read: it
  states exactly the three-way equivalence printed. Forster's theorem
  (Theorem 9.3), *J. Symbolic Logic* 68 (2003) 1251–1253: the write read the
  abstract only ("if there is a finite-to-one map 𝒫(X) ↠ X, then X is
  finite", a surjection arrow) and added the two-line `ZF` argument that the
  printed form for arbitrary maps follows (send `{u}` to `u`). Dilworth's and
  Sperner's theorems and the existence of a symmetric-chain decomposition are
  quoted (the recursive decomposition itself is proved).
- **Credit added by the write.** The complementary-transversal code of
  Lemma 9.5 is already in the MathOverflow thread for `r = 1` (Pruss's
  question, `A ↦ f(A ∪ (V ∖ g[A]))`, and Pruss's answer of 4 December 2025,
  `A ↦ f(h_0[A] ∪ (X_1 ∖ h_1[A]))`, giving an injection and Cantor's
  theorem). The manuscript credits Jeřábek's answer but not this code; what it
  adds is the passage to width `r` through Forster's theorem.
- **Proved in the text.** Everything else, read in full at intake and again
  at the write; no other error. The remainder `O(1)` of Theorem 6.2 is argued
  in one sentence and not made explicit.
- **The computation proves nothing beyond its cases.** `code/verification.py`
  checks symmetric-chain decompositions for `n ≤ 14`, grouped certificates for
  `n ≤ 10`, `r ≤ 5`, monotonicity for `n ≤ 300`, prints the tables and
  evaluates the asymptotic formula numerically. Nothing in it concerns the
  infinite results.
- **No priority.** "A targeted search of the inspected literature did not
  locate this precise bounded-width formulation, but absence from a search is
  not a priority proof"; the write did no literature review either.

## What it proves

`B_n = 𝒫([n])`, `W_n = C(n, ⌊n/2⌋)`; an `r`-width compression of a poset is a
map whose fibers have width at most `r`; `χ_r(P)` is the least number of
labels; `q_r(n) = χ_r(B_n)`; `δ(n)` is the least `r` admitting
`𝒫([n]) → [n]`; `N(r) = max{n : δ(n) ≤ r}`; `SC_r(X)` asserts a map
`𝒫(X) → X` with fibers of width at most `r`. Statement numbers are those of
the committed PDF (theorem counter per section; no delivered number moved).

- **Theorem 3.1, Corollary 3.2**: a finite poset of width `w` has a map to
  `[q]` with fiber widths `≤ r_i` iff `Σ r_i ≥ w` (Dilworth); so
  `χ_r(P) = ⌈w/r⌉`.
- **Theorem 4.1, Example 4.2**: `q_r(n) = ⌈W_n/r⌉`, with the middle layer as
  lower certificate and grouped symmetric chains (recursive construction) as
  upper certificate.
- **Theorem 5.1, Corollary 5.2, Proposition 5.3**: `𝒫([n]) → [n]` exists iff
  `W_n ≤ rn`, iff `r ≥ δ(n) = ⌈W_n/n⌉`; `δ = 1,1,1,2,2,4,5,9,14,26,…`;
  `W_n/n` is nondecreasing (exact ratios `2m/(m+1)`, `(2m+1)/(m+1)`).
- **Theorems 6.1–6.2**: `δ(n) = √(2/π) 2^n n^{−3/2}(1 + O(1/n))` and
  `N(r) = L + (3/2)log₂L + (1/2)log₂(π/2) + O(1)`, `L = log₂ r`.
- **Theorem 8.1, Corollary 8.2**: under `SC_r(X)`, `|f[𝒫(S)]| ≥ q_r(|S|)` for
  every finite `S ⊆ X`; no `n`-set with `n > N(r)` is closed.
- **Theorem 8.3, Corollary 8.4** (`ZF`): an infinite `X` with `SC_r(X)` is
  Dedekind-infinite, with an injection `ℕ → X` definable from `f` and an
  ordered `(N(r)+1)`-tuple (iterated hull, least-preimage orders, no countable
  choice); no Dedekind-finite or amorphous set satisfies `SC_r`.
- **Lemmas 9.2, 9.5, Theorems 9.4, 9.6, Corollaries 9.7–9.8** (with injective
  codes, Remark 9.10): if `U` is infinite, `U × 2 ≼ X` and there is a
  finite-to-one map `X → U`, then `SC_r(X)` fails for every `r`; in
  particular for every infinite `X` with `X × 2 ≼ X` and every infinite
  well-orderable `X`, so `ZFC` proves `SC_r(X)` iff `X` is finite, nonempty
  and `W_|X| ≤ r|X|`.
- **Theorem 10.1**: the profile of a hypothetical `ZF` counterexample for
  `r ≥ 2` (Dedekind-infinite, not binary-duplicable, no two-channel
  finite-to-one core, Choice fails).
- Sections 11–13: the computation, a five-stage formalization blueprint (a
  proposal) and sixteen research items; Appendix A: tables; Appendix B: claim
  ledger; Appendix C: reproduction.

Added by the write (5 October 2026), with proofs, marked `[write]`:

- **Remark 9.10 (`bwc:rem:injective`)**: the counterexample above, the repair,
  the proofs of Lemma 9.2 and Theorem 9.4 with injective codes, and the check
  of every later use.
- **Proposition 13.1 (`bwc:prop:matching`)**: the bipartite graph of research
  item 6 (`x` joined to `f({x, c_n})` for an injective `c : ℕ → X`) has
  infinite left degrees and right degrees at most `2r`; the source asserted
  "infinite left degree and bounded right degree" without proof.
- In notes: the surjective and arbitrary-map forms of Forster's theorem are
  equivalent in `ZF` (after Theorem 9.3); the variable-budget inequality of
  item 7 is the necessity half of Theorem 3.1 (item F7); the principle
  "`X × 2 ≼ X` for every infinite `X`" already gives the full classification
  (item F3, from Corollary 9.7).
- Notes: status and trust boundary; scope of the repository claim (Section
  1.4); Section 1.6 (provenance, sources as read, checks, relation to the
  repository, collected non-claims, reading conventions and notation table);
  the MathOverflow thread and the credit for the code (after Theorem 7.1);
  the plateau remark (after Proposition 5.3: `a_n = W_n/n` is strictly
  increasing from `n = 3`; the steps with ratio one are `a_2/a_1` and
  `a_3/a_2`); the remainder of Theorem 6.2; pointer notes at Definition 9.1,
  Lemma 9.2 and Theorem 9.4; the program in this directory (Section 11);
  mathlib's coverage (Section 12); the ledger; Appendix C; Section 13.1.

## What is not claimed

From the source, kept in the article (collected in Section 1.6):

- The exact finite formula is "a short synthesis of classical results of
  Dilworth and Sperner"; priority for the formulation "has not been
  established"; "no claim is made that the unresolved `r ≥ 2` question is
  known to be open in every source not inspected".
- Glazer's theorem is imported ("not reproved in full"); Forster's theorem is
  imported. Elliot Glazer "is a cited researcher, not an author or endorser".
- The full `ZF` classification for `r ≥ 2` "is posed as an open problem, not
  claimed solved".
- The verifier is "diagnostic, not foundational"; the manuscript is
  "AI-assisted, unrefereed, and not formally verified"; the research items
  and the blueprint are proposals.
- Added by the write: the antichain-transfer theorem holds only for injective
  codes.

## Further questions

Section 13.1 ("Further questions and research", `bwc:sec:further`) states
every unproved claim as an open question with its source, sketch and what is
missing (Vladimir's standing rule of 4 October 2026). **One statement of the
source is wrong as printed** (Remark 9.10, above); nothing else was found
wrong. Its 17 items F1–F17 are Conjecture 2.5, the fifteen other research
items of Section 13, and one item added by the write:

1. **F1, the `ZF` classification for `r ≥ 2`** (Conjecture 2.5 = research
   item 1): proved for finite `X` (`ZF`), in `ZFC`, and for `r = 1` (Glazer);
   open for infinite `X` in `ZF`. Theorem 10.1 profiles a counterexample; a
   positive answer to F5 would settle it; the two "routes" of Section 10.2 are
   heuristics.
2. **F2** permutation or symmetric model (the "would likely require" sentence
   is a heuristic); **F3** weakest choice principle (write: `X × 2 ≼ X` for all
   infinite `X` suffices; not compared with the named candidates); **F4**
   canonical chain splitting; **F5** finite-to-one core extraction.
3. **F6 matching formulation**: the graph assertion is now Proposition 13.1;
   the choice principle for a "two-matching saturating the left side" is open
   (the term is not defined in the source).
4. **F7** variable budgets (the finite inequality is Theorem 3.1); **F8**
   stability; **F9** enumeration ("nontrivial orbit structure" is not
   substantiated); **F10** other Peck posets; **F11** `q`-ary cubes; **F12**
   transfinite widths (with injective codes); **F13** reverse mathematics;
   **F14** formalize Forster (a proposal); **F15** definability strength,
   with the speculation of Remark 8.5 ("may be stronger … in symmetric
   models"); **F16** benchmark variants (a proposal; must state the injective
   form).
5. **F17** (write): an explicit remainder in Theorem 6.2. For `r = 2^k`,
   `4 ≤ k ≤ 60`, `N(r) − (L + (3/2)log₂L + (1/2)log₂(π/2))` lies between
   −0.5636 (at `k = 45`) and 1.6743 (at `k = 4`); not a proof.

**Independent check of the write (5 October 2026).** An adversarial check
made by the intake after the write (`74a988c32`) found no item needing a
correction. It re-checked the counterexample of Remark 9.10 by hand and by
program and audited every later use of an antichain code: Lemma 9.2 is used
only through Theorem 9.4, Theorem 9.4 only in Theorem 9.6, whose code
(Lemma 9.5) is injective, and Corollaries 9.7, 9.8 and Theorem 10.1 rest on
Theorem 9.6, so the `ZFC` classification stands. It confirmed the Forster
note, Proposition 13.1, notes F3 and F7, and the account of MathOverflow
504570 (read through the Stack Exchange API). With its own program (not
shipped) it recomputed `q_r(n) = ⌈W_n/r⌉` for `n ≤ 9`, `r ≤ 5` (upper bound
from an independently coded de Bruijn–Tengbergen–Kruyswijk decomposition;
exhaustive minimum for `n ≤ 3` and `n = 4`, `r ≤ 3`), `SC_r([n]) ⇔ W_n ≤ rn`
exhaustively for `n ≤ 4`, and `δ(1..16)` with the ranges of Corollary 5.2.
The record is a dated note at the end of Section 13.1.

## Checks made at intake

On copies (5 October 2026; Windows, Python 3.14.4, standard library only):

- At placement (batch-114 dossier): `verification.py` on a copy in 0.8 s, all
  assertions passing, output identical to the recorded report up to newline
  style; `SHA256SUMS.txt` 4/4 OK; independent checks of `δ(1..16)`, the
  `N(r)` table and the `SC_1({0,1,2})` witness. The dossier read every proof
  and found the injectivity gap; nothing else wrong.
- At the write: the verifier on a fresh copy in about 0.3 s, report identical
  to `data/verification_report.txt` up to carriage returns; both shipped
  delivered files byte-identical to the archive. The write's own program
  (not shipped) checked the counterexample in full (partition of `𝒫({0,1,2})`,
  fiber widths, constant `f ∘ Θ`), the transversal code for `U = {0,1}`, all
  24 rows of Table 1 and all 18 entries of Table 2 (including `N(26) = 10`,
  which the verifier does not print), the ratio identities for
  `1 ≤ m ≤ 200`, strict growth of `W_n/n` from `n = 3` to 300, Example 4.2
  against the recursive decomposition, and the diagnostic range of F17.
- Sources read by the write: the MathOverflow thread 504570 in full (via the
  Stack Exchange API; question by Pruss, 2 December 2025; answers by Glazer
  (accepted) and Jeřábek, 2 December, and Pruss, 4 December 2025); Forster
  (abstract and data on Project Euclid; body not read); Hu–Shen (arXiv
  abstract; the two sentences the article attributes to it not checked).
  Not read: Dilworth, Sperner, de Bruijn–van Ebbenhorst Tengbergen–Kruyswijk,
  Greene–Kleitman, Shen (2026), Glazer–Yao, FrontierMath.

## Relation to the repository

**Formal status.** No statement of this report is formalized. The
blueprint of Section 12 is a proposal. mathlib `v4.32.0` (the repository's
pin) proves Sperner's theorem (`IsAntichain.sperner`) and the LYM inequality
in `Mathlib/Combinatorics/SetFamily/LYM.lean`; no file of it mentions
Dilworth's theorem, so Stage I's "import a finite Dilworth theorem from
mathlib" is not available at that version.

**Stale claim (scoped, Section 1.4).** The source says the problem "spans
three of [ProveIt's] active surfaces: finite posets and Boolean-lattice
certificates in combinatorics; first-order ZF and cardinal arithmetic in set
theory; …". The first does not exist: at the pin `b71545625` and at the
write's base commit `bf70d7db4`, `git grep` of every `*.lean` and `*.v` file
finds no Dilworth, Sperner, symmetric chain, LYM, Lubell or Peck, and no
width of a finite poset; "Boolean lattice" occurs only in doc comments of
`Analysis/FabiusFunction/Lean/FabiusFunction/ThueMorseBooleanMobius.lean`
(signed sums over submask intervals), and antichains only in well-quasi-order
arguments (surreal and transseries libraries) and in the chain condition of
`SetTheory/Cardinals/Cardinals/Above.lean`. The second exists only in part:
first-order `ZF` is `SetTheory/ZF` (Lean and Rocq), cardinal arithmetic only
the `ZFC` large-cardinal library `SetTheory/Cardinals/Cardinals`; nothing
treats choiceless cardinal arithmetic, Dedekind-finite or amorphous sets,
finite-to-one maps or Forster's theorem ("Forster" in `*.v` files is Yannick
Forster's Coq library). The repository's self-description the source quotes
(root README, unchanged between pin and base) is correct.

**Neighbouring reports** (paths under `SetTheory/Cardinals/docs/reports/`):

- `ordinals-and-order-types/freiling-symmetry-blacklists` (same batch; **see
  also**; choiceless set theory): another exact finite extremal theory whose
  infinite form sits between choice principles over `ZF` (there
  `BPI ⇒ SAP_k ⇒ C_2 ∧ … ∧ C_{k+1}`), and which also asks for the weakest
  choice principle that suffices. No shared theorem; neither cites the other.
- `ordinals-and-order-types/naming-elementary-embeddings` cites the same
  Glazer–Yao paper (arXiv:2602.21970), motivation only here.
- Same batch and category, no shared theorem: `noisy-parity-cubes`,
  `robust-neutral-choice`, `random-bits-arithmetic-cuts`.

## Notation

A table at the end of Section 1.6 fixes the letters the source reuses or
leaves undefined, with the tempting false readings: `U ≼ X` (injection) and
`X ≼_fto U` (a finite-to-one map `X → U`; used but never defined; the macro
`\bfto` is defined and unused); `q` (bins in Theorem 3.1, a claimed label
count in Section 4, the alphabet of item 11) against `q_r(n)`; `χ_r(P)`, not
a chromatic number; `L = log₂ r` against the middle layer `L_n`; `δ` and `N`,
which satisfy only `δ(n) ≤ r ⇔ n ≤ N(r)`; `H_f`, `S_k`, `μ_k`, `x_k`; `Θ`,
`e`, `e_i`; `p`, `h`; `c`, `c_n`. No symbol was renamed.

## Labels

Every label carries the prefix `bwc:` (none existed in the repository). The
manuscript's 51 labels were prefixed before anything cited them, and all 27
references (`\cref`) were updated. The write added 41: four delivered
headings or remarks (`bwc:sec:proveit`, `bwc:sec:obvious`, `bwc:sec:routes`,
`bwc:rem:definable`), the sixteen research items `bwc:q:main` …
`bwc:q:benchmark`, the new `bwc:sec:provenance`, `bwc:rem:injective` and
`bwc:sec:further`, the 17 items `bwc:fq:…`, and `bwc:prop:matching`. The
report has 92 labels; builds of the delivered text and of this one give all
51 delivered labels the same numbers (aux files compared). Remark 9.10 is the
last numbered statement of Section 9 and Proposition 13.1 the only numbered
statement of Section 13, so no delivered theorem or equation number moved.

## Files

```text
README.md                        this guide (replaces the delivery README.md)
article.tex                      the report (delivered article.tex; labels prefixed, [write] additions)
article.pdf                      compiled report, 29 pages
code/verification.py             exact finite checks and tables (standard library; writes its report beside itself)
data/verification_report.txt     the program's recorded output
```

`code/verification.py` and `data/verification_report.txt` are byte-identical
to the delivery (checked again at the write).

**Not shipped**, recoverable from the arrival commit (next section): the
delivered 21-page PDF (284,625 bytes), `SHA256SUMS.txt` (four entries, all
verified at placement) and the delivery `README.md` (2,216 bytes), staged at
placement and replaced by this guide (summarized under "From the delivery
README").

**Delivered text that names the delivery layout.** The title page says the
accompanying archive contains the source, the compiled PDF and the verifier;
Section 11 and Appendix C name `verification.py` and
`verification_report.txt` at the archive root and tell the reader to run
`python3 verification.py` "from the extracted archive". Appendix C also offers
"the PDF skill's `latex_to_pdf.py` wrapper", a tool of the environment in
which the manuscript was generated, not part of the delivery or of ProveIt.
The text is kept as delivered; dated notes in Section 1.6, Section 11 and
Appendix C say so.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 2399df2bd:docs/incoming/Bounded_Width_Power_Set_Compression.zip > "$T/bwc.zip"
sha256sum "$T/bwc.zip"   # f84817867be61c97d50bbc42c6cbd1a150723e578b63ec33a743c93ef0b06292, 302,418 bytes
mkdir "$T/bwc" && cd "$T/bwc" && unzip -q ../bwc.zip   # six files, no wrapper directory
sha256sum -c SHA256SUMS.txt
```

## Rerun the checks (on a scratch copy)

Python 3.8 or later (it uses `math.comb`), standard library only.
The program writes `verification_report.txt` **beside itself**
(`Path(__file__).with_name`), so run in place it would create
`code/verification_report.txt`; run it on a copy:

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/ordinals-and-order-types/bounded-width-power-set-compression
T=$(mktemp -d); cp "$R/code/verification.py" "$T/"; cd "$T"
python3 -I -B verification.py > out.txt     # under a second; exits nonzero on a failed assertion
diff <(tr -d '\r' < verification_report.txt) "$R/data/verification_report.txt" && echo same
```

Tested at the write (Windows, `py` for `python3`): about 0.3 s, report
identical up to carriage returns.

## Build the PDF

pdfLaTeX (fontenc, inputenc, mathpazo, geometry, amsmath, amssymb, amsthm,
mathtools, microtype, aliascnt, booktabs, tabularx, array, longtable,
multirow, float, enumitem, xcolor, fancyhdr, graphicx, tikz, hyperref,
cleveref); the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 5 October 2026, and
rebuilt after the independent check: 29 pages (unchanged); no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, and no overfull or
underfull boxes. A build of the delivered text gives 21 pages, equally clean.
The write's one layout change is a `\clearpage` before Appendix B, which kept
its heading from being stranded at the foot of a page.

## From the delivery README

The delivery `README.md` (replaced by this guide) described a "21-page
research manuscript", listed the source, the US-Letter PDF, the verifier, its
output and `SHA256SUMS.txt`; summarized the main results (the formula
`ceil(binomial(n, floor(n/2)) / r)`, the self-indexed criterion
`binomial(n, floor(n/2)) <= r*n`, the three choice-free infinite results, and
the `ZF` case for `r >= 2` "stated explicitly as an open conjecture, not as a
solved theorem"); gave the `latexmk` and `python3 verification.py` commands;
and stated: "AI-assisted, unrefereed, and not formally verified in Lean or
Rocq. … Historical priority for the new formulation and intermediate
observations has not been established."

## Rights

Repository contents are MIT-0. The package contains no OEIS or other
third-party data. The MathOverflow thread was read through the Stack Exchange
API (content CC BY-SA 4.0); only short phrases are quoted in the article's
notes and nothing of it is shipped. Nothing was submitted anywhere.

## Provenance

- Sources cited by the manuscript: Pruss, Glazer, Jeřábek et al.
  (MathOverflow 504570, December 2025), Dilworth (1950), Sperner (1928),
  de Bruijn–van Ebbenhorst Tengbergen–Kruyswijk (1951), Greene–Kleitman
  (1976), Forster (JSL 2003), Hu–Shen (Logic J. IGPL 2025), Shen (JSL 2026),
  Glazer–Yao (arXiv 2026), FrontierMath (arXiv 2411.04872), and ProveIt at
  `b71545625`. The write added no bibliography entry.
- Repository input: none beyond the pin's self-description (root README,
  unchanged between `b71545625` and the write's base commit `bf70d7db4`).
- Batch 114 of `docs/incoming` (non-bundle arrivals); arrival `2399df2bd`,
  placement `99053b5d1`, written 5 October 2026. Single source, so no merge
  choices. The delivered `article.tex` is shipped under the same name; the
  delivered program and output as listed above.
