# The Surreal Numbers as a Real Vector Space

**Conway–Hahn coordinates, Hamel bases, strong duality, canonical operators, and the Euler quotient**

This is a research report dated 1 October 2026, built from three
manuscripts written independently on that day in answer to one question:
what is the natural basis of `No` over `ℝ`? Author lines: source 51,
"Research report prepared for Vladimir Reshetnikov" ("A research report for
the ProveIt project"); source 52, "Research article … Prepared for Vladimir
Reshetnikov"; source 53, "Independent research report prepared for Vladimir
Reshetnikov".

| Source | Manuscript | Archive (inner directory, main file; delivered PDF): title | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 51 | batch 73X, manuscript 51, base | `surreal_numbers_real_vector_class` (`surreal_numbers_real_vector_class_package/surreal_numbers_real_vector_class.tex`, 2,321 lines; 32 pp. Letter): *The Surreal Numbers as a Real Vector Class: Conway–Hahn Coordinates, Hamel Bases, Strong Duality, and Canonical Operators* | `f7e7d8607` | `26abf259b` | the spine, whole: Sections 1, 3–6, 10, 11, 18, 20–22 and the first parts of Appendices A and B, with the diagonal maps moved to Section 7 |
| 52 | batch 73X, manuscript 52 | `surreal_real_vector_spaces` (`surreal_real_vector_spaces/article.tex`, 1,054 lines; 29 pp. Letter): *Surreal Numbers as a Real Vector Space: Canonical Hahn Coordinates, Hamel Obstructions, and the Euler Quotient* | `f7e7d8607` | `26abf259b` | merged, whole: Section 1.4, parts of Sections 3–6, Sections 9 and 12, Theorems 10.11, 11.6, 11.12, Part IV (Sections 13–17), Sections 21.8, 22.2, Appendices A.2 and C.1 |
| 53 | batch 73X, manuscript 53 | `surreal_vector_space_over_R_article` (no inner directory; `surreal_vector_space_over_R.tex`, 1,819 lines; 28 pp. Letter): *Surreal Numbers as a Vector Space over ℝ: Hamel Bases, Hahn Bases, Canonical Coordinates, Valuation Layers, and Linear Operators* | `f7e7d8607` | `26abf259b` | merged, whole except the shared statements: Section 1.5, parts of Sections 3–6, Sections 7 and 8, Section 11.3, Sections 19, 20.4, 21.9, 22.3, Appendix A.3 |

All three archives arrived in `3172be896` (batch 73 of `docs/incoming/`,
cluster X) and record the same pin, `f7e7d8607` (each in its own text). They
do not know each other: the longest common word run of any pair is a
bibliography entry. Source 51 is the base because it works on the whole
class `No` under the weakest foundations (NBG with global choice, as does
52; 53 assumed more) and covers the most of the common spine.

**Status.** Three AI-assisted, unrefereed manuscripts. Every theorem has a
written conventional proof; source 52's program checks finite exact
instances only. **Nothing in this report is formalized**; no independent
proof review has been done; no manuscript claims literature-wide priority
or the solution of a named published problem.

```
README.md                                  this guide
article.tex                                the report: standalone LaTeX (pdfLaTeX), internal bibliography
article.pdf                                the compiled report, 88 pages (unnumbered title page,
                                           contents pages i–iii, then pages 1–84)
52-euler-quotient-PROOF_AUDIT.md           source 52's author-side proof and verification audit, as delivered
code/52-euler-quotient-verify.py           source 52's exact finite checks (Python 3.10+, standard library only)
data/52-euler-quotient-verification.json   source 52's recorded run: 39 checks, all passed
data/52-euler-quotient-sources.json        source 52's repository-pin and reading record, as delivered
```

Sources 51 and 53 shipped no code. For all three sources the delivered
README and PDF are not shipped: this README replaces them, and `article.pdf`
is a build of this text. Source 51's delivered README and checksum ledger
(`SHA256SUMS.txt`, verified 2/2 and retired at placement) name
`surreal_numbers_real_vector_class.tex` and `.pdf`; source 53's README names
`surreal_vector_space_over_R.tex` and `.pdf`. Source 51's `article.tex`
was staged unprefixed at placement and is rewritten here; the other
manuscripts are not shipped and survive in `3172be896`.

## Delivery names in shipped files

Source 52's four support files are shipped byte-identical under prefixed
names:

| Delivered as | Shipped as |
|---|---|
| `code/verify.py` | `code/52-euler-quotient-verify.py` |
| `data/verification.json` | `data/52-euler-quotient-verification.json` |
| `audit/PROOF_AUDIT.md` | `52-euler-quotient-PROOF_AUDIT.md` |
| `audit/sources.json` | `data/52-euler-quotient-sources.json` |

Their text still uses the delivery names: the audit names `code/verify.py`
and `sources.json`; the program's docstring says `python code/verify.py`
and that it writes `../data/verification.json`. The audit cites source 52's
own numbering: its Theorems 3.2, 4.2, 4.4, 6.1, 6.2, 6.4, 8.3, 8.4, 8.6,
Proposition 8.7, Theorems 9.1, 9.3, Proposition 9.5 and Theorem 10.1 are
Theorems 5.20, 9.2, 9.4, 12.1, 12.2, 11.12, 13.3, 13.4, 13.6, Proposition
13.7, Theorems 14.1, 14.3, Proposition 14.5 and Theorem 15.1 here. The
article prints the shipped names (Section 17).

## Labels and numbering

Every label in `article.tex` carries the prefix `rvs:`. Source 51's 109
labels (the staged `article.tex` had 109) are kept as `rvs:<original>`.
Source 52's 63 labels are all kept as `rvs:eu:<original>` (named after its
Euler-quotient package). Of source 53's 61 labels, 54 are kept as
`rvs:cv:<original>` (named after its convex-subspace and positivity
material); its seven equation labels on displays that duplicate source 51's
(`eq:CNF`, `eq:natural-valuation`, `eq:geometric-one`, `eq:slice-dim`,
`eq:gt`, `eq:graded-group-algebra`, `eq:support-projection`) are not printed,
and their references point to source 51's displays. Text written for this
report added 23 labels `rvs:w:…`. **249 labels in all.** Where a statement of
52 or 53 is printed once under source 51's wording, its label sits on the
printed statement (for example `rvs:cv:thm:hahn-basis` on Theorem 4.2).
Section labels of 52 and 53 sit on the sections that now print their
material. Every label in a lemma, proposition, corollary, definition,
example, remark, question, warning or principle carries a cleveref type
(`\label[remark]{…}`), so references print the right name; source 51's
delivered PDF printed "theorem" for its corollaries and propositions.

The report is new, so its numbering is new: 22 sections in five Parts and
three appendices. Part I (Sections 3–5) Hahn coordinates and Hamel bases;
Part II (6–9) canonical linear structure; Part III (10–12) strong maps,
duals and topology; Part IV (13–17) the Euler quotient (source 52 alone);
Part V (18–22) monomial symmetries, the recommendation, relation to the
collection, research questions, conclusions. 53 research questions are
numbered: 20 of source 51 (Sections 21.1–21.7), 8 of source 52 (21.8) and
25 of source 53 (21.9). The remaining 2 of 52's 10 and 6 of 53's 31 are printed
inside the overlapping questions of 51 (foundations, definability,
topologies, derivation matrix, formalization) or, for 53's "Strongly linear
matrices", as Remark 21.42, answered by Theorem 10.3. (The intake dossier counted
17 questions for 51 and 34 for 53; the delivered sources have 20 and 31.)

Text written for this report is marked **[write]**. It comprises Section 2
(assembly, conventions, the table of notions and symbols, the tempting false
readings), Section 20.5 (formal status), Appendix C (provenance), and the
[write] notes at the seams.

## Setting and notation

The work is in NBG with global choice (ZFC for sets; every support is a
set), and in the ω-convention: normal forms `Σ r_β ω^{γ_β}` with
reverse-well-ordered support, `v(x) = −lead(x)`. Source 52 writes
`t^γ = ω^{−γ}` (well-ordered supports, `v = min supp_t`); its material keeps
that convention, with its support written `supp_t`. The valuation is the
same function in all three sources.

Symbols renamed from the sources (Section 2.3 of the article has the full
table):

- 52's `E_Γ`, `C_Γ` (finite-monomial part of `H_Γ = ℝ((t^Γ))` and its valuation
  closure) → `Fin_Γ`, `Lf_Γ`; 52's `E_No` → `No_fin`. **Not** the three-duals
  report's `E_Γ(V)`, `C_Γ(V)`: with `V = ℝ` those are all of `H_Γ`.
- 52's Euler operator `D` → `𝔇`. In ω-exponents `𝔇 ω^β = −β ω^β`, so `𝔇` is
  51's `D_d` with `d = −id`, not `D_id`; on real exponents `D_ct = −𝔇`.
  The write (`9265235fd`) left three bare `D` of 52 unrenamed: the commutant
  condition `TD = DT` in Theorem 1.2(2) and in (14.1) (Theorem 14.1), and
  the module action `Xx = Dx` in Proposition 13.2. They now print `𝔇`, each
  marked by a `% ed.` comment in `article.tex`; no other bare `D` means the
  Euler operator (the remaining ones are a division ring in Section 5, sets
  of distances in Section 11, a generic diagonal derivation in Theorem 18.5
  and an exponent cut in Section 21). The shipped program
  `code/52-euler-quotient-verify.py` still writes `D` in its check names.
- 52's `𝔠` (typed `\ct`) → `\cont`; 51's `ct` is the constant term `[ω^0]`.
- 53's `𝓗_A`, `𝓗_A^fin` → 51's `H(A)`, `H(A)^fin` (sans-serif); 53's `𝓜` → `𝔐`.
- 51's and 53's real Vandermonde parameter `t` → `s` (`t` is 52's Hahn variable).
- 53's staged Hahn fields `V_α` → `W_α` (51's `V_α` are birthday spans).
- 53's leading-exponent symbol printed `le` now prints `lead`.

The collection's `NOTATION.md` recommends `F_Γ` for the real Hahn workspace;
this report keeps 52's `H_Γ` because `F_{≤γ}` is the dominance flag of 51
and 53. `NOTATION.md` has no entry for this report yet.

## What the report claims

Shared core (each printed once, other proofs as second routes):

| Result | Here | Sources | Status |
|---|---|---|---|
| Monomials are a Hahn basis; coordinate model | Thm 4.2, Thm 3.6, Cor 3.7 | 51, 52, 53 | classical restatement (Conway normal form) |
| Monomials independent; Hamel basis of `No_fin` only | Prop 4.5, Prop 4.7 | 51, 52, 53 | elementary |
| No set spans `No` | Thm 5.1 | 51, 52, 53 (two proofs) | elementary |
| Class Hamel basis in NBG + global choice, may contain all monomials | Thm 5.3, Prop 5.4 | 51, 52, 53 (three proofs) | elementary; 53's MK/ETR hypothesis corrected to GBC |
| Proper class of infinite-support basis vectors; no set repair; unbounded support cardinality | Thm 5.7, Cor 5.8, Thm 5.9, Thm 5.10, Rem 5.12 | 51, 52, 53 | elementary, three strengths |
| `dim H(A) = |ℝ|^{|A|}`, finite part `|A|`, quotient `|ℝ|^{|A|}`; Vandermonde family | Thm 5.15, Cor 5.16 | 51, 53 | Erdős–Kaplansky + elementary |
| `dim H_Γ/Fin_Γ = dim H_Γ = |H_Γ|`; `= 𝔠` for countable or real `Γ` | Thm 5.20, Cor 5.21 | 52 | new packaging of the classical Vandermonde method |
| Support projections; cut decompositions; graded layers; `gr No ≅ ℝ[No]` | Thm 6.1, Cor 6.2, Prop 6.5, Rem 6.6, Thm 6.7 | 51, 52, 53 | elementary |
| Coordinate-subspace classification on `H_Γ` | Prop 6.3 | 52 | elementary |
| Convex subspaces ↔ initial exponent classes | Thm 6.10 | 53 | **classical** (Hahn, Conrad); direct proof |
| Diagonal calculus; commutant of coordinate projections | Prop 7.1, Thm 7.3 | 51, 53 | elementary |
| Positive diagonal operators; positive support projections | Thm 7.4, Cor 7.5 | 53 | elementary; not found in the collection |
| Projection-and-shift commutant is `ℝ·id` | Cor 7.6 | 53 | elementary |
| Finite real systems coefficientwise; rank transfer | Thm 8.1, Thm 8.2 | 53 | elementary; formal special case on the purely infinite omnific ideal |
| Reduced echelon basis; no valuation basis; no best approximation | Thm 9.2, Thm 9.4, Prop 9.5 | 52 | **classical** in valued-vector-space theory; direct proofs |
| No projective Hamel basis invariant under reweightings; the shear | Thm 9.6, Section 9.4 | 52 | new |
| Strong maps = Hahn-compatible column families | Thm 10.3 | 51 | new packaging; the three-duals report has the `K`-linear analogue (its Thm 3.2) |
| Strong real dual: summation-finite weights (class), RWO weights (slice) | Thm 10.7, Thm 10.11 | 51, 52 | elementary |
| Order-bounded dual of `No` is zero; positive maps on any non-Archimedean `K ⊋ ℝ` vanish | Thm 11.2, Cors 11.3, 11.5, Prop 11.6 | 51, 52 | elementary |
| Set-indexed nets eventually constant; sets uniformly discrete; `No_fin` closed; trichotomy | Thm 11.8, Cors 11.10–11.11, Thm 11.12, Cor 11.13, Thm 11.15, Thm 11.18 | 51, 52, 53 | elementary, three routes |
| Completion `Lf_Γ`; cofinality and cyclicity; enlargement; invisible functionals | Thms 12.1, 12.2, Prop 12.3, Thm 12.4, Lem 9.3 | 52 | **re-proof**: diagonal case of three-duals Thms 4.2, 4.5, 4.6, 10.1, Lemma 4.4, Prop 5.1; Thm 12.4 parallels its Thm 6.4 |
| Euler package: torsion, finite resonance, `ℝ(X)`-structure of `Q_Γ` of dimension `𝔠`, factorial witness, automatic strongness of the Euler commutant, nonsplitting, no divisible submodule, lift ideal `J_Γ`, two layers | Part IV (Prop 13.2–Thm 15.1, Cor 15.2) | 52 | **new to the collection**; priority not certified by 52 |
| Monomial automorphisms `T_{χ,φ}` and converse | Thm 18.1 | 51 | **re-proof**: exponent-rigidity Prop 8.3 (χ = 1), omnific-preserving (5.1) and Thm 5.1; class-level converse only is new |
| Dilation-invariant strong functionals are `ℝ·ct` | Thm 18.3 | 51 | new |
| Diagonal derivations `D_d` and converse | Thm 18.5 | 51 | **re-proof** of the forward direction: omnific–Diophantine (7.1), Lemma 7.1, (16.1), Lemma 16.2; converse new but short |
| `ω^{γ_i}` algebraically independent ⇔ `γ_i` ℚ-independent; `{ω^{ω^α}}` | Thm 18.7, Cor 18.9 | 51 | classical |
| Scalar change to `k ⊆ ℝ` | Prop 4.14 | 51 | elementary |

## What the report does not claim

Every limitation of the three sources is printed: 51's claim-status and
title-page status (Section 1.3 and after it), 52's status, provenance and
"what has not been supplied" (Section 1.4, Appendices A.2 and C.1), 53's
source and priority discipline, title-page note and verification boundary
(Sections 1.5, 20.4). In particular:

- no cardinal-valued dimension of the proper class `No` is asserted;
- the class Hamel basis is an existence statement under a stated class
  theory, not a canonical or definable basis, and no algorithm;
- no explicit spanning Hamel basis of `H_Γ` or `No`, no classification of
  invariant subspaces, no all-rank Euler localization (52);
- `ℝ(X)`-linear independence is not algebraic or differential-algebraic
  independence; `𝔇` is not the Berarducci–Mantova derivation and nothing is
  claimed about compatibility with the surreal exponential;
- the topology statements concern set-indexed nets only;
- 52's 39 checks are finite exact identities; they prove no infinite
  statement;
- novelty is not certified by any source; the "new" entries above mean only
  that the collection had no such statement on 1 October 2026.

Corrections made at the write (each marked [write]): 53's foundation for
the class basis (MK or GBC + ETR → GBC suffices); 53's "unique natural
coordinate directions" and "every exponent symmetry merely permutes its
vectors" (canonical relative to the omega map; 52's shear and reweightings
are order-preserving strong automorphisms that move monomials); classical
status of 53's convex-subspace classification and 52's echelon and
no-valuation-basis theorems; 53's DOI for Berarducci–Mantova (`…/JEMS/762`,
another paper → `…/JEMS/769`); 52's page range for Kuhlmann (723–735 →
723–736). The arXiv identifiers 2509.22374, 2403.05827 and 2010.01983 were
checked on arXiv at the write.

## Relation to the collection and formal status

No other report of the collection treats `No` as a real vector space; the
neighbours touch it in side remarks only. Three groups of statements here
re-prove collection results and are printed as pointers with second routes
(Sections 12 and 18, and the opening of Part IV):

- [`../../surcomplex/three-duals-of-hahn-vector-spaces/`](../../surcomplex/three-duals-of-hahn-vector-spaces/):
  52's completion section is its diagonal case, by the embedding
  `x ↦ Σ t^γ (x_γ e_γ)` into `V((t^Γ))`, `V = ℝ^{(Γ)}` (Section 12 gives the
  dictionary); its Theorem 3.2 is the `K`-linear analogue of Theorem 10.3.
- [`../exponential-automorphism-rigidity/`](../exponential-automorphism-rigidity/)
  (Proposition 8.3, Theorem 8.4) and
  [`../omnific-preserving-automorphisms/`](../omnific-preserving-automorphisms/)
  ((5.1), Theorem 5.1): 51's monomial automorphisms. Theorem 8.4 also
  answers part of 51's question on exponential rigidity (Research question
  21.14).
- [`../omnific-diophantine-geometry/`](../omnific-diophantine-geometry/)
  ((7.1), Lemma 7.1, (16.1), Lemma 16.2) and
  [`../tail-spans-and-differential-transcendence/`](../tail-spans-and-differential-transcendence/)
  ((7.2)): 51's diagonal derivations and 52's Euler operator.
- [`../independent-surreal-copies/`](../independent-surreal-copies/) proves
  algebraic independence of other families; related to Corollary 18.9, not
  the same.

Placement in `Algebra/SurrealNumbers`, beside its Lean development, confers
no formal status, and `FORMALIZATION.md` maps no `rvs:` label. The Lean
development formalizes these special cases and ingredients (Section 20.5):
`Surreal.Foundations.SmallNormalForm.cutEvaluationOrderRingIso` (the
universe-relative coordinate model);
`Surreal.Foundations.SignSequence.StronglySummable`, `strongSum`,
`coeff_normalForm_strongSum` (strong summation);
`Surreal.Foundations.SignSequence.omnificPurelyInfiniteCoeff`,
`omnificPurelyInfinite_eq_zero_iff`, `omnificPurelyInfinite_linear_coeff_iff`
(coefficient separation and finite real systems on the purely infinite
omnific ideal only); `Surreal.ModuleKernelBasis` (generic kernel bases);
`Surreal.Foundations.SignSequence.exponentAutomorphism` (`T_{1,φ}`). Source
53's plan L1–L7 (files under `Surreal/Linear/`, none of which exists) is a
proposal.

## Build

From this directory (pdfLaTeX; MiKTeX or TeX Live with `tcolorbox`):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed build has no errors, no undefined references or citations,
no multiply-defined labels, no duplicate destinations and no overfull boxes;
one font-substitution warning remains (`T1/lmr/bx/sc`, the small-capital
"ProveIt" in the bold heading of Section 20.4). Every font is embedded Type 1.
Build in a scratch copy: commit `article.pdf`, not the auxiliary files.

## Rerunning source 52's checks

The program always writes `../data/verification.json` relative to its own
directory, so run it on a copy laid out under the delivered names (running
it in place would create an unprefixed `data/verification.json` beside the
shipped record):

```sh
mkdir -p /tmp/rvs52/code /tmp/rvs52/data
cp code/52-euler-quotient-verify.py /tmp/rvs52/code/verify.py
python3 /tmp/rvs52/code/verify.py          # prints "PASS: 39 exact finite checks"
python3 -c "import json; print(json.load(open('/tmp/rvs52/data/verification.json')) == json.load(open('data/52-euler-quotient-verification.json')))"
```

A rerun on 1 October 2026 (Python 3.14.4, Windows) took under 2 s, passed
all 39 checks and wrote a record JSON-equal to the shipped one. On Windows
the program writes the record with CRLF line endings (text-mode
`Path.write_text`), so compare as JSON, not byte for byte; the shipped
record is LF. Use `py` where `python3` does not resolve.

## Provenance

Appendix C of the article records the provenance: three manuscripts of
batch 73X (51, 52, 53), each pinned to `f7e7d8607`, arrived in
`3172be896`, placed in `26abf259b`; what each contributed; and where the
merge had to choose (base 51; shared statements printed once in 51's
wording except the window dimension, which carries 53's two extra clauses;
statements of different scope printed side by side; repository results as
pointers; 51's diagonal maps moved beside 53's; 51's dilation-invariant
dual kept with the dilations it uses; six overlapping questions printed
once). Appendix C also prints the three sources' abstracts and source 52's
own provenance and nonclaims.
