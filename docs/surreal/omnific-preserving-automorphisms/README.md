# Omnific-Preserving Automorphisms

**Convex-scale stabilizers, definable constants, nondefinable monomials, and algebraic-parameter rigidity**
Merged research report from nine manuscripts written independently and dated
23 September 2026: items 02, 04, 08 and 09 of batch 26, placed in `f4c9504`
(they keep those numbers here); item 05 of batch 28, placed in `c6359e4`
as an addition and numbered 10 here; items 03, 04 and 05 of batch 30,
placed in `21375f8` as an addition and numbered 11, 12 and 13 here; and item
07 of batch 31, placed in `9d28e28` as an addition and numbered 14 here.
Prepared for Vladimir Reshetnikov.

```
article.tex                                 the report, standalone LaTeX with an internal bibliography
article.pdf                                 the compiled report, 104 pages
README.md                                   this guide
02-parameter-rigidity-source_audit.md       source 02's source and novelty audit, as delivered
04-preserving-automorphisms-source_audit.md source 04's source and claim audit, as delivered
10-support-cut-source_audit.md              source 10's source, proof and novelty audit, as delivered
11-coefficient-gaps-SOURCE_AUDIT.md         source 11's source and novelty audit, as delivered
12-automatic-strongness-SOURCE_AUDIT.md     source 12's source, proof and novelty audit, as delivered
13-omnific-isomorphisms-SOURCE_AUDIT.md     source 13's source, novelty and verification audit, as delivered
14-automatic-summability-SOURCES.md         source 14's repository snapshot, literature and novelty statement, as delivered
code/
  09-omnific-preserving-verify_finite_identities.py   source 09 checks (standard library; prints only)
  09-omnific-preserving-Makefile                      source 09's build/check targets (delivered
                                                      file names; they do not build this report)
  04-preserving-automorphisms-verification.py         source 04 checks (SymPy; writes a JSON report)
  04-preserving-automorphisms-build.sh                source 04's build script (compiles its own
                                                      omnific_automorphisms.tex; not this report)
  08-integer-part-symmetries-verify.py                source 08 checks (standard library; always
                                                      writes verification.json beside itself)
  02-parameter-rigidity-verify.py                     source 02 checks (standard library; writes
                                                      verification.json beside itself by default)
  02-parameter-rigidity-Makefile                      source 02's build/check targets (delivered
                                                      file names; they do not build this report)
  10-support-cut-verify.py                            source 10 checks (standard library; writes
                                                      verification.json beside itself by default)
  10-support-cut-Makefile                             source 10's build/check/clean targets (delivered
                                                      file names; they do not build this report)
  11-coefficient-gaps-verify_finite_models.py         source 11 checks (standard library; prints, and
                                                      writes a file only with --output)
  11-coefficient-gaps-Makefile                        source 11's build/test/clean targets (delivered
                                                      file names; they do not build this report)
  12-automatic-strongness-verify.py                   source 12 checks (standard library; writes
                                                      verification.json beside itself by default)
  12-automatic-strongness-Makefile                    source 12's pdf/check/clean targets (delivered
                                                      file names; they do not build this report)
  13-omnific-isomorphisms-verify.py                   source 13 checks (standard library; writes
                                                      ../data/verification.json by default)
  13-omnific-isomorphisms-build.sh                    source 13's build wrapper (delivered layout;
                                                      it does not build this report)
  14-automatic-summability-verify.py                  source 14 checks (standard library; always
                                                      writes ../data/verification.json relative
                                                      to its own directory; no output option)
data/
  09-omnific-preserving-verification_output.txt       source 09's recorded run
  04-preserving-automorphisms-verification_report.json  source 04's recorded run (7,062 assertions)
  04-preserving-automorphisms-requirements.txt        pins sympy==1.14.0
  04-preserving-automorphisms-build_audit.json        source 04's build record for its own PDF
  08-integer-part-symmetries-verification.json        source 08's recorded run (9,469 checks)
  02-parameter-rigidity-verification.json             source 02's recorded run (7,041 assertions)
  02-parameter-rigidity-build_audit.json              source 02's build record, with SHA-256 hashes
                                                      of its delivered files
  10-support-cut-verification.json                    source 10's recorded run (28,668 assertions)
  10-support-cut-build_audit.json                     source 10's build record, with SHA-256 hashes
                                                      of its delivered files
  11-coefficient-gaps-verification.json               source 11's recorded run (3,880 assertions)
  11-coefficient-gaps-build_report.json               source 11's build record for its own PDF (no hashes)
  12-automatic-strongness-verification.json           source 12's recorded run (17,774 assertions)
  12-automatic-strongness-BUILD_AUDIT.json            source 12's build record, with SHA-256 hashes
                                                      of seven delivered files
  13-omnific-isomorphisms-verification.json           source 13's recorded run (13,885 assertions)
  13-omnific-isomorphisms-BUILD_REPORT.json           source 13's build record for its own PDF (no hashes)
  14-automatic-summability-verification.json          source 14's recorded run (four check groups, all passed)
```

Every label in `article.tex` carries the prefix `opa:` (316 labels). Source
02's part carries the sub-prefix `opa:par:` (43 labels), the material added
from source 10 carries `opa:sc:` (30 labels), Part III, from sources 11,
12 and 13, carries `opa:as:` (110 labels, besides `opa:part:as`), and Part IV,
from source 14, carries `opa:cm:` (29 labels, the part label `opa:cm:part`
included). These
prefixed labels identify the assembled report; the earlier placed base used
source-local labels. The batch-28 addition renamed and removed no label and
changed no existing theorem, section or equation number: its material is
appended at the ends of Sections 3, 4, 6, 7, 9, 10 and 11. The batch-30
addition likewise renamed and removed no label; its Part III (Sections 20–32)
sits after Part II and before the appendices, and a comparison of the
auxiliary files of the builds before and after it shows all 176 earlier labels
with unchanged numbers. The batch-31 addition likewise renamed and removed no
label (287 kept, 29 added); its Part IV (Sections 33–37) sits after Part III and
before the appendices, and the same comparison shows all 287 earlier labels with
unchanged numbers. The [formalization ledger](../../FORMALIZATION.md)
lists this report's statements in its inventory, all **Pending**; its line
anchors predate the batch-28, batch-30 and batch-31 additions. No implementation mapping
cites an `opa:` label. The repository now has Lean code constructing the
omnific rings themselves (`Surreal/Foundations/OmnificIntegers.lean`, for ring
clauses of the Diophantine report), but none for any statement of this report;
the earlier sentence here that there was no Lean code about omnific integers
is out of date.

## Nine sources, one report

| | Manuscript | Repository pin | Contributes |
|---|---|---|---|
| **09** | *Omnific-Preserving Automorphisms: convex-scale stabilizers, definable constants, and nondefinable monomials* | `fb5c4b5` | The base text and structure. The criterion for any characteristic-zero `k` and any unital coefficient ring (Theorem 3.3, with 04's proof) and its derivation form (Theorem 3.4). The operator form (Corollary 3.5), the rank dichotomy (Theorem 4.13) and the strong factorization (Theorem 5.1). The finite-rank derived-length bound `r−1` (Theorem 6.3), sharp for `Q^r` also for the abstract group (Theorem 6.6). The `R^κ` actions and nonsolvable stabilizers (Theorems 7.6, 7.7). Set-parameter nondefinability (Theorem 9.1), and no definable valuation-representative rule (Theorem 9.4). The projections and truncation (Theorem 8.2). Files prefixed `09-omnific-preserving-`. |
| **04** | *Automorphisms Preserving the Omnific Integers: a convex-support criterion, fixed fields, and nondefinability of Conway monomials* | `fb5c4b5` | The import-free proof of the criterion through the logarithmic character, which is the proof of record for `No` (Theorem 3.3). Exact displacement (Theorem 4.2) and the common-shift exponential–logarithm correspondence (Theorems 4.7, 4.8). The bottom-subgroup fixed field (Theorem 4.15), separation, and the relative Hahn hull (Theorem 7.4, Corollary 7.5). The commutator formula (Theorem 6.8). The one-term class and the `RV` sort (Remark 9.5). The real axis inside the leading-term kernel (Theorem 10.2). Files prefixed `04-preserving-automorphisms-`. |
| **08** | *What the Omnific Integer Part Remembers: coefficient reconstruction, convex-scale automorphisms, nondefinable monomials, and an explicit wreath product* | `befe739` | The divisibility-free threshold for single flows (Theorem 4.10) and phase shears (Theorem 4.17). The faithful `Z ≀ Z` with exact commutator leading terms (Theorems 6.8, 6.10). The order formula on `Oz` (Lemma 8.1) and the floor map (Theorem 8.2). The wild coefficient lift (Proposition 10.3) and the Gaussian fixed field `Q` (Corollary 10.4). Files prefixed `08-integer-part-symmetries-`. |
| **02** | *Algebraic-Parameter Rigidity of the Omnific Integers: strong cancellation, finite-type embeddings, and nonalgebraizable formal flows* | `fb5c4b5` | All of Part II (Sections 12–19). Files prefixed `02-parameter-rigidity-`. |
| **10** | *Omnific Integers Do Not Determine Surreal Monomials: exact support-cut stabilizers, fixed fields, and parameterwise nondefinability* (batch 28, item 05) | `58cd8e1` | A fifth proof of the criterion, in the support-cut form, with its least-forbidden-shift proof as a second route (Theorem 3.8); necessity without strongness (Remark 3.9); Archimedean blocks (Proposition 3.10). Twists with a general profile and their fixed fields, finite orbits and algebraic independence (Theorems 4.18, 4.20, Corollary 4.21, Proposition 4.22). The set-sized definable-closure bound (Proposition 7.8). The two-term witness (Theorem 9.8) and the nondefinability of simplicity and of the Gonshor exponential (Theorem 9.10). Question 11.7. Files prefixed `10-support-cut-`. |
| **11** | *Coefficient Gaps and Proper Self-Embeddings of the Surreal Field: omnific preservation, topological dichotomies, and nonconjugate copies* (batch 30, item 03) | `cf56b89` | Base of the embedding sections of Part III: the bottom-gap classification (Theorem 26.3), Taylor admissibility and the coinitiality criterion (Theorem 26.6, Corollary 26.7), the explicit embedding (Theorem 27.3), closed images and the continuity dichotomy (Theorems 28.1, 28.3, 28.4), nonelementarity (Theorem 29.1), the ordinary overlap (Proposition 29.2), continuum many nonconjugate copies (Theorem 29.4), parameter-fixed copies (Theorems 29.6, 29.7), conjugation-compatible surcomplex embeddings (Theorem 30.3, Proposition 30.4, Corollary 30.5). Files prefixed `11-coefficient-gaps-`. |
| **12** | *Automatic Strongness and Proper Embeddings of the Omnific Integers: constant-term duality, full stabilizers, and the surreal–surcomplex boundary* (batch 30, item 04) | `a6c68ac` | Base of the automatic-strongness sections of Part III: scalar detection (Theorem 21.4), the constant-term isomorphism theorem with the weaker hypothesis (Theorem 22.1), automatic strongness of `Aut(Oz)` (Theorem 23.2), the factorization at set size and the Archimedean corollary (Theorem 24.1, Corollary 24.3), adjoints and the general retraction (Theorems 25.2, 25.3, Corollary 25.4), the proper-class functional (Theorem 25.6), the image corollary (Corollary 27.4), regular cardinals (Proposition 31.1). Files prefixed `12-automatic-strongness-`. |
| **13** | *Automatic Hahn Linearity of Omnific Isomorphisms: residue duality, full stabilizers, and coefficient-drifting self-embeddings* (batch 30, item 05) | `0865f04` | The same main theorems as 12, printed once. Its own additions: the countable binary witness and finite-row lemma (Lemma 21.3, second route in Theorem 21.4, Corollary 21.5), isomorphisms between different, possibly non-divisible groups (Proposition 23.1, Corollary 23.4), the coefficient-matrix formula (Proposition 22.3), constant-term preservation without `Oz`-preservation (Example 23.6), the small-integer-part example (Example 31.2), the failure of pair homogeneity (Corollary 27.5). Files prefixed `13-omnific-isomorphisms-`. |
| **14** | *Automatic Summability from Omnific Arithmetic: constant-term duality, the full omnific stabilizer, and a sharp set–class distinction* (batch 31, item 07; 24 pages) | `3d40856` | A third derivation of 12's and 13's main theorems, in less generality, printed once with them (14 added to their sources in Part III). Its own material is Part IV (Sections 33–37): the induced-matching route to detection (Lemma 34.1, third route in Theorem 21.4, Corollary 34.2), the cancellation example (Example 34.3), detection in subfields with the countable detector property (Definition 35.1, Proposition 35.2), formal power-series evaluation (Theorem 36.1), the general adjoint matrix (Proposition 36.2), the case `Γ = R` (Remark 36.3), and Question 37.1. Files prefixed `14-automatic-summability-`. |

`fb5c4b5` is 12 commits before the placement `f4c9504` and `befe739` is 10
commits before it. Both pins contain the batch-24 placement `be06fc8`. Neither
contains the reconstruction section that batch 25 added to the omnific
Diophantine report. The source manuscripts are not shipped: no delivered
`.tex`, PDF or README is here. Their code, recorded data, build records, and the
source audits of 02 and 04 are shipped. The hashes in
`data/02-parameter-rigidity-build_audit.json` refer to 02's delivered files
(`article.tex`, `article.pdf`, `README.md` and others under their delivered
names). Most of those files are not shipped. The theorem numbers in
`04-preserving-automorphisms-source_audit.md` are those of manuscript 04: its
Theorem 4.3 is Theorem 3.3 here, and its Theorem 8.1 is Theorem 7.4.

Source 10 pins `58cd8e1`, a commit on a line that does not contain
`f4c9504`, so its author never saw this report. Its code, recorded run, build
record and source audit are shipped under the prefix `10-support-cut-`; its
delivered `article.tex`, `article.pdf` and `README.md` are not. The SHA-256
hashes in `data/10-support-cut-build_audit.json` cover seven delivered files:
the four shipped ones match their prefixed copies here byte for byte, and the
other three refer to the unshipped manuscript files. The section numbers in
`10-support-cut-source_audit.md` are manuscript 10's: its Section 9.4
(coefficient rigidity) corresponds to the closing paragraph of Section 9.2 here.
That audit's statement that no inspected guide states the support-cut
criterion was true at its pin and is stale now (see below).

Sources 11, 12 and 13 pin `cf56b89`, `a6c68ac` and `0865f04`, three commits of
the line that forked at `c6359e4`. None contains `b3fa9e2`, the batch-28 write of
source 10, so their authors saw this report without Section 3.3, Remark 3.9 and
the partial information after Question 11.1. Their code, recorded runs, build
records and source audits are shipped under the prefixes `11-coefficient-gaps-`,
`12-automatic-strongness-` and `13-omnific-isomorphisms-`; their delivered `.tex`,
PDF and README files are not. Delivered files are kept byte-identical, so the
following wrong or unshipped references in them are disclosed here instead of
edited:

- `11-coefficient-gaps-SOURCE_AUDIT.md` (Section 2), and the bibliography of the
  unshipped manuscript 11, call `a6c68ac3826ac337762b71a2ef901997d019260c` "a tree
  SHA, not a commit SHA". **This is false**: it is a commit (source 12's pin), with
  tree `12bfef3`. 11's own pin `cf56b89`, its tree `21d04b0` and its four blob
  hashes are correct.
- `13-omnific-isomorphisms-SOURCE_AUDIT.md` gives `71c1710` as the blob of the
  top-level `README.md` at its pin `0865f04`. That blob is the file at the earlier
  commit `b895e86`; at `0865f04` it is `8c636c7`. Its `docs/README.md` blob
  `ee31a8f` is correct.
- `data/12-automatic-strongness-BUILD_AUDIT.json` records SHA-256 hashes and sizes
  of seven delivered files. All seven were verified at placement. Three of them
  (`article.tex`, `article.pdf`, `README.md`) are not shipped; the other four are
  shipped here under their prefixed names.
- The Makefiles of 11 and 12 and 13's `build.sh` name the delivered files
  (`surreal_embeddings.tex`, `article.tex`, `verify.py`, `verify_finite_models.py`,
  `verification.json`, `code/verify.py`), which are not present here under those
  names; they do not build this report or run as-is.
- The theorem numbers in the three audits and build records are those of the
  manuscripts: 12's Theorem 5.5 is Theorem 23.2 here, 13's Theorem 6.1 is also
  Theorem 23.2, and 11's Theorem 4.2 is Theorem 26.3.

Source 14 pins `3d40856`, which contains this report's `article.tex` exactly as
written in batch 26 (`9b80a30`) and the placement `c6359e4` of source 10's files,
but not `b3fa9e2` (source 10's write) nor `21375f8` and `20c4c9f` (the placement
and write of 11–13). So its author saw Question 11.1 open and none of Part III.
Its checks, recorded run and source statement are shipped under the prefix
`14-automatic-summability-`; its `article.tex`, PDF, README and `SHA256SUMS.txt`
are not (the checksum list was verified at placement and dropped). Disclosures
about its delivered files, which are kept byte-identical:

- `code/14-automatic-summability-verify.py` was delivered as `checks/verify.py`.
  It always writes `data/verification.json` under the parent of its own directory
  (`Path(__file__).resolve().parents[1]`) and has no option to change that. Run in
  place it would create an unprefixed `data/verification.json` in this report
  (not overwriting `data/14-automatic-summability-verification.json`); run from a
  flat copy directory it writes into that directory's parent. The rerun
  instructions below account for this.
- Its delivered README (not shipped) says the program writes
  `data/verification.json`; that is the delivered layout.
- `14-automatic-summability-SOURCES.md` describes the batch-26 text of this report
  (accurate at the pin) and states a novelty claim that is stale at the merge
  (see "Stale statements corrected").

**Why one report.** 04, 08 and 09 prove one classification at three
generalities, with the same consequences:

- rank triviality;
- fixed field `R`;
- set-parameter nondefinability of monomials;
- a non-nilpotent stabilizer.

The shared results are printed once. 09 is the base because its hypotheses on
`(k, 𝔬)` are the weakest and its group-theoretic results the widest. 04's
proof is used for the criterion because it imports no correspondence. 08's
single-flow threshold is kept as a marked case because it needs no
divisibility. 02 has a different subject: algebraic families of embeddings,
not automorphisms. It is the shift-zero complement of Part I and forms Part
II. None of the four contradicts another or any report in the collection.

10, added in batch 28, is a fifth independent derivation of the Part I
classification. Its hypotheses are exactly those of Theorem 3.3:
characteristic-zero `k`, any unital `𝔬`, divisible `Γ`. Its condition "every
shift `h` in `ε_g`, `g > 0`, has `nh < g` for all `n`" is Theorem 3.3's
condition (v) read on the principal unit instead of its logarithm, so it is
**the same theorem**, not a strengthening. It is printed once, as further
equivalent conditions (vii)–(ix) in Theorem 3.8. Its genuinely new material is
appended at the ends of the sections it belongs to. 10 contradicts neither
this report nor any other.

11, 12 and 13, added in batch 30, form **Part III**. 12 and 13 answer this
report's Question 11.1 and extend Theorem 5.1 and Corollary 5.2 to every
automorphism; 11 classifies the strong exact-monomial embeddings, of which the
embeddings of 12 and 13 are instances. 12 and 13 prove the same main theorems
and are printed once with 12 as the base; 11 is the base of the embedding
sections. Section 20.1 records where the merge chose. None of the three
contradicts this report or another: automorphisms preserving `Oz` fix `R`,
embeddings need not.

14, added in batch 31, is a **third independent derivation** of automatic
strongness for the real pair (after 12 and 13), in less generality: it treats
isomorphisms of one divisible group, where Proposition 23.1 allows different,
possibly non-divisible groups, and its constant-term theorem assumes `σ(k) = l`, as
13's does. Its proof chain `ℛ_Γ → Π → 𝒜_Γ → R → 𝔪 → ct → summation` is the one
printed after Theorem 23.2. So its shared results are printed once in Part III
with 14 added to their sources, and only its genuinely new material forms **Part
IV** (Sections 33–37; Section 33.2 has the full correspondence table). 14
contradicts neither this report nor any other.

**Printed once.**

- **The criterion** (04, 09; 08 for single flows): Theorem 3.3 with Theorem
  3.4, Corollary 3.5 and Theorem 4.10. 04's logarithmic-character coefficients
  `a_{σ,δ}` and 09's operator coefficients `c_δ` are **different functionals**.
  Example 3.2 has `a_{σ,ω+1}(ω²) = 1/2` while `c_{ω+1}(ω²) = 0`. Each
  vanishing condition is equivalent to preserving the integer part, so the
  two conditions are equivalent.
- **Rank dichotomy** (Theorem 4.13).
- **Fixed field `R`** (Theorem 7.2).
- **Set-parameter nondefinability** (Theorem 9.1).
- **One group**: 04's `⟨A_s, B_u⟩` and 08's `⟨A_1, B_1⟩` are the same group at
  `s = u = −1` (Theorems 6.8, 6.10).
- **Strong factorization** (Theorem 5.1).
- **Source 10's duplicates**, printed once with 10 added to their sources:
  - its criterion and logarithmic corollary (Theorems 3.3, 3.8);
  - its rank theorem (Theorem 4.13);
  - its stabilizer splitting (Theorem 5.1);
  - the fixed field for `F = exp ξ` (Theorem 4.2);
  - its parameter theorem (Theorem 9.1) and the monomial and omega-map parts
    of its nondefinability theorem (Theorem 9.1, Corollary 9.2);
  - its Gaussian theorem (Theorem 10.1);
  - its one-shift lemma (Lemma 2.1);
  - its floor, fraction-field and coefficient-rigidity statements (Corollary
    5.2 and `odg:`, not reprinted).

  Its three-scale nonabelian example is kept as Example 6.13 beside Theorems
  6.8 and 6.10, which give more.
- **Sources 12 and 13, the same paper twice** at the level of main theorems
  (batch 30): scalar detection (Theorem 21.4), the constant-term isomorphism
  theorem (Theorem 22.1), automatic strongness of `Aut(Oz)` (Theorem 23.2), the
  set pairs (Proposition 23.1, Corollary 23.4), monomial determination
  (Corollary 23.5), the factorization of every automorphism (Theorem 24.1),
  adjoints and retractions (Proposition 25.1, Theorems 25.2, 25.3), monomial
  adjoints (Example 25.5), the class functional (Theorem 25.6), and the
  surcomplex automorphism theorems (Theorems 30.1, 30.2). 12 is the base: its
  isomorphism theorem assumes only a coefficient isomorphism `α` and derives
  `F|_k = α`, where 13 assumes `σ(k) = ℓ`.
- **Sources 11, 12 and 13, one embedding**: 11's, 12's and 13's embeddings moving
  a real `b` to `b + ω^{−1}` are one construction with three order isomorphisms
  `No → No_{>0}` or `No → (1, ∞)` (Theorem 27.3), all instances of 11's
  classification (Theorem 26.3). `J(No) ∩ R = ker d` (12 and 11) is Corollary
  27.4 and Proposition 29.2; nonelementarity (12 and 11) is Theorem 29.1.
- **Source 14, printed once** (batch 31; its numbering; Section 33.2): Theorem 1.1,
  Theorem 5.3 and Corollary 5.5 as Theorem 23.2 and Corollary 23.4; Lemma 2.2 as
  Lemma 2.1 and Lemma 21.1; Theorem 3.3 and Corollary 3.4 as Theorem 21.4;
  Theorem 4.1 and Corollary 4.2 as Theorem 22.1 and Corollary 22.2; Propositions
  5.1–5.2 as the cited reconstruction and Proposition 23.1; Lemma 5.4 as
  `odg:thm:fractions` (and its `Γ = Z` warning as Example 31.2); Corollary 5.6 as
  Corollary 23.5; Theorems 6.1–6.2 and Corollary 6.3 as Proposition 25.1 and
  Theorem 25.2; Theorem 7.1 as Theorem 25.6; Theorem 8.1 as Theorem 24.1;
  Theorem 8.2 as Theorem 3.3 (04's polynomial route); Corollary 8.3 as Corollary
  24.3; Proposition 9.1 as the inverse of Example 4.19 (letters swapped);
  Proposition 10.1 and Theorems 10.2–10.3 as Theorems 30.2 and 30.1; Example 10.4
  as the phase twists of `odg:def:lem:twist`.
- **Reproved and cited, not reprinted**: the reconstruction of `R`, `Π`, the
  multiplier ring and `Frac Oz = No` (all three; `odg:`), the convex-support
  criterion (12 by the least forbidden shift, which is 10's route; 13 by the
  polynomial in `q`, which is 04's route; Theorem 3.3 and Theorem 3.8), and the
  Taylor automorphism (11; `saut:thm:coeffflow`).

**Cited, not reprinted.** 04, 08 and 09 each reprove parts of the omnific
Diophantine report (`odg:`), which gained this material after their pins:

- units and constant products;
- Pell rigidity;
- `Frac Oz = No`;
- the multiplier ring and the reconstruction of `R`, order and standard part;
- automorphisms of `Oz` fix `R`;
- the split restriction to `Aut C`;
- the definitions of `Z`, `Π` and `C`.

08's formula for `Π` is `odg:cor:definablect` in structure, and that
corollary was in the tree at 08's pin. Both 08's and 09's formulas are
dominated by the one-witness `∃y x² = 2y²` of `odg:def:thm:ideal`. Only the
extras are printed:

- the order formula on `Oz`;
- the projections `P_−, P_0, P_+` on all of `No`;
- the floor map;
- truncation at a named monomial;
- the set-sized version;
- the Gaussian fixed field `Q`;
- the wild lift.

**Kept as second routes.**

- 04's proved exponential–logarithm correspondence on common positive shifts
  (Theorem 4.8), beside the imported one.
- 04's separation lemma, beside the explicit functional in Theorem 7.2.
- 10's least-forbidden-shift proof of necessity (Theorem 3.8, second route),
  beside 04's polynomial argument. 04 shows that a coefficient is a polynomial
  in `q` with infinitely many zeros. 10 needs one rational `q`: at the least
  forbidden shift no nonlinear binomial term contributes.
- 10's direct proof of the inner-support bound (Corollary 9.11).
- 13's binary finite-row proof of scalar detection (Lemma 21.3 and the second
  route in Theorem 21.4), beside 12's triangular detector. 12 makes the family
  triangular and then chooses coefficients; 13 keeps the family and chooses
  them row by row.
- 14's induced-matching proof (Lemma 34.1 and the **third route** in Section 34),
  beside those two. It passes to a diagonal submatrix, so the witness has all
  coefficients `1` and nothing is chosen.

**Added by the merge**, each tagged `[merge]` with a complete proof:

- the combined Theorem 3.3 (09's generality, 04's proof, and 09's first step,
  which removes 04's use of `⋂ n𝔬 = 0`);
- Example 3.2;
- Remark 6.11 (`⟨A_s, B_u⟩ ≅ Z ≀ Z` for all real `s, u ≠ 0`);
- Question 11.6;
- with 10: the converse in Theorem 4.18 (a twist preserves `ℛ_𝔬` only if its
  profile vanishes on `C_δ`) and the outer bound `f ∈ R((t^{V_A}))` in
  Corollary 9.11;
- with 11–13: Corollary 24.4 (what an automorphism of `Oz` does inside `Π`),
  the bottom gap `C_ω` of 12's exponent embedding (Lemma 27.2), the extension of
  12's image corollary to all three embeddings (Corollary 27.4), and the second
  sentence of Question 32.13 (general `(k, 𝔬)`);
- with 14 (batch 31): Example 35.3 (the Puiseux field, where detection fails),
  Remark 35.4 (support-bounded fields for every uncountable `κ`, and partial
  information on Question 32.12), Proposition 36.5 (an extension of a ring
  automorphism of `ℛ_Γ` to `K_Γ` is unique), the weakened coefficient hypothesis
  after Proposition 35.2, and the status notes after Questions 32.12 and 32.14.

**Notation.**

- Part I uses the small-`t` convention `t^γ = ω^{−γ}` of 04 and 09, so the
  purely infinite ideal `Π` sits at **negative** `t`-exponents. 08's
  `ω`-convention statements are translated: its `D_{φ,δ}` is `D_{δ,−φ}`.
- Part II keeps 02's large-monomial convention `X^g = ω^g`, which is that of
  the other omnific reports.
- `Π` replaces `𝒥` (08, 09) and `𝓘` (04).
- `𝒜_k = k ⊕ Π` replaces 09's `B`, 04's `𝒜` and 08's `𝓑_k`.
- `ℛ_𝔬 = 𝔬 ⊕ Π` replaces `A_D`, `O_D`, `A_k` and `R_Γ(D, k)`. The coefficient
  ring `D` is renamed `𝔬` because `D` names derivations.
- `C_δ` replaces 08's `H_δ`; in Part II 02's `H(a)` is `C(a)`, the
  transcendence report's notation. The quotient report's `H_a` means the
  opposite.
- `q_β` is the exponent-coefficient functional, for 09's `q_η`, 08's `c_a`
  and 02's `χ_b`.
- 09's parameter monomial `H = ω^η` is `η = ω^β`.
- 10 writes `X^g = ω^g = t^{−g}`; its statements are translated. Two traps:
  - 10's `H_h` (principal convex subgroup) is `C_δ` here, and 10's `C_g`
    (elements infinitesimal relative to `g`) is `H_g` here. **The letters are
    swapped.**
  - 10's `pr_+` (the purely infinite part) is `P_−` here, and its `pr_−` is
    `P_+`. **The subscripts are reversed.**
- 10's `𝓘`, `R_D`, `B`, `𝒰_D` are `Π`, `ℛ_𝔬`, `𝒜_k`, `U`. Its shift `h` is `δ`
  and its `λ_b` is `q_b`. Its profile `P` and variable `T` are `Θ` and `ξ`. Its
  twist `σ_{λ,F,h}` is `σ^F_{h,−λ}`, and its structure `𝒩†` is `𝔖†`.

- Part III (11, 12, 13) uses the same `t`-convention; Section 20.3 has its
  table. Traps:
  - 11's `C_τ`, the **bottom gap** (the largest convex subgroup of the target
    group meeting `τ(Γ)` only in `0`), is `𝖦_τ` here. It is **not** a principal
    convex subgroup `C_δ`, although for the explicit maps it happens to be `C_1`
    or `C_ω`.
  - 12's `θ` is an exponent embedding, written `ι_{μ_12}`, not an additive
    profile. 13 uses `τ` twice; its second `τ` is `ι_{μ_13}`. 11's and 13's
    order isomorphisms are both `p` (here `μ_11`, `μ_13`), and 11's `ρ`
    (coefficient section) and 13's `ρ = σ|_k` (here `α`) differ.
  - 13 writes `σ = U ∘ M`; here, as in Theorem 5.1, `σ = M ∘ u`, with `U = M u M^{−1}`.
  - The embeddings `Φ` (11), `J_D` (12) and `F_D` (13) are `J_{μ,d}`; the
    large-cardinal report's `J` is written `ĵ`.
  - Strongly additive is one-directional and does not include `R`-linearity; a
    strong automorphism has a strongly additive inverse.

- Part IV (14) uses the same `t`-convention; Section 33.3 has its table. Traps:
  - 14's `A_Γ = Z ⊕ Π` is `ℛ_Γ` here; `𝒜_Γ = R ⊕ Π` here is 14's `B`. **14's `A`
    is not `𝒜`.**
  - 14's coefficient isomorphism `τ` is `α`; 14's exponent automorphism `φ` is
    `τ` here, and `M_{χ,φ}` is `M_{χ,τ}`. 14's ring automorphism `ρ` of `Oz` is
    `σ` (Part III's `ρ` is a coefficient section).
  - 14's normalized factor `ν`, its `𝒰` and `L_ν(g)`, `a_{ν,δ}` are `u`,
    `U_{ℛ_Z}(Γ)` and `h_u(g)`, `a_{u,δ}`; its `T*` is `T†`; its `Λ` is `λ_On`.
  - 14's `F` is a power series (written `𝖥`) in one theorem and a subfield
    (written `K'`) in the next; neither is Part III's isomorphism `F`.
  - In 14's shear `e_1` is the **larger** scale; in Example 4.16 it is the
    smaller, so the letters are swapped. Its `s = t^{e_2}` is written `t^{e_1}`.
  - 14's truncation `P_{<γ}` is `T_{<γ}`, not a zero-cut projection; its additive
    `h` is `θ`, not a logarithmic character; its infinitesimals `u_j` are `z_j`;
    its `d > 0` is `δ` (`d` is a derivation of `R` in Part III); its target
    monomial `u` is `t`.
  - 14's `≪` is the same relation as `≪` here.

Section 1.5, Section 20.3, Section 33.3 and Appendix A.4 list every renaming.

## What the report claims

Part I (`K = k((t^Γ))`, `k` of characteristic zero, `Γ ≠ 0` divisible, `𝔬 ⊆ k`
unital):

- **Theorem 3.3** (convex-support criterion). A strong `k`-linear
  1-automorphism `σ` preserves `ℛ_𝔬` if and only if
  `a_{σ,δ}(C_δ) = 0` for every `δ > 0`, if and only if `σ` commutes with
  `P_−, P_0, P_+`. Four further equivalent conditions are listed, and
  Theorem 3.8 (from 10) adds three more. The stabilizer does not depend on
  `𝔬`. The proof is elementwise, imports no
  exponential–logarithm correspondence, and holds for `Γ = No`, that is for
  `Oz` and `Oz[i]`.
- **Theorem 3.4 and Corollary 3.5.** A contracting strong derivation preserves
  `𝒜_k` if and only if `c_δ(C_δ) = 0`. `U = Exp(𝔏_A)` holds for set-sized
  `Γ`. For `No` it holds granted the proper-class correspondence (see below)
  or on the common-shift class (Theorem 4.8).
- **Theorems 4.1, 4.2 and 4.8.** Homogeneous shears
  `t^γ ↦ t^γ exp(θ(γ) t^δ)` with `θ(C_δ) = 0`, their exact first
  displacement and fixed field `k((t^{ker θ}))`, and the proved correspondence
  on common positive shifts.
- **Theorem 4.10** (08). For any ordered abelian group, divisible or not, a
  single flow `exp(s D_{δ,θ})` preserves `ℛ_Z` if and only if
  `θ(C_δ) = 0`. `θ(δ) ≠ 0` is allowed.
- **Theorem 4.13.** The stabilizer is trivial if and only if `Γ` is
  Archimedean.
- **Theorem 4.15.** Its fixed field is `k((t^{B(Γ)}))`, where `B(Γ)` is the
  bottom convex subgroup. **Theorem 4.17**: phase shears.
- **Theorem 5.1 and Corollary 5.2.** The strong `Oz`-stabilizer is
  `{M_{χ,τ}} ⋉ U_Oz`. Every field automorphism preserving `Oz`, strong or
  not, fixes `R` and commutes with the projections and the floor. Since
  batch 30 the corollary adds that every such automorphism is strong
  (Theorem 23.2), so `{M_{χ,τ}} ⋉ U_Oz` is the whole stabilizer (Theorem 24.1).
- **Theorems 6.3 and 6.6.** In finite ordered rank `r` the derived length is
  at most `r − 1`. It equals `r − 1` for `Q^r`, for the Lie algebra and for
  the abstract group.
- **Theorems 6.8 and 6.10.** Exact commutators. `⟨A_{−1}, B_{−1}⟩ ≅ Z ≀ Z`
  faithfully, with leading terms `(−1)^n ω^{ω²−ω−n}`.
- **Corollary 6.12.** Every set stabilizer contains `Z ≀ Z`.
- **Theorem 7.2.** `Fix U_Oz = R`, also for all field automorphisms of `No`
  preserving `Oz`. The common fixed subring of all ring automorphisms of
  `Oz` is `Z`.
- **Theorem 7.4 and Corollary 7.5.** Elementary shears fixing a set `A` have
  fixed field `k((t^{V_A}))`. For monomial parameters this is the fixed field
  of the full stabilizer.
- **Theorems 7.6 and 7.7.** Faithful `R^κ` actions fixing any set of
  parameters, and nonsolvable set stabilizers.
- **Lemma 8.1 and Theorem 8.2.** `z ≥ 0 ⇔ ∃a,b (b ≠ 0 ∧ a² = z b²)` on `Oz`.
  `P_−, P_0, P_+` on all of `No`, the floor map, and truncation at a named
  monomial are definable in `(No, Oz)`.
- **Theorem 9.1, Corollary 9.2 and Theorem 9.4.** For every set of parameters,
  neither the monomial class nor the omega-map is definable, not even in the
  pure ring `Oz` for the monomials in `Oz`. No valuation-representative rule is
  definable.
- **Remark 9.5.** The one-term class and the `RV` sort.
- **Theorems 10.1 and 10.2, Proposition 10.3, Corollary 10.4.** Gaussian
  results:
  - conjugation-compatible witnesses;
  - an imaginary-time shear that fixes any set and moves the real axis inside
    the leading-term kernel;
  - a wild coefficient lift that moves an ordinary real;
  - the common fixed field of all `Oz[i]`-preserving automorphisms is `Q`.

Added to Part I from source 10:

- **Lemma 3.7 and Theorem 3.8** (support-cut form). The inclusion
  `σ(ℛ_𝔬) ⊆ ℛ_𝔬` already suffices. With `ε_σ(γ) = t^{−γ}σ(t^γ) − 1`, the
  conditions of Theorem 3.3 are equivalent to `supp ε_σ(γ) ⊆ H_γ` for every
  `γ < 0`, and to the same for every `γ ≠ 0`. There are two proofs: one via
  Theorem 3.3, and 10's least-forbidden-shift proof.
- **Remark 3.9.** The necessity half needs no strongness. Every `k`-fixing
  1-automorphism with `σ(ℛ_𝔬) ⊆ ℛ_𝔬` satisfies the condition on monomials.
  This was partial information on Question 11.1; for `(No, Oz)` the remark is
  now subsumed by Theorem 23.2, which answers that question.
- **Proposition 3.10.** Every element of the stabilizer maps each monomial
  into the signed Archimedean block of its exponent. It commutes with the
  projection onto any union of blocks and preserves `k((t^Δ))` for every
  convex `Δ`. Individual truncations are not preserved.
- **Theorem 4.18.** Twists `t^γ ↦ t^γ exp(Θ(γ)(t^δ))` for additive
  `Θ: Γ → ξk[[ξ]]` with `Θ(δ) = 0` are strong 1-automorphisms with
  `σ_{δ,Θ}σ_{δ,Ψ} = σ_{δ,Θ+Ψ}`. They preserve `ℛ_𝔬` if and only if
  `Θ(C_δ) = 0` (the "only if" is the merge's).
  `Hom_Q(Γ/C_δ, ξk[[ξ]])` embeds in the stabilizer.
- **Binomial twists** `t^γ ↦ t^γ F(t^δ)^{θ(γ)}` (equation 4.4). **Example
  4.19** is a two-scale example.
- **Theorem 4.20, Corollary 4.21 and Proposition 4.22.** For a general profile
  `F`, the fixed field is `k((t^{ker θ}))`, with an exact first displacement.
  `Fix σ^n = Fix σ`, there are no nontrivial finite orbits, and the fixed field
  is relatively algebraically closed. Independent exponent cosets give
  algebraically independent monomials.
- **Remark 4.23.** 10's rank witness `t^{γ_0} ↦ t^{γ_0} + t^{γ_0+δ}`. Its
  `Γ = Z` example is for `𝔬 = k` and agrees with Remark 4.11.
- **Example 6.13.** Noncommuting binomial twists at the scales `ω`, `ω^ω`,
  `ω^{ω²}`.
- **Proposition 7.8.** Set-sized definable-closure bound:
  `dcl(A) ⊆ ⋂_δ k((t^{span_Q(S_A) + C_δ}))` in `K` with `ℛ_𝔬`, all constants,
  the projections and, when `k` is ordered, the order.
- **Remark 9.7 and Theorem 9.8.** For every set of parameters there is `β`
  such that `ω^{ω^β} ↦ ω^{ω^β} + ω^{ω^β−δ}` for every `0 < δ < 1`. This is a
  two-term omnific integer. The images form a proper class. **Corollary
  9.9**: every bounded birthday stage is fixed by a nonidentity
  `Oz`-preserving automorphism.
- **Theorem 9.10.** With any set of parameters, in `(No, +, ·, <, Oz)` with
  every real and `P_−, P_0, P_+` named, the simplicity relation and the graph
  of the Gonshor exponential are not definable. The monomial and omega-map
  clauses are Theorem 9.1.
- **Corollary 9.11.** Definable elements lie in `R((t^{V_A}))` (the merge's
  outer bound, from Theorem 7.4). In particular they create no new positive
  inner support position (10).
- **Proposition 10.5.** Two-term Gaussian witnesses that preserve the real
  axis, its order, conjugation and the projections. On the real axis the
  omega-map, simplicity and exponential are not definable in that expansion.

Part II (source 02):

- **Theorem 13.1 and Corollary 13.3.** `ℛ_𝔬(k, Γ)` has every nonzero element
  dividing a positive monomial if and only if `Γ` has no order unit. This is
  `bst:thm:fieldcriterion` restricted to positive support. `Oz` and `Oz[i]`
  are root-covered.
- **Theorems 14.4 and 14.5.** Embeddings of a set-sized root-covered domain
  into a finite-type domain land in a finite field of algebraic constants.
  There is a pointed version.
- **Theorems 15.1, 15.3, 15.4 and 15.5.** Polynomial and Laurent coefficient
  rigidity. Strong cancellation: every isomorphism `Oz[X_1..X_n] ≅ B[Y_1..Y_n]`
  carries `Oz` onto `B`. Automorphisms of `R[T]` and `R[U^±]`.
- **Theorem 16.2 and Corollary 16.3.** `ML(Oz[T_1..T_n]) = Oz`. There are no
  finite-rank additive or torus coactions and no gradings.
- **Theorems 17.2, 17.3 and 17.5.** Formal flows of all orders that no
  polynomial family realizes, even to first order. The monomial orbit field
  has transcendence degree `dim_Q χ(Γ)` and is never finitely generated.
- **Theorem 17.6.** The commuting derivations `D_b` are `osq:prop:classder`.
  They are independent over `Oz`. **Corollary 17.9**: a continuum of
  independent orbit elements.
- **Proposition 18.1.** The bounded-scale fraction field of a set-sized
  workspace, as in `bst:prop:localdensity`.

Part III (sources 11, 12 and 13; Sections 20–32). `K_Γ = k((t^Γ))`,
`ℛ_Γ = Z ⊕ Π_Γ`, and `⟨x, y⟩_0 = ct(xy)`.

- **Theorem 21.4** (scalar detection; 12, 13). A set-indexed family in a full
  Hahn field, the group a set or `No`, is Hahn-summable if and only if for every
  `y` only finitely many `ct(x_j y)` are nonzero. Tests `y` with countable support
  and coefficients in `{0, 1}` suffice. Lemmas 21.2 and 21.3 give the two
  cancellation-proof detectors; Corollary 21.5 gives countable certificates.
- **Theorem 22.1** (12, 13). A field isomorphism `F` of full Hahn fields with
  `ct(Fx) = α(ct x)` for a coefficient isomorphism `α` satisfies `F|_k = α` and
  is strong in both directions. **Proposition 22.3** (13): the coefficient matrix
  of `F` is the inverse transpose of that of `F^{−1}`.
- **Theorem 23.2** (12, 13). Every ring automorphism of `Oz` extends uniquely to
  an automorphism of `No` that fixes `R` and is strongly `R`-linear with strongly
  `R`-linear inverse: `Aut(Oz) ≅ Aut(No; Oz) = Aut^str_R(No; Oz)`. **Proposition
  23.1 and Corollary 23.4**: the same for ordered isomorphisms between full real
  Hahn pairs with nonzero groups, possibly different and non-divisible ("ordered"
  may be dropped when both are divisible). **Corollary 23.5**: an automorphism of
  `Oz` is determined by its values on monomials. **Example 23.6** (13): a strong
  automorphism preserving `ct` but not `Oz`.
- **Theorem 24.1 and Corollary 24.3.** Every automorphism of `(No, Oz)`, and of
  a full real Hahn pair with nonzero divisible set-sized group, is uniquely
  `M_{χ,τ} ∘ u` with `u` as in Theorem 3.3; for Archimedean groups every one is
  a monomial map. **Corollary 24.4** (merge) answers the second clause of
  `osq:q:invisible`.
- **Section 25** (set-sized groups; 12, 13). Strong `k`-linear functionals are
  `ct(a ·)` (Proposition 25.1); a `k`-linear map is strong if and only if it has a
  constant-term adjoint (Theorem 25.2); every strong `k`-linear field embedding has
  a canonical strong linear retraction, not multiplicative when proper (Theorem
  25.3, Corollary 25.4). **Theorem 25.6**: `λ_On(x) = Σ_{α∈On} [t^{−α}]x` is a
  strong functional on `No` with no representing surreal.
- **Theorem 26.3** (bottom-gap classification; 11). For divisible `Γ, Δ` and an
  ordered embedding `τ: Γ → Δ`, strong field embeddings with `t^γ ↦ t^{τ(γ)}` and
  `ℛ_Γ → ℛ_Δ` correspond to ordered field embeddings `ρ: R → R((t^{𝖦_τ}))`, where
  `𝖦_τ` is the largest convex subgroup meeting `τ(Γ)` only in `0`. They preserve
  valuation, leading coefficient and `ct`, and reflect `ℛ` and `Π`. The gap
  condition is necessary even without strongness. **Theorem 26.6 and Corollary
  26.7**: a Taylor section is admissible exactly when its shift is in the gap, and
  reals can move exactly when `τ(Γ)^{>0}` is not coinitial.
- **Theorem 27.3** (11, 12, 13). For a transcendental real `b`, a derivation `d` of
  `R` with `d(b) = 1` and any of three order isomorphisms, the map
  `Σ r_γ t^γ ↦ Σ_γ Σ_n d^n(r_γ)/n! t^{ι_μ(γ)+n}` is a proper strong embedding of
  `No` with `ct` preserved, `J^{−1}(Oz) = Oz` and `b ↦ b + ω^{−1}`; `ω ↦ ω^ω`
  (11, 13) or `ω^{ω²}` (12). **Corollary 27.4**: `J(No) ∩ R = ker d`, and `t`
  annihilates the image for the pairing. **Corollary 27.5** (13): `(No, Oz)` is not
  strongly homogeneous for set-sized induced substructures.
- **Section 28** (11). Classified images are closed, proper ones nowhere dense
  (Theorem 28.1). Any field embedding of `No` is continuous if its value image is
  cofinal and nowhere continuous with uniformly discrete image otherwise (Theorem
  28.3). All four cofinal/coinitial combinations occur (Theorem 28.4).
- **Section 29** (11). Coefficient-moving embeddings are not elementary for
  `(No, Oz)`, nor on `Oz` as rings (Theorem 29.1); `F ∩ R` is the real closed fixed
  field of `ρ` (Proposition 29.2); continuum many images, field-conjugate but
  pairwise nonconjugate under `R`-fixing automorphisms (Theorem 29.4); proper
  copies fixing any set of parameters, discrete or not (Theorem 29.6), and moving a
  real transcendental over the parameters' coefficients (Theorem 29.7).
- **Section 30.** Conjugation-compatible automorphisms of `(No(i), Oz[i])` are
  `σ(x) ± iσ(y)` with `σ ∈ Aut(Oz)`, hence strong (Theorem 30.1; 12, 13);
  valuation-compatible ones are strong and `α`-semilinear (Theorem 30.2; 12, 13);
  conjugation-compatible exact-monomial embeddings are classified (Theorem 30.3;
  11).
- **Proposition 31.1** (12). The detection and isomorphism theorems for
  `<κ`-support fields, `κ` regular uncountable. **Example 31.2** (13):
  `Frac(Z ⊕ uR[u]) = R(u) ≠ R((t))`.

Part IV (source 14; Sections 33–37). Everything 14 shares with Part III is
credited there; Part IV adds:

- **Lemma 34.1 and the third route in Theorem 21.4.** A matrix over a field with
  nonzero finite rows (indexed by `N`) and finite columns has an infinite induced
  matching. Applied to a descending sequence in the union of the supports, it
  gives the detector `y = Σ_r t^{−g_{n_r}}`, all coefficients `1`, with
  `⟨x_{j_r}, y⟩_0` a single nonzero matrix entry; no coefficient is chosen, in
  every characteristic, for `Γ` a set or `No`. **Corollary 34.2**: monomial tests
  and all-ones series on strictly increasing sequences suffice. **Example
  34.3**: `±t^{−nδ}` cancel in pairs but are not summable, and the all-ones test
  gives `±1`. **Remark 34.4**: `(t^{n/(n+1)})` is summable but does not tend to 0.
- **Definition 35.1 and Proposition 35.2.** A subfield `K'` containing `k`, every
  monomial and every all-ones series on a strictly increasing sequence detects
  ambient summability by tests in `K'`, and a coefficient- and
  `ct`-compatible automorphism of `K'` preserves ambient summability and carries a
  sum lying in `K'` to the sum. **Example 35.3** (merge): in the Puiseux field
  `t^{−n/(n+1)}` passes every test but is not summable. **Remark 35.4** (merge):
  every `K_{<κ}`, `κ` uncountable, has the property.
- **Theorem 36.1.** Every automorphism of a full real Hahn pair (divisible `Γ`, or
  `(No, Oz)`) commutes with the evaluation of formal power series at
  infinitesimals, in particular with the local `exp` and `log(1 + ·)`; with `α` on
  the coefficients in the valuation-compatible Gaussian case.
- **Proposition 36.2.** At set size the constant-term adjoint of a strong
  `k`-linear map is the sign-reversed transpose `(T†)_{γ,η} = T_{−η,−γ}`.
- **Remark 36.3.** For `Γ = R` the stabilizer consists of
  `t^γ ↦ e^{θ(γ)} t^{λγ}` with `λ > 0` and `θ` additive, possibly discontinuous.
- **Remark 36.4.** 14's shear moves `t^{−e_2}` to `Σ(−1)^n t^{−e_2+ne_1}` and does
  not commute with truncation at the monomial `t^{−e_2+e_1/2}`; the definable
  truncation of Theorem 8.2 is carried to truncation at a non-monomial.
- **Proposition 36.5** (merge). For nonzero divisible set-sized `Γ`, a ring
  automorphism of `ℛ_Γ` has at most one extension to `K_Γ`, and any extension is
  strong and fixes `R`.
- **Remark 36.6.** 14's real-structure hypothesis `σ(No) = No` is equivalent to
  commuting with conjugation; its phase example is a phase twist already in the
  collection.

## What the report does not claim

Appendix B lists every source's non-claims: 13 from 09, 13 from 04, 12 from
08, 11 from 02, 18 from 10, 13 from 11, 14 from 12, 12 from 13 and 16 from 14.
In brief:

- Sources 04, 09 and 10 state that nonstrong automorphisms are not classified
  and that strongness is not shown. These non-claims are kept as their records.
  **Status:** for `(No, Oz)` and the full real Hahn pairs with divisible group,
  Part III now proves that every automorphism is strong (Theorem 23.2,
  Corollary 23.4), so Theorem 24.1 classifies them all. For `Oz[i]` without
  conjugation or valuation data, and for general `(k, 𝔬)`, strongness is still
  not shown.
- No construction for arbitrary logarithmic characters; Part III retains this
  admissibility qualification (Remark 24.2).
- No generation or density theorem.
- The relative fixed field is computed for elementary shears only, and for
  monomial parameters. The Hahn hull is not definable closure.
- The shears are not exponential and do not respect the omega-map.
- Nothing is claimed after naming a proper class of parameters. Bare
  nondefinability of coefficient-one monomials already follows from character
  twists.
- No set or class of all class automorphisms is formed.
- Part II:
  - its theorems need injectivity and domain targets;
  - root-covered is sufficient, not necessary;
  - the formal flows are not convergent and not internal exponentials;
  - no classification of `Aut(Oz)` or of all derivations;
  - no Jacobian or general cancellation claim.
- Source 10:
  - its rank theorem concerns the leading-term-fixing factor only;
  - only Archimedean blocks are preserved, not every truncation;
  - the fixed fields are relatively, not absolutely, algebraically closed;
  - the definable-closure statements are upper bounds, not descriptions or
    quantifier elimination;
  - the bounded-birthday automorphism does not preserve birthdays globally;
  - the nonabelian example gives no presentation;
  - `Frac Oz = No` and coefficient rigidity are prior results;
  - the omega-map question of Kaplan–Krapp–Serra, factorization and the
    holonomic order-unit question are not addressed.
- Sources 11, 12 and 13 (Part III):
  - the classification of embeddings needs the exact-monomial hypothesis; it
    does not classify all surreal embeddings, does not assert that
    omnific-preserving embeddings are strong, and excludes characters and unit
    corrections;
  - the proper embeddings are not a counterexample to strongness of embeddings,
    and are not claimed initial, exponential or omega-compatible; the real
    derivations are choice-dependent and not computable;
  - support duality, finiteness spaces, `Frac Oz = No`, the reconstruction, the
    convex criterion, Taylor automorphisms and exponent lifts are prior work;
  - the adjoint theory is for set-sized groups only and fails for `No`; the
    retraction is linear, not a field retraction or a positive conditional
    expectation;
  - the Gaussian results need conjugation or valuation compatibility and must
    not be merged into an unconditional classification; no nonconjugacy is
    claimed for automorphisms preserving `Oz[i]` but not conjugation;
  - the support-bound result is for regular uncountable `κ`; no singular case and
    no birthday cutoff;
  - the set-pair results assume an ambient isomorphism: automorphisms of a small
    integer part are not claimed to extend when its fraction field is smaller;
  - the continuum of conjugacy types is a lower bound; the annulus bounds are
    external; topological claims are local; pure-field elementarity is classical
    and coefficient fixing is not shown sufficient for pair elementarity;
  - summation detection is not valuation-topological convergence and not
    first-order definability; invariance is not definability;
  - no exponential, logarithm, omega-map, birthday or simplicity structure is
    preserved or used; omnific automorphisms are not trivial, and not every
    automorphism of `No` is strong.
- Source 14 (Part IV):
  - the unrestricted Gaussian problem is not solved, in either direction; its
    phase example is strong and disproves nothing;
  - no embedding theorem (the isomorphism proof uses surjectivity essentially);
  - no compatibility with the global Gonshor exponential (formal evaluation is at
    infinitesimals only), and no commutation with arbitrary truncations, which is
    false; continuity and the monomial cross-section are neither assumed nor
    concluded;
  - the strong dual and adjoint theory hold at set size only and fail for `No`;
  - it does not assert that ring automorphisms of a set-sized `ℛ_Γ` extend to
    `K_Γ`;
  - the convex criterion classifies existing automorphisms and constructs none;
  - summation, the monomials and a cross-section are not claimed first-order
    definable;
  - class-group notation is elementwise (NBG with global choice, set-indexed
    families, set supports);
  - the countable detector property is sufficient only, and is not claimed for
    transseries, Puiseux or left-finite subfields;
  - the adjoint is algebraic, not a Hilbert-space adjoint;
  - finiteness-space duality (Blute–Cockett–Jacqmin–Scott) and the Hahn
    automorphism decompositions (Kuhlmann–Serra, Kaplan–Krapp–Serra) are prior
    work; no priority is claimed, and global priority is not certified;
  - its finite checks are not proofs; no Lean; its proposed Lean modules are
    plans only; Conway's irreducibility conjectures are not addressed.
- No named conjecture is solved. The report is not refereed, has no Lean
  formalization and makes no priority claim. The finite checks test identities
  only.

**The imported correspondence.** The correspondence between contracting strong
derivations and strong 1-automorphisms is Cited theorem 1.1 (BKKPS Theorem
3.13). BKKPS proves it for set-sized `Γ`. The placement dossier doubted 09's
citation of Kaplan–Krapp–Serra Fact 4.2 for the surreal case. The merge re-read
the arXiv v3 PDF: Fact 4.2 does state the bijection, and says that it "also
holds for G a proper class", without a separate proof (Remark 1.2). So these
statements depend on that assertion for `Γ = No`, and say so:

- `U_Oz = Exp(𝔏_A)` (Corollary 3.5);
- the group upper bounds (Theorem 6.3);
- the "exactly `r − 1`" in Theorem 7.7.

Theorem 3.3, the explicit constructions on `No` and nonsolvability do not
depend on it.

## Open questions, re-scoped

- **Questions 11.1–11.7.**
  - 11.1: strongness of `Oz`-automorphisms (04, 09 and 10). **Answered** in
    batch 30 by sources 12 and 13 (Theorem 23.2): every ring automorphism of
    `Oz` extends uniquely to a strongly `R`-linear automorphism of `No` with
    strong inverse. So all of them extend to strong automorphisms, preservation
    of `Oz` forces strongness, and there is no nonstrong example; 09's clause
    (characterize the nonstrong automorphisms commuting with normal-form sums)
    is vacuous, and 10's variant ("is every one strong?") has the answer yes.
    10's partial information (Remark 3.9) is subsumed. The analogue for `Oz[i]`
    is answered under conjugation or valuation compatibility and open otherwise
    (Question 32.1). Source 14 (batch 31) answers it again independently.
  - 11.2: admissible logarithmic characters (04). Still open; 12, 13 and 14 ask
    it again. Automatic strongness settles recognition of existing automorphisms,
    not their construction.
  - 11.3: full relative fixed fields (04). 10's definable-closure question is
    recorded with it.
  - 11.4: generation and exhaustion (04 Q4 with 08 Q1 and 10's generation
    question).
  - 11.5: normal-form data weaker than the omega-map (08). 10 adds that the
    reals, projections and floor do not help, and that simplicity and the
    exponential are not definable either.
  - 11.6: the criterion for non-divisible `Γ` (merge). It stays **open**: 10
    assumes divisibility, and its `Γ = Z` example is for `𝔬 = k`.
  - 11.7: other integer parts (10), new. 12's question on intrinsic scalar
    tests for other rings is related (Question 32.13).
- **Questions 32.1–32.18** (Part III): the thirty questions of 11, 12 and 13
  (ten each), merged where they coincide, with 12's and 13's admissibility
  question recorded under 11.2.
  - 32.1: the unrestricted Gaussian stabilizer (12, 13, 14). Still open; 14
    proposes `C((t^Q))`, then a rank-two lexicographic group, as first targets.
  - 32.2: must an embedding `f` of `No` with `f^{−1}(Oz) = Oz` be strong, also
    when `ct ∘ f = ct`, and what survives without strongness (12, 13, 14; 11)?
    **Negative answer under a measurable cardinal**: the large-cardinal report
    ([`large-cardinal-embeddings-and-normal-forms`](../../foundations-and-computation/large-cardinal-embeddings-and-normal-forms/))
    shows that applying an elementary embedding `j` with critical point to sign
    sequences gives an ordered field embedding of `No` that fixes `R`, preserves
    and reflects `Oz`, preserves `ct` and is not strongly additive. It is not
    onto, so it does not conflict with Theorem 23.2. Without large cardinals the
    question stays open, as do 11's clauses on dense images and images neither
    closed nor discrete.
  - 32.3: target tests for coefficient-fixing embeddings (13, 14).
  - 32.4: which subfields of `R` occur as `f(No) ∩ R` (12). **Partly answered**
    by 11 (Proposition 29.2): in the exact-monomial strong class they are the
    real closed fixed fields of the sections, and Taylor sections give `ker d`.
  - 32.5–32.7: removing exact monomial preservation, elementarity of
    coefficient-fixing pair embeddings, coefficient sections (11).
  - 32.8: conjugacy of proper copies (11, 13); **partly answered** by
    Theorem 29.4. The independent-copies report asks its pair version at a
    fixed Hahn core (batch 31 note).
  - 32.9: homogeneity of the pair (12, 13).
  - 32.10: surcomplex embeddings without a real form (11).
  - 32.11: the proper-class strong dual (12, 14).
  - 32.12: singular support bounds (12, 13). **Partial information** (batch 31,
    Remark 35.4): the image family is Hahn summable with the right sum; only the
    size of the union of its supports remains open.
  - 32.13: other rings and coefficient fields (12, 14, with the merge's clause on
    general `(k, 𝔬)`).
  - 32.14: isomorphisms of small integer parts (13, 14). 14 asks the automorphism
    case with uniqueness; **uniqueness is answered** by Proposition 36.5 (merge),
    existence stays open.
  - 32.15: exponential, omega-map and differential structure (11, 12, 13).
  - 32.16–32.18: restricted workspaces and compositions (11); formalization
    (11, 12, 13, 14). For 32.17, image inclusion and intersection inside one
    independent family with `ρ = id` are settled by `isc:thm:boolean` (batch 31
    status note); composition and the general case stay open.
- **Question 37.1** (Part IV, 14), new: can the countable detector property be
  weakened to a necessary and sufficient closure condition for product
  detection, and which computable or transseries subfields satisfy it? Example
  35.3 shows that some closure is needed. 14's other seven questions are merged
  into 32.1, 32.2–32.3, 32.11, 32.13 (with 11.7), 11.2 (with 11.4), 32.14 and
  32.18 (Section 37.1).
- **08's Question 2** asked whether `C` is first-order reconstructible from
  the pure ring `Oz[i]`. It is **answered** by `odg:def:cor:internal`, and
  independently by 09's Pell-divisibility route, so it is dropped.
- **02's questions** are 19.1–19.3. Question 19.2, on formal directions, is
  **partly answered** by Part I: positive-shift derivations preserving `Oz`
  are classified, and those with a common shift set integrate to automorphisms
  inside `No`. The shift-zero and other cases stay open.

Questions of other reports (Section 11.1). These are recorded here; the
other reports were not edited by these merges (the quotient report received a
reciprocal status note in batch 31).

- **`osq:q:invisible`**, second clause ("How much can an automorphism of `Oz`
  do inside `Π` while fixing `ct`?"): **answered** in batch 30 (Corollary 24.4).
  Every automorphism is strong (Theorem 23.2) and is `M_{χ,τ} ∘ u` with `u`
  classified by Theorem 3.3. The first clause stays open. Since batch 31 the
  quotient report records the question as partly answered, citing Corollary
  24.4.
- **`odg:def:q:realform`**: **negative information** only (Theorem 10.2,
  Proposition 10.3). It is not answered.
- **The surcomplex report's "effective descriptions inside the leading-term
  kernel"** (`saut:sec:questions`): **not answered**. Its `Oz`-stabilizing part
  is described. No exhaustion theorem is proved.
- **`dsn:q:languages`** of the definable-surreals report: **further
  information**, not an answer (from 10). Simplicity and the Gonshor
  exponential are not definable in `(No, +, ·, <, Oz)` with any set of
  parameters, even with all reals and the projections named (Theorem 9.10).
  Order plus simplicity already defines `ω` (`dsn:prop:simplicity-omega`).
- **The Diophantine report's caution** after `odg:def:thm:autreal` (its argument
  "does not apply unchanged to endomorphisms") is **sharpened**, not contradicted:
  Theorem 27.3 gives proper ring embeddings `Oz → Oz` whose fraction-field
  extensions move a real (Theorem 29.1 explains why the universal multiplier
  definition of `R` is not preserved).

## Stale statements corrected

Appendix A.3 records these.

- **09's divisibility remark** was right for `𝒜_k` and wrong for the integer
  part: the translation sends `t^{−1}/2 ∈ Z + t^{−1}R[t^{−1}]` outside it
  (Remark 4.11).
- **The reconstruction and definability sections of 04, 08 and 09** were
  written before the Diophantine report's reconstruction section was placed.
  They are cited. 04's remark that its reconstruction is not first order is
  superseded.
- **Credits added:**
  - `saut:thm:shiftflow`, which 08 and 09 did not credit;
  - `saut:thm:decomp`;
  - the rigidity report's `thm:no` and `cor:question54`, where 09 cited only
    KKS Proposition 5.2;
  - for 02: `bst:thm:fieldcriterion`, `bst:prop:localdensity`,
    `osq:prop:classder` and `odg:thm:fractions`.
- **The surcomplex report's `T_1(t) = t/(1−t)`** does not preserve `Oz`
  (Example 4.12).
- **10's novelty statement.** 10 said that no inspected report guide states
  the support-cut criterion. It proposed the criterion, the rank boundary, the
  fixed fields and the parameter witnesses as new. That was true at its pin
  `58cd8e1`. At the merge those results are Theorems 3.3, 4.13, 4.2 and 9.1,
  so 10 is credited as an independent fifth source. Only the material listed
  above is printed as its contribution (Section 11.1, Appendix A.3). 10's
  other repository statements (`Frac Oz = No`, the multiplier and coefficient
  results, the Gaussian phase twists) are accurate. No mathematical error was
  found in 10.
- **A false reason, corrected (batch 30).** After Corollary 10.4 the report
  said that a real automorphism "preserves order and cannot move an ordinary
  real". Read literally that is false: `saut:thm:coeffflow` is a strong
  order-preserving automorphism of `No` with `b ↦ b + t^δ`. The correct reason is
  that an automorphism preserving `Oz` fixes `R`, which is definable in the pair.
  The sentence is corrected in place. No result depended on it: this is a
  correction, not a retraction.
- **Status notes (batch 30).** Question 11.1 is answered, so Remark 3.6 (what has
  been classified), Remark 3.9, the paragraph after Theorem 5.1, Corollary 5.2,
  the `osq:q:invisible` item of Section 11.1 and the paragraph after Question 11.1
  carry status notes. No label, number or earlier sentence was removed.
- **Credits added (batch 30):** `saut:thm:coeffflow` for the Taylor motion used by
  12 and 13, which do not credit it; 11 does.
- **14's novelty statement (batch 31).** 14's abstract says the strong-additivity
  hypothesis "can be removed" from this report's real stabilizer classification,
  its introduction that it "supplies a missing implication", and its questions
  section that it "closes the automatic-strongness question for the real omnific
  pair". That was accurate at its pin `3d40856`, where Question 11.1 was open. It
  is stale at the merge: 12 and 13 answered Question 11.1 in `20c4c9f`. 14 is
  credited as an independent third derivation (Section 37.2, Appendix A.3), and
  only the material listed above is printed as its contribution. No mathematical
  error was found in 14. Its pinpoint citations of Kuhlmann–Serra (an example of a
  non-strongly additive automorphism) and of Blute–Cockett–Jacqmin–Scott (Theorem
  3, Lemmas 4.1–4.2) were not rechecked.
- **Checked true (batch 30):** 12's statement that this report's Theorem 5.1 is
  the strong factorization and that Corollary 5.2 needs no strongness, and that
  10's audit disclaims nonstrong classification; 13's statements on Theorems 3.3
  and 5.1 and on the Diophantine reconstruction; 11's statements on the
  surcomplex Taylor motions and exponent lifts, the Diophantine ideal test,
  multiplier and fraction field, and this report's automorphism rigidity. Their
  claims that no report proves automatic strongness, scalar detection or
  coefficient-moving embeddings are still true. The two wrong statements in their
  delivered audits are listed above ("Eight sources, one report").
- **Checked true:**
  - "the catalogue lists 51 reports", at the pins;
  - the antecedents in `saut` and `odg` that the sources name;
  - no report contained an `Oz`-automorphism classification.

## Relation to the neighbouring reports

- [`omnific-diophantine-geometry`](../omnific-diophantine-geometry/) (`odg:`).
  - Its reconstruction section (`odg:def:`) is the source of everything that
    this report cites about what `Oz` remembers.
  - This report adds the automorphisms and the nondefinability, and records
    negative information for `odg:def:q:realform`.
- [`set-sized-quotients-of-omnific-integers`](../set-sized-quotients-of-omnific-integers/)
  (`osq:`).
  - Its `osq:q:invisible` is partly answered: the second clause by Corollary 24.4
    (from 12 and 13, and again from 14's factorization and automatic
    strongness), the first clause not. Since batch 31 the quotient report
    records this in its status of the question.
  - Its `osq:prop:classder` derivations are Part II's `D_b`.
  - Its `osq:thm:derivations` (derivations into set-sized modules vanish) is
    consistent with them.
- [`surcomplex-field-automorphisms`](../../surcomplex/surcomplex-field-automorphisms/)
  (`saut:`).
  - Fixed-shift flows, the four-layer decomposition and the phase twists come
    from this report.
  - This report describes the `Oz`-stabilizing part of its kernel `U`.
  - Its Taylor motion `saut:thm:coeffflow` is the ambient automorphism in every
    embedding of Part III; composed with a proper exponent embedding it preserves
    and reflects `Oz` (Theorem 26.6), although alone it never preserves `Oz`.
- [`exponential-automorphism-rigidity`](../exponential-automorphism-rigidity/).
  Every exponential 1-automorphism of `No` is the identity, so the shears are
  not exponential.
- [`single-dilation-hahn-support`](../../surcomplex/single-dilation-hahn-support/)
  (`dsup:`). The dilation `S_2` defines the monomials, and `(No, Oz)` does
  not.
- [`transcendence-over-bounded-support`](../transcendence-over-bounded-support/)
  (`bst:`). Its field criterion underlies Theorem 13.1.
- [`omnific-groups-and-lattices`](../omnific-groups-and-lattices/). It is a
  sibling report written concurrently from the same batch.
- [`definable-surreals-and-omnific-integers`](../../foundations-and-computation/definable-surreals-and-omnific-integers/)
  (`dsn:`). It uses `opa:thm:fixed` and `opa:thm:parameters`. Theorem 9.10
  adds information on its `dsn:q:languages`.
- [`holonomic-rigidity-for-entire-hahn-functions`](../../surcomplex/holonomic-rigidity-for-entire-hahn-functions/).
  Its order-unit boundary is a different condition from the Archimedean rank
  of Theorem 4.13. 10 does not address its question.
- [`three-duals-of-hahn-vector-spaces`](../../surcomplex/three-duals-of-hahn-vector-spaces/)
  (`duals:`). It studies `K`-linear maps on vector-valued Hahn spaces; the
  adjoints of Section 25 are `k`-linear scalar maps for the pairing `ct(xy)`, a
  different convention. No exhaustive non-overlap is claimed.
- [`independent-surreal-copies`](../independent-surreal-copies/) (`isc:`;
  batch 31). Its monomial lifts are the maps `J_{h,id}` of Theorem 26.3.
  `isc:cor:parameters` extends the fixing clause of Theorem 29.6 to an
  `On`-indexed family whose pairwise intersection is exactly the full Hahn
  field `R((t^H))` on the rational span `H` of the supports of `A`, jointly
  linearly disjoint over it (note after Theorem 29.6; for its explicit `H = 0`
  copies Theorem 28.3(ii) gives closed, uniformly discrete images, a `[merge]`
  observation). `isc:thm:boolean` settles image inclusion and intersection
  inside one independent family with `ρ = id` (status note after Question
  32.17); its second research question is the pair version of Question 32.8
  (note after that question). Both questions stay open in general.
- [`large-cardinal-embeddings-and-normal-forms`](../../foundations-and-computation/large-cardinal-embeddings-and-normal-forms/)
  (batch 30, written concurrently; cited by directory only). Under a measurable
  cardinal its sign-sequence embedding answers Question 32.2 negatively; it is not
  an automorphism, so Theorem 23.2 stands. Under the same hypothesis it shows that
  14's embedding question (merged into 32.2–32.3) needs hypotheses beyond
  constant-term compatibility and preservation and reflection of `Oz`.

## What was run

For the merges all nine suites were rerun on copies, with Python 3.14.4 and
SymPy 1.14.0 (10's for the batch-28 addition, 11's, 12's and 13's for the
batch-30 addition, 14's for the batch-31 addition). Each reproduced its
recorded result:

| Suite | Result |
|---|---|
| 09 | twelve PASS lines and `ALL CHECKS PASSED` |
| 04 | 7,062 assertions in 17 groups, `all_checks_passed` |
| 08 | 9,469 checks in 15 categories, `PASS`; the rewritten file is identical to the shipped record up to line endings |
| 02 | 7,041 assertions in 13 families, `PASS`; identical up to line endings |
| 10 | 28,668 assertions in 19 categories, `passed`; category counts identical to the shipped record, which differs only in the `python` and `generated_utc` fields |
| 11 | 3,880 assertions in 15 categories, `passed`; the report written with `--output` is identical to the shipped record up to line endings |
| 12 | 17,774 assertions (10,800 detector, 4,502 adjoint, 2,472 Taylor-block), `PASS`; identical up to line endings |
| 13 | 13,885 assertions in 16 categories, all passed; identical up to line endings |
| 14 | four groups, all `passed`: binomial identities to degree 20 for 31 rational parameters (961 multiplication and 31 inverse cases), an induced matching of size 64 on a 256-row banded prefix, 100 adjoint trials with 13 source and 9 target exponents (seed 20260923), cancellation prefixes for 1, 2, 5, 16 and 64 pairs; the written file and the printed report are identical to the shipped record up to line endings |

The placement dossiers ran further independent checks, which are not shipped:

- 281 for 04, 08 and 09, including Example 3.2, the commutator formula for
  symbolic `s, u` and the failure example of Remark 4.11;
- for 02, the quotient-rule identity of Example 17.8, to 29 terms;
- 8,724 assertions for 11, 12 and 13 (SymPy): the Taylor-block embedding in a
  lexicographic `Z²` model, the failure of the ambient Taylor automorphism, 13's
  binary finite-row algorithm over `F_2` and `Q`, 12's triangular detector, the
  least-forbidden-shift coefficient and Example 23.6.

## Build and reproduce

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build uses standard packages only and gives no errors, warnings,
overfull or underfull boxes, or undefined references. Build in a scratch
directory; the auxiliary files are not kept here.

Seven of the shipped scripts can write files, so rerun the checks on a copy, outside
this directory, and pass `--output` where it is shown:

```
D=$(mktemp -d) && cp code/*.py "$D" && cd "$D"
python 09-omnific-preserving-verify_finite_identities.py            # prints only
python 04-preserving-automorphisms-verification.py --output rerun-04.json   # needs sympy==1.14.0
python 08-integer-part-symmetries-verify.py                         # writes verification.json here
python 02-parameter-rigidity-verify.py --output rerun-02.json
python 10-support-cut-verify.py --output rerun-10.json              # standard library
python 11-coefficient-gaps-verify_finite_models.py --output rerun-11.json
python 12-automatic-strongness-verify.py --output rerun-12.json
python 13-omnific-isomorphisms-verify.py --output rerun-13.json    # --output is required, see below
```

Source 14's script has no output option and writes `../data/verification.json`
relative to its own directory, so give it a subdirectory of its own inside a
fresh scratch directory (do not run it from the flat copy above, where it would
write into the parent of `$D`):

```
E=$(mktemp -d) && mkdir "$E/code" && cp code/14-automatic-summability-verify.py "$E/code/"
python "$E/code/14-automatic-summability-verify.py"   # prints; writes $E/data/verification.json
```

The scripts write as follows:

- Without `--output`, 04's script writes `verification_report.json` into the
  current directory.
- 08's script always writes `verification.json` next to itself.
- 02's and 10's scripts do the same unless `--output` is given. Run in place,
  10's script would create `code/verification.json`; it does not touch
  `data/10-support-cut-verification.json`.
- 11's script prints its report and writes a file only with `--output`.
- 12's script writes `verification.json` next to itself unless `--output` is
  given; run in place it would create `code/verification.json`.
- 13's script writes `../data/verification.json`, relative to its own
  directory, unless `--output` is given. Run in place, or from a copy directory
  inside this report, it would create an unprefixed `data/verification.json`
  here (not overwriting `data/13-omnific-isomorphisms-verification.json`), so
  always pass `--output`.
- 14's script prints its report and always writes `../data/verification.json`
  relative to its own directory; it has no `--output`. Run in place it would
  create an unprefixed `data/verification.json` here (not overwriting
  `data/14-automatic-summability-verification.json`). On Windows the written file
  has CRLF line endings; it matches the shipped record up to line endings.

The five Makefiles and the build scripts `04-preserving-automorphisms-build.sh`
and `13-omnific-isomorphisms-build.sh` are shipped as delivered. They name the
manuscripts' own files (`omnific_automorphisms.tex`, `surreal_embeddings.tex`,
`article.tex`, `verify.py`, `verify_finite_identities.py`,
`verify_finite_models.py`, `code/verify.py`), which are not present here under
those names, so they do not run as-is. The `clean` targets of
`10-support-cut-Makefile` and `12-automatic-strongness-Makefile` delete
auxiliary files named `article.*` in the working directory; do not use them
here. 13's `build.sh` expects its delivered layout (`code/verify.py` and
`article.tex` beside the script) and stops at its first step here; in its
delivered layout it runs the checks with the default output path above.
