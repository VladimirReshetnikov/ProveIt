# Omnific-Preserving Automorphisms

**Convex-scale stabilizers, definable constants, nondefinable monomials, and algebraic-parameter rigidity;
formal orbit fields, left-orderable symmetry groups, integration of all derivations, and exact difference equations**
Merged research report from fifteen manuscripts written independently and dated
23 September 2026: items 02, 04, 08 and 09 of batch 26, placed in `f4c9504`
(they keep those numbers here); item 05 of batch 28, placed in `c6359e4`
as an addition and numbered 10 here; items 03, 04 and 05 of batch 30,
placed in `21375f8` as an addition and numbered 11, 12 and 13 here; item
07 of batch 31, placed in `9d28e28` as an addition and numbered 14 here;
items 03 and 08 of batch 32, placed in `7d04483` as additions and numbered 15
and 16 here; manuscripts 03, 05 and 08 of batch 33, placed in `aa9c891` as
additions and numbered 17, 18 and 19 here; and manuscript 01 of batch 34, placed in
`a7a435f` as an addition and numbered 20 here. Prepared for Vladimir Reshetnikov.

```
article.tex                                 the report, standalone LaTeX with an internal bibliography
article.pdf                                 the compiled report, 221 pages
README.md                                   this guide
02-parameter-rigidity-source_audit.md       source 02's source and novelty audit, as delivered
04-preserving-automorphisms-source_audit.md source 04's source and claim audit, as delivered
10-support-cut-source_audit.md              source 10's source, proof and novelty audit, as delivered
11-coefficient-gaps-SOURCE_AUDIT.md         source 11's source and novelty audit, as delivered
12-automatic-strongness-SOURCE_AUDIT.md     source 12's source, proof and novelty audit, as delivered
13-omnific-isomorphisms-SOURCE_AUDIT.md     source 13's source, novelty and verification audit, as delivered
14-automatic-summability-SOURCES.md         source 14's repository snapshot, literature and novelty statement, as delivered
15-topological-collapse-SOURCE_AUDIT.md     source 15's source, proof and novelty audit, as delivered
16-coefficient-recovery-SOURCE_AUDIT.md     source 16's source, dependency and novelty audit, as delivered
17-formal-orbit-fields-PROOF_AUDIT.md       source 17's author-side proof audit, as delivered
17-formal-orbit-fields-SOURCE_AUDIT.md      source 17's source and novelty audit, as delivered
18-exact-symmetries-PROOF_AUDIT.md          source 18's author-side proof audit, as delivered
18-exact-symmetries-SOURCE_AUDIT.md         source 18's source and novelty audit, as delivered
19-formal-symmetry-SOURCE_AUDIT.md          source 19's source, proof and novelty audit, as delivered
20-universal-symmetries-SOURCE_AND_PROOF_AUDIT.md   source 20's source and proof audit, as delivered
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
  15-topological-collapse-verify.py                   source 15 checks (standard library; writes
                                                      verification.json beside itself by default)
  15-topological-collapse-Makefile                    source 15's all/check/clean targets (delivered
                                                      file names; they do not build this report)
  16-coefficient-recovery-verify.py                   source 16 checks (standard library; writes
                                                      verification.json beside itself by default)
  16-coefficient-recovery-build.py                    source 16's build script (delivered layout; it
                                                      does not build this report, see below)
  17-formal-orbit-fields-verify.py                    source 17 checks (SymPy; writes --output, by
                                                      default verification.json in the working directory)
  17-formal-orbit-fields-Makefile                     source 17's all/pdf/check/clean targets (delivered
                                                      file names; do not run it here, see below)
  18-exact-symmetries-verify.py                       source 18 checks (standard library; writes
                                                      verification.json beside itself by default)
  18-exact-symmetries-build.sh                        source 18's build script (delivered layout; it
                                                      does not build this report)
  18-exact-symmetries-Makefile                        source 18's all/verify/clean targets (delivered
                                                      file names; they do not build this report)
  19-formal-symmetry-verify.py                        source 19 checks (standard library; writes
                                                      ../data/verification.json by default)
  19-formal-symmetry-build.sh                         source 19's build script (delivered layout; it
                                                      fails here, see below)
  20-universal-symmetries-verify.py                   source 20 checks (standard library; writes
                                                      verification.json beside itself by default)
  20-universal-symmetries-Makefile                    source 20's all/pdf/checks/clean targets (delivered
                                                      file names; do not run it here, see below)
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
  15-topological-collapse-verification.json           source 15's recorded run (27,139 assertions)
  15-topological-collapse-BUILD_AUDIT.json            source 15's build record for its own PDF (no hashes)
  16-coefficient-recovery-verification.json           source 16's recorded run (1,314 checks)
  16-coefficient-recovery-build_report.json           source 16's build record, with SHA-256 hashes
                                                      of seven delivered files
  17-formal-orbit-fields-verification.json            source 17's recorded run (30,900 assertions)
  17-formal-orbit-fields-requirements.txt             pins sympy==1.14.0
  17-formal-orbit-fields-BUILD_REPORT.json            source 17's build record, with SHA-256 hashes
                                                      of four delivered files
  18-exact-symmetries-verification.json               source 18's recorded run (11,330 assertions)
  18-exact-symmetries-BUILD_REPORT.json               source 18's build record for its own PDF (no hashes)
  19-formal-symmetry-verification.json                source 19's recorded run (1,576 checks)
  19-formal-symmetry-BUILD_REPORT.json                source 19's build record for its own PDF (no hashes)
  20-universal-symmetries-verification.json           source 20's recorded run (5,555 assertions)
  20-universal-symmetries-BUILD_REPORT.json           source 20's build record for its own PDF (sizes, no hashes)
```

Every label in `article.tex` carries the prefix `opa:` (729 labels). Source
02's part carries the sub-prefix `opa:par:` (43 labels), the material added
from source 10 carries `opa:sc:` (30 labels), Part III, from sources 11,
12 and 13, carries `opa:as:` (110 labels, besides `opa:part:as`), Part IV,
from source 14, carries `opa:cm:` (29 labels, the part label `opa:cm:part`
included), Part V, from source 15, carries `opa:tc:` (44 labels, with
`opa:tc:part`), Part VI, from source 16, carries `opa:cr:` (66 labels, with
`opa:cr:part`), Parts VII, VIII and IX, from sources 17, 18 and 19, carry `opa:of:`
(82 labels), `opa:es:` (66) and `opa:hs:` (69), each with its part label, and Part X, from
source 20, carries `opa:us:` (86 labels, with `opa:us:part`). These
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
unchanged numbers. The batch-32 addition likewise renamed and removed no label (316
kept, 110 added: 44 `opa:tc:`, 66 `opa:cr:`); its Parts V (Sections 38–42) and VI
(Sections 43–52) sit after Part IV and before the appendices, and the auxiliary-file
comparison shows all 316 earlier labels with unchanged numbers. The batch-33 addition
likewise renamed and removed no label (426 kept, 217 added: 82 `opa:of:`, 66 `opa:es:`, 69
`opa:hs:`); its Parts VII (Sections 53–59), VIII (Sections 60–66) and IX (Sections 67–75) sit
after Part VI and before the appendices, and the auxiliary-file comparison shows all 426
earlier labels with unchanged numbers. The batch-34 addition likewise renamed and removed no
label (643 kept, 86 `opa:us:` added); its Part X (Sections 76–82) sits after Part IX and before
the appendices, and the auxiliary-file comparison shows all 643 earlier labels with unchanged
numbers. The
[formalization ledger](../../FORMALIZATION.md)
lists this report's statements in its inventory, all **Pending**; its line
anchors predate the batch-28, batch-30, batch-31, batch-32, batch-33 and batch-34 additions. No implementation mapping
cites an `opa:` label. The repository now has Lean code constructing the
omnific rings themselves (`Surreal/Foundations/OmnificIntegers.lean`, for ring
clauses of the Diophantine report), but none for any statement of this report;
the earlier sentence here that there was no Lean code about omnific integers
is out of date. The Lean congruence and `p`-adic topologies on `Oz`
(`Surreal/Foundations/OmnificCongruenceTopology.lean`,
`OmnificSeparationTopology.lean`, recorded under `odg:eq:profinite` in the ledger)
are instances of Part V's pullback classification (Remark 39.6); nothing of Parts V–X
is formalized.

## Fifteen sources, one report

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
| **15** | *Algebraic Rigidity and Topological Collapse of Surreal Arithmetic: Hahn summation, omnific integer topologies, and the discrete-exponent boundary* (batch 32, item 03; archive `Surreal_Arithmetic_Topological_Collapse`; 29 pages) | none; blobs `059939b` (this report's source at `b3fa9e2`) and `60f3b17` (at `20c4c9f`) | All of Part V (Sections 38–42): Hahn-compatible ring topologies on `𝔬 ⊕ Π` for dense `Γ` are the pullbacks along `ct` of ring topologies on `𝔬` (Theorem 39.4); the omnific and field cases (Theorem 39.7, Proposition 39.8, Corollaries 39.9, 39.10); the cyclic boundary for full Hahn fields (Theorem 39.12); a disjoint-row detector with interpolation (Lemma 40.1, Corollary 40.2), the naive-detector example (Example 40.3), the Gaussian ring corollary (Corollary 40.4), the class description of the strong dual of `No` (Proposition 40.5); the pairing topology (Theorems 41.1, 41.3, Corollary 41.2); Questions 42.1–42.6. A fourth derivation of Part III's automatic strongness, printed once there. Files prefixed `15-topological-collapse-`. |
| **16** | *Recovering Surreal Coefficients from Monomial Extensions: quartic definitions, arbitrary-rank rigidity, and sharp cancellation* (batch 32, item 08; archive `surreal_coefficient_rigidity`; 24 pages) | `1ab41af` | All of Part VI (Sections 43–52): the quartic coefficient definitions (Theorems 45.3, 45.4, 45.7), the sparse power bound (Theorem 46.2), the all-order root locus (Proposition 46.5), arbitrary-monoid coefficient rigidity (Theorem 47.1, Proposition 47.2), group- and monoid-algebra automorphisms (Theorems 48.1, 48.3), the `Hom(G, Z) = 0` criterion (Theorem 49.2, using Lin–Wang), pair reconstruction (Theorem 49.5), finite-rank cancellation and its exact infinite-rank failure (Theorems 50.1, 50.3, 50.4), the boundary examples (Section 51), Questions 52.1–52.10. It generalizes Part II's Theorems 15.1, 15.3, 15.4 and 15.5. Files prefixed `16-coefficient-recovery-`. |
| **17** | *Full Formal Orbit Fields of Surreal Arithmetic: proper-class independence, exact algebraic trajectories, and the effect of changing the formal parameter* (batch 33, manuscript 03; archive `Surreal_Formal_Orbit_Fields`; 25 pages) | `efc5446` | All of Part VII (Sections 53–59): for the Euler derivation `D_0` and its constant field `𝖢_0 = ker D_0`, exact full-image descent (Theorems 53.1, 55.2, Corollary 55.3), exclusion of the additive parameter (Theorem 55.4), the ordinal family of omnific witnesses `Ξ_α` (Theorems 53.2, 56.5, Corollary 56.6), the multiplicative clock and its exact algebraic core (Theorems 53.3, 57.2, 57.3, Corollaries 57.4, 57.5), the monomial test (Proposition 58.1), the surcomplex case (Theorem 58.4), the abstract theorem (Theorem 58.6), Questions 59.1–59.10 (two merged). It answers, for `D_0`, the lower bound left after Corollary 17.9. Files prefixed `17-formal-orbit-fields-`. |
| **18** | *Relative Universality and Exact Fixed Fields of Strong Omnific Symmetries: group realization, two-level Hahn supports, and conjugation on the surcomplex field* (batch 33, manuscript 05; archive `Surreal_Exact_Symmetries_Research`; 24 pages) | `efc5446` | All of Part VIII (Sections 60–66): every nontrivial left-orderable set group acts faithfully by strongly additive, real-fixing, `Oz`-preserving double Hahn lifts with one prescribed fixed field `𝖪_S` (Theorem 60.1, Corollaries 60.2, 60.3); the orbit-support and two-level hull results (Theorem 61.5, Proposition 61.6); free equivariant cut filling (Lemma 62.3, Theorems 62.4, 62.6); the converse and the field–ring equivalence (Lemma 63.1, Corollary 63.2); the fraction gap and products (Corollaries 63.3, 63.4); examples, including the Klein bottle group (Section 64); the conjugation-compatible classification (Theorem 60.4, Section 65); Questions 66.1–66.8. Files prefixed `18-exact-symmetries-`. |
| **19** | *All Derivations Integrate: Formal Symmetry and Coefficient Definability of Omnific Arithmetic* (batch 33, manuscript 08; archive `omnific_formal_symmetry`; 25 pages) | `889b87c` | All of Part IX (Sections 67–75): every derivation of `Oz`, `Oz[i]` maps into `Π` and integrates uniquely (Theorem 67.1, Lemma 68.4, Corollary 68.5), answering Question 19.2; divisible-ideal integration and commuting families (Propositions 68.6, 68.7); the integral exponential–logarithm correspondence (Theorem 69.3, Corollary 69.5); the jet tower, lifting but nonsplit, of class exactly `N` (Theorems 70.1, 70.4); residue sections and their common core (Theorems 71.1, 71.4); the quartic formula before and after completion (Corollary 72.2, printed once with Part VI; Propositions 72.4, 72.5, Theorem 72.7, Proposition 72.8); parameterwise nondefinability of the coefficient copy (Theorem 73.2, Corollaries 73.3, 73.4); the pointed finite-type theorem for the class rings (Theorem 74.2, Corollary 74.3); Questions 75.1–75.7. Files prefixed `19-formal-symmetry-`. |
| **20** | *Universal Symmetries and Exact Difference Equations over the Surreals: left-orderable groups, omnific stabilizers, fixed fields, and surcomplex descent* (batch 34, manuscript 01; archive `Surreal_Universal_Symmetries_and_Difference_Equations`; 25 pages) | `e93a06d` | All of Part X (Sections 76–82): an independent second derivation of Part VIII's classification (Theorem 76.1, printed once there) with the orbit of `ω` algebraically independent (Proposition 77.3); a second cut filling (Proposition 77.1); the translation family (Proposition 77.4); a relative action with the proper-class fixed field `𝖪_{No∖𝖩}` and an independent interval of double exponentials (Theorem 77.5, Remark 77.6); the downward-orbit lemma and the weighted Green operator (Lemmas 78.1–78.3, Theorem 78.5); omnific primitives (Corollary 78.7); constant-coefficient operators and the operator field (Theorem 79.1, Corollaries 79.2, 79.3); the inner difference lemma (Lemma 79.4); global and relative multiplicative criteria (Theorems 79.5, 79.7); the first-order criterion (Theorem 80.1); central and free-group cocycles (Theorem 80.2, Corollary 80.3, Remark 80.4, Proposition 80.5); set-sized models (Propositions 81.1, 81.2); Questions 82.2–82.9. Its difference core re-derives the single-dilation report (`dsup:thm:resolvent`, `dsup:thm:multsingle`). Files prefixed `20-universal-symmetries-`. |

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

Source 15 names no commit. Its "pins" are two **blob** identifiers of this report's
`article.tex`, read through a connector: `059939b5…` is the file written in `b3fa9e2`
(batch 28; Question 11.1 still open) and `60f3b172…` the file written in `20c4c9f`
(batch 30, with Part III); its three audit blobs `050b52f`, `0e4e3a1`, `c4d3939` are
those placed in `21375f8`. All five were checked against the history. So it saw
Part III but not Part IV. Its checks, recorded run, build record, Makefile and
source audit are shipped under the prefix `15-topological-collapse-`; its `.tex`,
PDF and README are not. Disclosures about its delivered files, kept byte-identical:

- `code/15-topological-collapse-verify.py` was delivered as `verify.py`. It writes
  `verification.json` beside itself unless `--output` is given (run in place it would
  create `code/verification.json`, not touching the prefixed record).
- `code/15-topological-collapse-Makefile` builds `Surreal_Arithmetic_Topological_Collapse.tex`
  and runs `python3 verify.py`, delivered names not present here; it does not run as-is.
- `data/15-topological-collapse-BUILD_AUDIT.json` records 15's own 29-page US-Letter
  PDF and 27,139 assertions; it carries no hashes.
- `15-topological-collapse-SOURCE_AUDIT.md` describes an incomplete reading of this
  report (it says the updated article was not read in full), which the merge records
  in Section 38.1; its statements checked true are listed below.

Source 16 pins `1ab41af` (tree `fba47f2`, which it distinguishes correctly), which
contains Parts I–III (`20c4c9f`) but not the placement `9d28e28` or write `d4d72d7` of
source 14. It read 11's and 12's audits and some guides, not this article. Its
"prior manuscript" is source 02 itself (pin `fb5c4b5`), retrieved separately. Its
checks, recorded run, build script, build record and source audit are shipped under
the prefix `16-coefficient-recovery-`; its `article.tex`, PDF, README and
`SHA256SUMS.txt` are not (the checksum list was verified at placement and dropped).
Disclosures, files kept byte-identical:

- `code/16-coefficient-recovery-verify.py` (delivered `verify.py`) writes
  `verification.json` beside itself unless `--output` is given.
- `code/16-coefficient-recovery-build.py` (delivered `build.py`) creates `build_logs/`
  beside itself, then runs `verify.py --output verification.json` and `pdflatex
  article.tex` three times in its own directory, rewriting `article.pdf` and
  `verification.json` there. Here `verify.py` and `article.tex` are absent under those
  names, so run in place it creates `code/build_logs/` and stops with "Build failed".
  Do not run it here.
- `data/16-coefficient-recovery-build_report.json` records SHA-256 hashes of seven
  delivered files; all seven were verified. Four are shipped here under prefixed names
  (`SOURCE_AUDIT.md`, `verify.py`, `verification.json`, `build.py`); `article.tex`,
  `article.pdf` and `README.md` are not.
- Its unshipped README gives `python verify.py --output verification.json`, the
  delivered layout.

Sources 17 and 18 pin `efc5446` (tree `aba6982`, as 18 states), the eight-source text:
it contains Parts I–III (`20c4c9f`) and the placement `9d28e28` of source 14, but not
its write `d4d72d7` nor Parts V–VI. Source 19 pins `889b87c`, the nine-source text
with Part IV, but not the batch-31 notes `ab18444` nor Parts V–VI (`7d04483`,
`c315ac9`), so its quartic formula is an independent re-derivation of Part VI's. All
three read guides and searched this report through a connector, with some truncated
responses; their accounts of this report are accurate at their pins. Their checks,
recorded runs, build records, build files and audits are shipped under the prefixes
`17-formal-orbit-fields-`, `18-exact-symmetries-` and `19-formal-symmetry-`; their
`article.tex`, PDFs and READMEs are not, nor 17's and 18's `SHA256SUMS.txt` (verified at
placement and dropped). Disclosures, files kept byte-identical:

- `data/17-formal-orbit-fields-BUILD_REPORT.json` gives SHA-256 hashes of 17's
  `article.tex`, `article.pdf`, `verify.py` and `verification.json`; all four match the
  delivered files, and the last two are shipped under prefixed names. The build records
  of 18 and 19 give PDF sizes only.
- `code/17-formal-orbit-fields-verify.py` (delivered `verify.py`) writes `--output`, by
  default `verification.json` in the **working directory**.
  `code/17-formal-orbit-fields-Makefile` runs `latexmk … article.tex` and `python verify.py
  --output verification.json` in the working directory: run from this report's root it
  would rebuild this report in place (auxiliary files) and then fail on the absent
  `verify.py`. Do not run it here.
- `code/18-exact-symmetries-verify.py` writes `verification.json` beside itself unless
  `--output` is given. `code/18-exact-symmetries-build.sh` changes to its own directory
  and runs `python3 verify.py`, absent under that name, so it stops before `pdflatex`;
  `code/18-exact-symmetries-Makefile` calls `build.sh` and `verify.py` by their delivered
  names, and its `clean` target removes `article.aux`, `article.log` and similar files in
  the working directory.
- `code/19-formal-symmetry-verify.py` (delivered `code/verify.py`) writes
  `data/verification.json` under the parent of its own directory unless `--output` is
  given; run in place it would create an unprefixed `data/verification.json` here (not
  touching `data/19-formal-symmetry-verification.json`). `code/19-formal-symmetry-build.sh`
  changes to its own directory, creates `code/build/` and `code/data/`, and then fails on
  the absent `code/code/verify.py`. Its unshipped README gives `python code/verify.py
  --output data/verification.json`, the delivered layout.
- 19's audit notes that its package was compiled after midnight UTC on 24 September,
  although the manuscript is dated 23 September.

Source 20 pins `e93a06d` (tree `42aec05`), which contains Parts I–IV (with the batch-31
notes `ab18444`) and the single-dilation, autonomous-dilation and surcomplex-automorphism
reports, but not the write of Parts V–VI (`c315ac9`) nor the placement `aa9c891` of sources
17–19. So it never saw Part VIII, and its universality theorem is an independent second
derivation. It read five report guides (this report's, the independent-copies, quotient,
surcomplex-automorphism and differential-equations reports), some truncated, and not the
single-dilation report, whose resolvent and multiplicative theorems its difference core
re-derives. Its checks, recorded run, Makefile, build record and source and proof audit are
shipped under the prefix `20-universal-symmetries-`; its `article.tex`, PDF and README are
not. Disclosures, files kept byte-identical:

- `code/20-universal-symmetries-verify.py` (delivered `verify.py`) writes `verification.json`
  **beside itself** unless `--output` is given (run in place: `code/verification.json`).
- `code/20-universal-symmetries-Makefile` has targets `all`, `pdf` (`latexmk … article.tex`),
  `checks` (`python3 verify.py`) and `clean` (`latexmk -c article.tex`), all in the working
  directory: run from this report's root it would rebuild this report in place and then fail on
  the absent `verify.py`. Do not run it here.
- `data/20-universal-symmetries-BUILD_REPORT.json` records 20's 25-page PDF, 92 labels and file
  sizes (not hashes) of its `article.tex`, `article.pdf` and `verify.py`; only the last is
  shipped (as `code/20-universal-symmetries-verify.py`).
- `20-universal-symmetries-SOURCE_AND_PROOF_AUDIT.md` and the build record describe 20's
  contribution as new; that statement is stale for universality (Part VIII) and was incomplete
  at its pin for the difference core (single-dilation report); see "Stale statements corrected".
  Its unshipped README gives `python3 verify.py` and `python3 verify.py --output …`, the
  delivered layout.

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

15 and 16, added in batch 32, form **Parts V and VI**, one part each, since their
subjects differ (topology of summation; coefficient recovery at arbitrary rank).

17, 18 and 19, added in batch 33, form **Parts VII, VIII and IX**, one part each: the
full formal orbit field of one Euler flow of Part II; the set groups of
`Oz`-preserving automorphisms and their fixed fields; and formal integration of all
derivations. 17 answers, for `D_0`, the lower bound left after Corollary 17.9; 18
answers no named question; 19 answers Question 19.2. None contradicts this report or
another.

20, added in batch 34, forms **Part X**. Its universality theorem is Part VIII's, found
independently, and is printed once there; its new material is the equation theory of the
same automorphisms (additive, operator, multiplicative, first-order, cocycle) with the
independence and relative fixed-field statements that go with it. That equation theory was
already in the single-dilation report for monomial automorphisms of set-sized Hahn fields;
Part X states each correspondence (Section 76.2, Remark 78.6) and prints 20's class-sized
versions for `Oz`-preserving double lifts, which that report does not state. 20 answers no
named question and contradicts neither this report nor another.

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
- **Source 15, printed once** (batch 32; its numbering; Section 38.2): Lemma 2.2 as
  Lemmas 2.1 and 21.1; Theorem 4.2 as Theorem 21.4 (its (iii) allows all countable
  tests, not only `{0, 1}`-valued ones); Proposition 4.5 as Example 21.6; Theorem
  5.1 as Theorem 22.1; Proposition 5.3 as a direction of Theorem 25.2; Lemmas
  6.1–6.2 and Theorem 6.4 as the cited reconstruction, Proposition 23.1 and
  Corollary 23.4; Lemma 7.1 as `odg:thm:fractions`; Theorem 1.2 and Corollaries
  7.2, 7.4 as Theorem 23.2; Corollary 7.3 as Corollary 23.5; Theorem 8.1 as
  Theorem 24.1; Proposition 8.2 as Theorem 3.3 (04's route); Remark 8.3 as Remark
  24.2; Corollary 8.4 as Corollary 24.3 and Remark 36.3; Example 8.5 as Remark
  36.4; Theorems 9.2–9.3 as Theorems 30.2 and 30.1; Theorem 10.2, Corollary 10.3
  and Proposition 10.4 as Proposition 25.1 and Theorems 25.2, 25.6. 15 is added to
  their sources; it credits 12 and 13 itself.
- **Source 16, printed once** (batch 32): its Definition 6.1, Proposition 6.2 and
  Example 6.3 as Definition 12.1, Theorem 13.1, Corollary 13.3 and the workspace
  of Section 18 (16 added); its Proposition 4.1 as `odg:thm:fractions` and the
  unit lemmas; its Question 12.8 as Question 19.3. Its generalizations of
  Theorems 15.1, 15.3, 15.4 and 15.5 are printed as new results in Part VI.
- **Source 17, printed once** (batch 33; its numbering; Section 53.2): its Lemma 2.1 as
  `odg:thm:fractions`; its derivation (Proposition 2.2) as `D_0` of Theorem 17.6, with the
  constant field and `ct(D_0 x) = 0` printed in Proposition 54.1; the ring and flow statements of
  its Proposition 4.1 as Theorem 17.2; its monomial comparison (Section 4.4) as Lemma 17.4,
  Theorem 17.5 and Corollary 17.9.
- **Source 18, printed once** (batch 33; Section 60.2): its Lemma 2.1 as `odg:thm:fractions`;
  its Lemma 2.2 as Corollary 5.2 (its direct floor argument recorded after Proposition
  61.2); its lifts `T_φ`, `F_φ` as Part III's inner lift `ι_φ` and monomial map
  `M_{1,ι_φ}` (Lemma 27.1); its Lemma 8.2 as `saut:thm:axis` (its ring clause printed as
  Lemma 65.2); the infinite order in its Corollary 6.2 as in `saut:thm:torsion`; its twist
  (Proposition 9.1) as the phase twist of `saut:thm:phase`.
- **Source 19, printed once** (batch 33; Section 67.2): its Lemma 3.1 as Lemma 2.3; its
  Lemma 3.2 as `odg:thm:fractions`; the derivations `D_η` of its Lemma 6.2 as Theorem 17.6;
  its Lemma 8.1 as Theorem 45.3 for `G = Z^n`; its Theorem 8.2 and Corollary 8.3 (the formula
  `∃a ∃b (b ≠ 0 ∧ a² = (x⁴ + 1) b²)`, which is Part VI's ring formula with `a, b = u, v`) as
  Theorems 45.4 and 45.7, printed once in the joint generality of Corollary 72.2; its conic
  and characteristic-2 warnings as Remark 45.6 and Example 51.2; its Lemma 11.1 as Lemma 14.1.
- **Source 20, printed once** (batch 34; Section 76.2): its Theorem 1.1 (i)–(iii) and fixed
  fields as Corollaries 60.3, 63.2 and Proposition 65.1; its Lemma 2.3 as `odg:thm:fractions`;
  Lemma 3.2 as Lemma 63.1; Definition 3.3 as Definition 62.1; Lemmas 4.1–4.3 and Theorem 4.4 as
  Proposition 61.2, Lemma 61.4 and Theorem 61.5 (with Lemma 77.2 for the general outer lift);
  Corollary 4.5 as Theorem 60.1; Corollary 5.2 as Corollary 60.2; Proposition 12.1 as Lemma 65.2
  and `saut:thm:axis`; Theorem 12.2 as Theorem 60.4. Its difference core (Lemma 6.2, Theorems 7.1,
  8.1, 9.2, 9.4, Corollaries 8.2, 11.3) re-derives `dsup:lem:orbit`, `dsup:thm:resolvent`,
  `dsup:cor:poly`, `dsup:cor:fixed`, `dsup:thm:multsingle` and `dsup:cor:simultaneous`; it is
  printed in Part X with each correspondence, since `dsup:` states these for set-sized fields
  and, on `No`, for rational dilations only.
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
- 15's disjoint-row proof (Lemma 40.1 and the variant of the third route in
  Section 40): it selects family members with pairwise disjoint supports along the
  descending sequence, which yields an induced matching, and normalizes the pairings
  to `1`; the same selection gives prescribed pairings (Corollary 40.2). Its
  detector has countable support but not `{0, 1}` coefficients.
- 19's genus-one proof of quartic rigidity (Lemma 72.1: Riemann–Hurwitz for
  `Y² = X⁴ + 1`, then induction on the variables), beside 16's Mason–Stothers and
  specialization proof (Lemma 45.2, Theorem 45.3).
- 20's cut filling (Proposition 77.1: a whole regular copy of `G` at **every** cut), beside
  18's fibers over cut orbits (Lemma 62.3, Theorem 62.4); 20's one-operator proof of the
  commuting system (Corollary 80.3), beside the single-dilation report's Koszul contraction.

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
  after Proposition 35.2, and the status notes after Questions 32.12 and 32.14;
- with 15 and 16 (batch 32): Remark 39.6 (the congruence and `p`-adic topologies
  of the Diophantine and quotient reports, formalized in Lean, are instances of the
  pullback classification), the comparison with the foundations report's
  `found:sub:tsum` in Remark 39.13, the reading of Proposition 40.5 as an answer to
  the first clause of Question 32.11, the notes after Questions 42.2, 42.6 and
  52.9, the record that 16 does not answer `odg:def:q:coeffpe` (Section 52.2), the
  status notes after Questions 11.4, 19.3, 32.1, 32.11, 32.12, 32.18 and 37.1, and
  pointers after Theorem 15.5 and in Remark 34.4;
- with 17, 18 and 19 (batch 33): Corollary 58.7 (the descent of Theorem 58.6 holds for
  every Euler flow `D_χ` of Part II, from 17's remark after its first question);
  Corollary 72.2 in the joint generality of 16 and 19 (intermediate rings
  `A ⊆ B ⊆ K(U^G)` with `B ∩ K = A`, any rank); Remark 63.5 (18's realizations against
  Theorems 7.2, 7.4 and 7.6); the identification of 18's lifts with `ι_φ` and `M_{1,ι_φ}`
  and of its twist with the phase twist; the relations of 19's results to Theorem 4.8,
  Corollary 17.7, Lemma 7.1, Example 51.1 and Question 52.1; the merged Questions 59.6
  (internal evaluation, 17 and 19) and 59.10 (formalization, 17, 18, 19); and status notes
  after Corollary 17.9, Theorem 7.6, Questions 11.3, 19.2, 19.3, 32.15, 52.2 and 75.2, in
  Section 19, in Section 52.2 and in Appendix B;
- with 20 (batch 34): Remark 77.6 (20's proper-class relative fixed field against 18's
  `𝖪_{Σ_2(A)}`, and the new instance of Question 66.2), Remark 78.6 (the dictionary with the
  single-dilation report: chambers swapped, `Q_c`, `P_1 = ϖ`), the specialization remarks after
  Theorems 79.5, 79.7 and Corollary 80.3, the comparisons with `adr:` and `saut:thm:torsion`,
  the merged Questions 32.15, 66.3, 66.7 and 59.10, and status notes after Questions 11.3, 66.2
  and 82.2 and in Appendix B.

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

- Part V (15) uses the same `t`-convention; Section 38.3 has its table. Traps:
  - 15's topologies `𝒯, 𝒯_0, 𝒯_β` are `𝔗, 𝔗_0, 𝔗_β`; Part III's `𝒯_{d,δ}` is
    the Taylor automorphism, and `T`, `T_{<γ}`, `T^1` are maps, not topologies.
  - 15's `N` is the closure of zero, not the natural numbers; its exponent sets
    `D, E` are `𝖠, 𝖡` (not derivations, not the flow `ℰ`, not the rings `𝒜`).
  - 15's corollary "automorphisms invisible to every compatible omnific topology"
    is Corollary 39.10; it is **not** Corollary 24.4, the algebraic description of
    what an automorphism does inside `Π`.
  - 15's `No[i]` is `No(i)` here, the same field; its `ρ = σ|_k` is `α`; its
    `R_{𝔬,Γ}` is `ℛ_𝔬` with `Γ` only densely ordered.
- Part VI (16); Section 43.3 has its table. Traps:
  - **16's `X^g` is an external indeterminate**, written `U^g`; in Part II
    `X^g = t^{−g} = ω^g` is a Hahn monomial. In `No(U^G)` with `g ≠ 0`, `U^g` is
    transcendental over `No`, while `ω^g` is a coefficient.
  - 16's `K_k(G) = Frac k[G]` is `k(U^G)`, not the Hahn field `K_Γ`; its defect
    group `Δ_k(G)` is `Def_k(G)`, not Part III's target group `Δ`.
  - 16's `𝒰_∞(B)`, `D(G)`, `𝒟(B)`, `𝒞(B)` are `Rt_∞(B)`, `G_div`, `𝔇(B)`, `𝔆(B)`:
    not the stabilizer `𝒰`, not a derivation, not `C_δ`, `C(a)` or `c_δ`.
  - 16's monoids `M, N` are `𝖬, 𝖭`, not monomial maps `M_{χ,τ}`; its `τ ∈ Aut(G)`
    involves no order and its `χ` need not be positive; its coefficient
    automorphism `σ` is `α`.
  - 16's `v, d, w` (auxiliary support minimum, maximum, width) are `min supp`,
    `max supp`, `wd`, and its `ℓ` is `λ` (not Part II's leading exponent `ℓ(x)`).
- Parts VII–IX (17, 18, 19) use Part II's large-monomial convention `ω^g = X^g = t^{−g}`;
  Sections 53.3, 60.3 and 67.3 have their tables. Traps:
  - 17's `C = ker D` is the huge real closed field `𝖢_0` (it contains `ω^ω` and
    `ω^{−ω}`), **not** `C` (the complex numbers), `C_δ`, `C(a)` or `C_1`; its `D` is `D_0`
    (Part II's `D_b`, `b = 0`) and its `h = ct` is `q_0`, the constant coefficient of the
    **exponent**; `ker q_0` is not convex and is not `H_g` or the hull `ℋ(A)`.
  - 17's Taylor map `𝒯_s` is Part II's formal flow `ℰ_{0,s}`, not the Taylor automorphism
    `𝒯_{d,δ}` of Part III or a topology; its multiplicative clock `𝒰_v` is written `Υ_v`
    (not the stabilizer `𝒰`), and its `u = 1 + v` is neither Part III's factor `u` nor the
    witness `u` of Part VI; in Part VII `v` is a formal variable, not a valuation.
  - 17's full orbit field `L_add` is `L̂_0`; Part II's `L_χ` is only its monomial subfield.
    17's `A_α, B_α, a_α, E_α, X_α` are `𝔞_α, 𝔟_α, ζ_α, exp(ζ_α z), Ξ_α` (not the shears
    `A_s, B_u`, the group `ℰ_A` or Part II's monomials `X^g`).
  - 18's `ℋ(B)` (normal forms supported in `B`) is written `NF(B)`, and its `𝒦_B = ℋ(ℋ(B))`
    is `𝖪_B`: **not** Part I's relative Hahn hull `ℋ(A) = R((t^{V_A}))`, which takes a
    rational span. 18's double lift `T_φ`, `F_φ` is Part III's inner lift `ι_φ` followed
    by the monomial map `M_{1,ι_φ}`; `ι_φ` is additive, not multiplicative, and
    `ι_φ(1) = ω^{φ(0)}`.
  - 18's cut `D`, stabilizer `H` and components `C_D` are `𝖼`, `G_𝖼`, `I_𝖼`; the factor `H`
    of `H × C_2` is `G_0`; its twist `U` with character `χ` is `Φ_ph`, the phase twist
    `P_{−2π}` of `saut:thm:phase`.
  - 19's formal variable `T` is Part II's `s`; its `𝔍_R` is `Π_R` and its `J` is `Π^♯_R`; its
    Hasse–Schmidt components `H_n` are `𝖧_n`; its `ℓ_η` is `q_η`; its `E_m` is `ω^m D_0`;
    its `C_R` (common constants of **all** derivations) is `𝖢_R`, not `𝖢_0`; its `Θ` (a
    formula) is `𝖰`, not source 10's profile `Θ`.
  - **19's "coefficient section"** `R → R[[T]]` is a section of the residue map, written
    `ς` and called a *residue section*; it is **not** Part III's coefficient section
    `ρ: R → R((t^{𝖦_τ}))`. The same phrase names two different notions.

- Part X (20) uses the same growth convention; Section 76.3 has its table. Traps:
  - **20's `S_s` is the double lift of the index translation `a ↦ a + s`**, so
    `S_s(ω^γ) = ω^{ω^s γ}` and `S_1 ≠ id`; it is written `σ^tr_s` here (`σ^tr_1` is Example 64.1).
    The single-dilation and autonomous-dilation reports' `S_q`, `S_d` multiply exponents by a
    number, so there `S_1 = id`. Reading 20's `S_1` as a dilation is wrong.
  - 20's `p`, `T_p`, `σ_p` are Part VIII's `φ`, `ι_φ`, `M_{1,ι_φ}`; its `F = Fix(p)`, `H_F`,
    `F_{J,k}`, `B_A`, `y_a` are `B`, `NF(B)`, `𝖪_{No∖𝖩,k}`, `Σ_2(A)`, `w_a`; its interval `J` is `𝖩`.
  - 20's `M_k = ker c_0` is `𝖵_k` (not a monomial map `M_{χ,τ}`); its `c_0` is `ct`.
  - 20's Green operator `𝒢_c` is `Gr_c` (not the bottom gap `𝖦`, the surcomplex group `𝒢` or
    Part IX's `𝒢(R)`); its retraction `ℛ_F` is `mr_B` (not `ret_φ` or `ℛ_𝔬`); its outer and
    inner projections `P_H`, `Q_F` are `ϖ_{Γ_τ}` and `ϖ^in_B` (not `P_−, P_0, P_+`; `ϖ_{0} = ct`
    only globally).
  - 20's `f_+`, `f_−` (orbit **direction**, not sign) are `f_↑`, `f_↓`; the single-dilation
    report's valuation chambers are swapped: its `f_+` is `f_↓`.
  - 20's `P ∈ k[X, X^{−1}]` and operator field `k(X)` are `𝗉 ∈ k[𝖸, 𝖸^{−1}]` and `k(𝖸)`; its
    cocycle characters `h`, `χ` are `ch⁺`, `ch^×` (not the exponent characters of `M_{χ,τ}`);
    its conjugation `j` is `cj` and its identity `e` is `1`.

Section 1.5, Section 20.3, Sections 33.3, 38.3, 43.3, 53.3, 60.3, 67.3 and 76.3 and Appendix
A.4 list every renaming.

### Source 15 (batch 32): topological collapse

| | |
|---|---|
| Manuscript | *Algebraic Rigidity and Topological Collapse of Surreal Arithmetic: Hahn summation, omnific integer topologies, and the discrete-exponent boundary*, 23 September 2026, 29 pages; batch 32 item 03, archive `Surreal_Arithmetic_Topological_Collapse` (delivered in `aa268a4`, placed in `7d04483`) |
| Pin | none; blobs of this report's source at `b3fa9e2` and at `20c4c9f` (it saw Part III, not Part IV) |
| Contributes | Part V (Sections 38–42), sub-prefix `opa:tc:` (44 labels): Hahn-compatible ring topologies (Definition 39.1) on `𝔬 ⊕ Π`, `Γ` densely ordered, are exactly the pullbacks along `ct` of ring topologies on `𝔬` (Lemmas 39.2–39.3, Theorem 39.4, Corollary 39.5); on `Oz`, `Oz[i]` they see only `Z`, `Z[i]`, never Hausdorff (Theorem 39.7), and countable monomial sums suffice (Proposition 39.8); on `No`, `No(i)` only the indiscrete topology (Corollary 39.9); automorphisms are invisible to them (Corollary 39.10); a set-sized full Hahn field has a Hausdorff one iff `Γ = 0` or `Γ ≅ Z` (Lemma 39.11, Theorem 39.12); the pairing topology realizes exactly the Hahn sums, continuous linear maps are the strong ones, and multiplication is not jointly continuous (Section 41) |
| Placement | a new Part after Part IV, before the appendices; no existing number changes |
| Printed once | its algebraic half (Sections 4–10 of 15): detection (Theorem 21.4), transport (Theorem 22.1), reconstruction and set pairs (Proposition 23.1, Corollary 23.4), automatic strongness (Theorem 23.2), monomial determination (Corollary 23.5), factorization (Theorem 24.1), the criterion (Theorem 3.3), rank one (Corollary 24.3, Remark 36.3), the shear (Remark 36.4), Gaussian theorems (Theorems 30.1, 30.2), duality and the class functional (Proposition 25.1, Theorems 25.2, 25.6); 15 added to their sources (Section 38.2 has the table) |
| Kept as a route | its disjoint-row proof of detection, a variant of 14's induced matching (Lemma 40.1) |
| New besides topology | interpolation (Corollary 40.2), the naive-detector example (Example 40.3, beside Example 34.3), the Gaussian ring corollary (Corollary 40.4), the class description of the strong dual of `No` (Proposition 40.5), which answers the first clause of Question 32.11 |
| Renamed symbols | topologies `𝒯 → 𝔗`; closure of zero `N →` the closure of `{0}`; exponent sets `D, E → 𝖠, 𝖡`; `R_{𝔬,Γ} → ℛ_𝔬`; `ρ → α`; `No[i] → No(i)`; its invisibility corollary is Corollary 39.10, **not** Corollary 24.4 (Section 38.3) |
| Merge additions `[merge]` | Remark 39.6 (the congruence and `p`-adic topologies of the quotient and Diophantine reports, and their Lean formalization, are instances), the comparison with `found:sub:tsum` in Remark 39.13, the note after Question 42.2, the relation after Question 42.6, status notes |
| Verification | suite rerun on a copy: 27,139 assertions in 14 categories, `passed`; the written record is identical to the shipped one |

### Source 16 (batch 32): coefficient recovery at arbitrary rank

| | |
|---|---|
| Manuscript | *Recovering Surreal Coefficients from Monomial Extensions: quartic definitions, arbitrary-rank rigidity, and sharp cancellation*, 23 September 2026, 24 pages; batch 32 item 08, archive `surreal_coefficient_rigidity` (delivered in `aa268a4`, placed in `7d04483`) |
| Pin | `1ab41af` (contains Parts I–III); its prior manuscript is source 02 (pin `fb5c4b5`) |
| Contributes | Part VI (Sections 43–52), sub-prefix `opa:cr:` (66 labels): Mason–Stothers and the quartic (Lemmas 45.1–45.2, Theorem 45.3); `∃y (y² = 1 + x⁴)` defines `F` in `F(U^G)` and a denominator-cleared form defines `R` in `R[U^M]` (Theorem 45.4, Corollaries 45.5, 45.8, Theorem 45.7); the sharp bound `n ≤ max(wt P, wt Q) − 1` (Lemma 46.1, Theorem 46.2) and the all-order root locus (Proposition 46.5); coefficient rigidity into every `S[U^M]` (Theorem 47.1) and the intrinsic set `𝔆` (Proposition 47.2); automorphisms of group and divisible-monoid algebras (Theorems 48.1, 48.3, Example 48.4); the `Hom(G, Z) = 0` criterion (Theorem 49.2, via Lin–Wang, Cited theorem 49.1; independent for unbounded-root generators, Proposition 49.3) and pair reconstruction (Theorem 49.5); finite-rank cancellation and its exact failure for `Q^(κ)` (Theorems 50.1, 50.3, 50.4); Hahn, translation and characteristic-`p` boundaries (Section 51) |
| Placement | a new Part after Part V, before the appendices; no existing number changes |
| Generalizes | Part II's Theorems 15.1 and 15.3 (to every cancellative torsion-free monoid), 15.4 (to finite rational rank; exact failure at infinite rank, parallel to `R[X_1, X_2] = B[X_2]`), 15.5 (torus part, `GL_q(Z)` to `Aut(G)`) |
| Printed once | its Proposition 6.2, Definition 6.1, Example 6.3 as Theorem 13.1, Corollary 13.3, Definition 12.1 and the workspace of Section 18 (16 added); its Proposition 4.1 as `odg:thm:fractions` and the unit lemmas; its Question 12.8 as Question 19.3 |
| Renamed symbols | **16's `X^g` is an external indeterminate, written `U^g` here**; Part II's `X^g = t^{−g} = ω^g` is a Hahn monomial. `K_k(G) → k(U^G)` (not the Hahn field `K_Γ`); `Δ_k(G) → Def_k(G)`; `𝒰_∞ → Rt_∞`; `D(G) → G_div`; `𝒟, 𝒞 → 𝔇, 𝔆`; monoids `M, N → 𝖬, 𝖭`; its coefficient automorphism `σ → α`; `H → G'`; `v, d, w → min supp, max supp, wd`; `ℓ → λ`; `T d/dT → ϑ`; `𝔖_d → Sym(d)` (Section 43.3) |
| Merge additions `[merge]` | the relation of Question 52.9 to `odg:def:q:realform` and Question 32.1; the record that 16 does not answer `odg:def:q:coeffpe` (Section 52.2); status notes and the pointer after Theorem 15.5 |
| Verification | suite rerun on a copy: 1,314 checks in 12 categories, `PASS`; the record differs from the shipped one only in `python` (3.14.4 vs 3.13.5) and `elapsed_seconds` |

### Source 17 (batch 33): full formal orbit fields

| | |
|---|---|
| Manuscript | *Full Formal Orbit Fields of Surreal Arithmetic: proper-class independence, exact algebraic trajectories, and the effect of changing the formal parameter*, 23 September 2026, 25 pages; batch 33 manuscript 03, archive `Surreal_Formal_Orbit_Fields` (delivered in `73043eb`, placed in `aa9c891`) |
| Pin | `efc5446` (Parts I–III; it saw neither Part IV's write nor Parts V–VI) |
| Contributes | Part VII (Sections 53–59), sub-prefix `opa:of:` (82 labels): `D_0` and its constant field `𝖢_0` (Proposition 54.1, Corollaries 54.3, 54.5); the differential-field lemmas (Lemmas 54.4, 54.6–54.11, Example 54.8); exact additive descent, the trajectory criterion and parameter exclusion (Theorem 55.2, Corollary 55.3, Theorem 55.4); the witnesses `Ξ_α` and their independence (Lemmas 56.1–56.4, Theorem 56.5, Corollary 56.6); the multiplicative clock (Proposition 57.1, Theorems 57.2, 57.3, Corollaries 57.4, 57.5); the monomial test, examples, `lcm` degrees, the surcomplex case, omnific generators and the abstract theorem (Section 58); ten questions (Section 59.3) |
| Placement | a new Part after Part VI, before the appendices; no existing number changes |
| Answers | for `D_0`, the lower bound left after Corollary 17.9 and in 02's sixth non-claim; status notes there |
| Printed once | its fraction lemma as `odg:thm:fractions`; its derivation as Theorem 17.6 with `b = 0`; the ring and flow parts of its Taylor embedding as Theorem 17.2; its monomial comparison as Lemma 17.4, Theorem 17.5, Corollary 17.9 (Section 53.2) |
| Renamed symbols | `D, h → D_0, q_0`; `H, C → ker q_0, 𝖢_0`; `𝒯_s, 𝒰_v → ℰ_{0,s}, Υ_v`; `L_add, L_mult → L̂_0, L̂^×_0`; `𝔓 → Π`; `Const(K,D), C_K → K^∂`; `δ, δ_m, ∂ = −ωD → ∇_s, ∇^×, D̃_0`; `A_α, B_α, a_α, M_α, E_α, X_α → 𝔞_α, 𝔟_α, ζ_α, ω^{𝔟_α}, exp(ζ_α z), Ξ_α`; `F, M, A, A'` written out (Section 53.3) |
| Merge additions `[merge]` | Corollary 58.7 (descent for every Euler flow `D_χ`); the merged Questions 59.6 (with 19) and 59.10 (with 18 and 19); status notes |
| Verification | suite rerun on a copy (SymPy 1.14.0, about 22 s): 30,900 assertions in 24 groups, `passed`; the written record differs from the shipped one only in `python_version` (3.14.4 vs 3.13.5), up to line endings |

### Source 18 (batch 33): left-orderable symmetry groups

| | |
|---|---|
| Manuscript | *Relative Universality and Exact Fixed Fields of Strong Omnific Symmetries: group realization, two-level Hahn supports, and conjugation on the surcomplex field*, 23 September 2026, 24 pages; batch 33 manuscript 05, archive `Surreal_Exact_Symmetries_Research` (delivered in `73043eb`, placed in `aa9c891`) |
| Pin | `efc5446`, tree `aba6982` (Parts I–III) |
| Contributes | Part VIII (Sections 60–66), sub-prefix `opa:es:` (66 labels): Theorems 60.1 and 60.4 with Corollaries 60.2, 60.3; the lifts (Definition 61.1, Proposition 61.2, Remark 61.3); orbit supports and two-level hulls (Lemma 61.4, Theorem 61.5, Proposition 61.6, Lemma 61.7); the set-cut property, back-and-forth and free equivariant cut filling (Section 62); the converse, the field–ring equivalence, the fraction gap and products (Section 63); translation, dilation, two-point and Klein-bottle examples and the countable route (Section 64); complex fixed fields, the nonreal-parameter obstruction, the parity tower and the phase-twist fixed fields (Section 65); ten questions (Section 66.3) |
| Placement | a new Part after Part VII, before the appendices; no existing number changes |
| Answers | no named question; it generalizes Theorem 7.6 from `R^κ` to every left-orderable set group (in the monomial factor, not in `U_Oz`) and sharpens Theorem 7.2 to single automorphisms; Question 11.3 is not addressed (note there) |
| Printed once | its fraction and floor lemmas as `odg:thm:fractions` and Corollary 5.2; its lifts as `ι_φ` and `M_{1,ι_φ}` (Lemma 27.1); its Lemma 8.2 as `saut:thm:axis`; its infinite-order clause as `saut:thm:torsion`; its twist as `saut:thm:phase` (Section 60.2) |
| Renamed symbols | **`ℋ(B)` → `NF(B)`** (not the hull `ℋ(A)`); `𝒦_B → 𝖪_B`; `σ_2 → Σ_2`; `T_φ, F_φ → ι_φ, M_{1,ι_φ}`; `No_C, Oz_C, c → No(i), Oz[i], cj`; cut `D`, `H`, `C_D` → `𝖼, G_𝖼, I_𝖼`; `H` in `H × C_2` → `G_0`; `X, X_α → 𝒳, 𝒳_α`; `U, χ, E_n → Φ_ph, χ_ph, 𝖤_n`; `h → ψ`, `h_KB` (Section 60.3) |
| Merge additions `[merge]` | the identification with Part III's lifts; Remark 63.5; the remarks on `saut:thm:torsion` and `saut:thm:phase`; 18's Question 11.5 merged into Question 32.15 and 11.10 into 59.10; status notes |
| Verification | suite rerun on a copy (about 1 s): 11,330 assertions in 19 categories, seed 20260923, `PASS`; the written record is identical to the shipped one up to line endings |

### Source 19 (batch 33): all derivations integrate

| | |
|---|---|
| Manuscript | *All Derivations Integrate: Formal Symmetry and Coefficient Definability of Omnific Arithmetic*, 23 September 2026, 25 pages; batch 33 manuscript 08, archive `omnific_formal_symmetry` (delivered in `73043eb`, placed in `aa9c891`) |
| Pin | `889b87c` (Parts I–IV; not Parts V–VI) |
| Contributes | Part IX (Sections 67–75), sub-prefix `opa:hs:` (69 labels): automatic integration (Theorem 67.1, Lemma 68.4, Corollary 68.5), formal fraction fields (Proposition 68.1), divisible-ideal integration for every exponent group and commuting families (Propositions 68.6, 68.7); the exponential–logarithm correspondence, higher-derivation formulas, unique roots (Lemmas 69.1, 69.2, Theorem 69.3, Corollary 69.5); jets (Theorems 70.1, 70.4, Lemmas 70.2, 70.3, Remark 70.5); residue sections, directions beyond the Euler family and the common core (Section 71); the definable evaluation, the curve criterion, formal square roots, universality of the quartic in the completion and the parity exception (Section 72); fresh-direction nondefinability (Section 73); the class-size pointed theorem and escape from finite type (Section 74); eleven questions (Section 75.3) |
| Placement | a new Part after Part VIII, before the appendices; no existing number changes |
| Answers | **Question 19.2** (formal directions), all clauses: every derivation of `Oz`, `Oz[i]` maps into `Π`, preserves it and has the unique iterative integral extension `δⁿ/n!`; the class is strictly larger than the Euler family (it contains `ω d_*`). Status notes after the question, in Section 19 and in Section 52.2 |
| Printed once | its Lemmas 3.1, 3.2 and 11.1 as Lemma 2.3, `odg:thm:fractions` and Lemma 14.1; its `D_η` as Theorem 17.6; its quartic formula (Theorem 8.2, Corollary 8.3) as Part VI's Theorems 45.4, 45.7, printed once as Corollary 72.2; its Lemma 8.1 as Theorem 45.3, kept as a second route (Lemma 72.1); its warnings as Remark 45.6 and Example 51.2 (Section 67.2) |
| Renamed symbols | `T → s`; `𝔍_R, J → Π_R, Π^♯_R`; `H_n → 𝖧_n`; `L → 𝖫`; `G(R) → 𝒢(R)`; `ℓ_η → q_η`; `E_m → ω^m D_0`; `C_R → 𝖢_R`; **`Θ → 𝖰`**; **coefficient section `s` → residue section `ς`** (not Part III's `ρ`); `D_d → d_*`; curve `C → 𝖷` (Section 67.3) |
| Merge additions `[merge]` | Corollary 72.2 in the joint generality; the relations to Theorem 4.8, Corollary 17.7, Lemma 7.1, Example 51.1 and Question 52.1; questions merged into 59.6, 52.2, 19.3 and 59.10; the status after Question 75.2 (answered for `D_0` by Part VII) |
| Verification | suite rerun on a copy (about 2 s): 1,576 checks in 17 groups, seed 20260923, `passed`; the written record is identical to the shipped one up to line endings |

### Source 20 (batch 34): universal symmetries and exact difference equations

| | |
|---|---|
| Manuscript | *Universal Symmetries and Exact Difference Equations over the Surreals: left-orderable groups, omnific stabilizers, fixed fields, and surcomplex descent*, 23 September 2026, 25 pages; batch 34 manuscript 01, archive `Surreal_Universal_Symmetries_and_Difference_Equations` (inner directory `surreal_universal_symmetries`; delivered in `bbe23a3`, placed in `a7a435f`) |
| Pin | `e93a06d`, tree `42aec05` (Parts I–IV and the single-dilation report; not Parts V–IX) |
| Contributes | Part X (Sections 76–82), sub-prefix `opa:us:` (86 labels): Theorems 76.1, 76.2 and Example 76.3; the second cut filling (Proposition 77.1), the outer lift in both coefficient cases (Lemma 77.2), independence of the orbit of `ω` (Proposition 77.3), the translation family `σ^tr_s` (Proposition 77.4); the relative action with fixed field `𝖪_{No∖𝖩,k}` and the independent family `{ω^{ω^a} : a ∈ 𝖩}` (Theorem 77.5); the sequential test, downward-orbit and orbit-direction lemmas (Lemmas 78.1–78.3, Remark 78.4); the weighted Green operator (Theorem 78.5), omnific primitives (Corollary 78.7, Example 78.8); constant-coefficient operators (Theorem 79.1, Corollaries 79.2, 79.3); the inner difference lemma (Lemma 79.4); the multiplicative criterion (Theorem 79.5, Example 79.6) and the relative retraction (Theorem 79.7); the first-order criterion (Theorem 80.1); cocycles (Theorem 80.2, Corollary 80.3, Remark 80.4, Proposition 80.5); set-sized models and `η_κ`-orders (Propositions 81.1, 81.2); the worked equation (Example 82.1); eight questions (Section 82.3) |
| Placement | a new Part after Part IX, before the appendices; no existing number changes |
| Answers | no named question; **Question 66.2 is partly answered** (it realizes `E = NF(No∖𝖩)`, a proper class not of the form `NF(S)`; note after it); 20's own Question 2 is partly settled by Part VIII (status after Question 82.2) |
| Printed once | its universality theorem, fraction lemma, necessity lemma, lifts, invariant-support lemma, fixed-field theorem, parameter corollary and complex classification as Part VIII's and `odg:thm:fractions` (Section 76.2); its difference core is printed with its correspondence to `dsup:lem:orbit`, `dsup:thm:resolvent`, `dsup:cor:fixed`, `dsup:cor:poly`, `dsup:thm:multsingle` and `dsup:cor:simultaneous` (Remark 78.6), which 20 did not read |
| Kept as a route | its cut filling (Proposition 77.1); its one-operator proof of Corollary 80.3 |
| New | independence of the orbit of `ω` and of `{w_a : a ∈ 𝖩}` over the relative fixed field; the proper-class relative fixed field; the translation family; Lemma 79.4 and the explicit image `ker ϖ^in_B` in Theorem 79.7; Theorem 80.1; Corollary 79.3; Theorem 80.2 and Remark 80.4 (every group with a central element; the single-dilation report has only `Z^d`); Proposition 80.5; Propositions 81.1, 81.2 |
| Renamed symbols | **`S_s → σ^tr_s`** (translation lift, `S_1 ≠ id`; not a dilation `S_q`); `p, T_p, σ_p, σ_T → φ, ι_φ, M_{1,ι_φ}, M_{1,τ}`; `F, H_F, H_J, F_{J,k}, B_A, y_a, J → B, NF(B), NF(No∖𝖩), 𝖪_{No∖𝖩,k}, Σ_2(A), w_a, 𝖩`; `M_k = ker c_0 → 𝖵_k = ker ct`; `c_0 → ct`; `H, K_H, P_H, Q_F → Γ_τ, k((ω^{Γ_τ})), ϖ_{Γ_τ}, ϖ^in_B`; `f_± → f_↑, f_↓`; `𝒢_c → Gr_c`; `ℛ_F → mr_B`; `P, X, k(X) → 𝗉, 𝖸, k(𝖸)`; `h, χ → ch⁺, ch^×`; `j → cj`; `No[i], Oz[i], K_k → No(i), Oz[i], No_k` (Section 76.3) |
| Merge additions `[merge]` | Remarks 77.6 and 78.6; the specialization remarks after Theorems 79.5, 79.7 and Corollary 80.3; questions merged into 32.15, 66.3, 66.7 and 59.10; status notes after Questions 11.3, 66.2 and 82.2 and in Appendix B |
| Verification | suite rerun on a copy (about 1 s): 5,555 assertions in 29 groups, seed 20260923, `PASS`; the written record is identical to the shipped one up to line endings |

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

Part V (source 15; Sections 38–42). A *Hahn-compatible ring topology* makes
addition and multiplication (jointly) continuous and every Hahn sum the limit of
its net of finite partial sums (Definition 39.1); Hausdorffness is not assumed.

- **Theorem 39.4.** For `Γ` densely ordered, any field `k` and unital `𝔬 ⊆ k`, the
  Hahn-compatible ring topologies on `𝔬 ⊕ Π` are exactly `ct^{−1}(𝔗_0)` for ring
  topologies `𝔗_0` on `𝔬`; `Π` lies in the closure of zero, none is Hausdorff. The
  engine is Lemma 39.3: joint continuity and null monomial sequences put every
  negative monomial in the closure of zero, because a dense interval is not the
  union of a set without increasing sequences and one without decreasing ones
  (Lemma 39.2). **Corollary 39.5**: a sum-respecting map into a Hausdorff
  topological ring factors through `ct`.
- **Theorem 39.7 and Proposition 39.8.** On `Oz` and `Oz[i]` every such topology is
  pulled back from `Z` or `Z[i]`; countable monomial sums already force this.
  **Corollary 39.9**: on `No` and `No(i)` only the indiscrete topology qualifies.
  **Corollary 39.10**: automorphisms of `Oz` are invisible to every such topology.
  **Remark 39.6** (merge): the congruence and `p`-adic topologies of the
  Diophantine and quotient reports (formalized in Lean) are such pullbacks.
- **Theorem 39.12.** A set-sized full Hahn field `k((t^Γ))` has a Hausdorff
  Hahn-compatible ring topology iff `Γ = 0` or `Γ ≅ Z` (lexicographic `Z²` is
  excluded); otherwise every ring topology with null increasing monomial sequences
  is indiscrete.
- **Section 40.** A disjoint-row variant of the detection proof (Lemma 40.1),
  interpolation of prescribed pairings (Corollary 40.2), the failure of the naive
  all-ones detector (Example 40.3), the Gaussian ring with conjugation (Corollary
  40.4), and **Proposition 40.5**: the strong `R`-linear functionals on `No` are
  exactly `Σ c_g t^g ↦ Σ c_g a(g)` for class functions `a` whose support has no
  strictly increasing sequence; representable by a surreal iff the support is a set.
- **Section 41.** For set-sized `Γ` and discrete `k`, the weak topology of the
  pairing realizes exactly the Hahn sums (Theorem 41.1), its continuous linear maps
  are the strong ones (Corollary 41.2), and its multiplication is separately but not
  jointly continuous (Theorem 41.3).

Part VI (source 16; Sections 43–52). `F[U^G]` is the finite-support group algebra
of a torsion-free abelian `G` with external monomials `U^g`, `F(U^G)` its fraction
field; `F` is real closed or algebraically closed of characteristic zero.

- **Theorems 45.3, 45.4, 45.7.** `b² = 1 + a⁴` has only constant solutions in
  `k(U^G)` (by Mason–Stothers, Lemma 45.1, and specialization, Lemma 44.3); so
  `∃y (y² = 1 + x⁴)` defines `F` in `F(U^G)`, and
  `∃u ∃v (v ≠ 0 ∧ u² = (1 + x⁴)v²)` defines `R` in `R[U^M]` when `Frac R` is closed,
  for example `Oz`, `Oz[i]`. Embeddings of `No`, `No(i)`, `Oz`, `Oz[i]` land in the
  coefficients (Corollaries 45.5, 45.8).
- **Theorem 46.2.** A nonmonomial `P/Q` that is an `n`th power in any monomial
  extension `L(U^{G'})` has `n ≤ max(wt P, wt Q) − 1`, sharply. **Proposition
  46.5**: the elements with roots of all orders are `cU^g` with `c` such and `g`
  in the divisible part of `G`.
- **Theorem 47.1 and Proposition 47.2.** A root-covered domain embeds into
  `S[U^M]` only inside `S`, for every cancellative torsion-free monoid; this extends
  Theorems 15.1 and 15.3 to arbitrary rank.
- **Theorems 48.1 and 48.3, Example 48.4.** Automorphisms of `R[U^G]` are
  `Σ a_g U^g ↦ Σ α(a_g) χ(g) U^{τ(g)}` (extending Theorem 15.5); for `Oz`, `Oz[i]`
  and divisible `G`, `Aut(R[U^G]) ≅ Aut(R) × Aut(G)`; divisible monoids likewise.
- **Theorem 49.2.** Every field automorphism of `F(U^G)` has that form iff
  `Hom(G, Z) = 0`, using Lin–Wang's defect theorem (Cited theorem 49.1, an
  unrefereed preprint); **Proposition 49.3** proves it without that input when `G`
  is generated by elements of unbounded divisibility. **Theorem 49.5**:
  `F(U^G) ≅ E(U^{G'})` iff `F ≅ E` and `G ≅ G'` (also via Lin–Wang).
- **Theorems 50.1, 50.3, 50.4.** At equal finite rational rank every isomorphism
  `R[U^M] ≅ S[U^N]` maps `R` onto `S` (extending Theorem 15.4); for `Q^(κ)` this
  holds exactly when `κ` is finite, with explicit absorption counterexamples.
- **Section 51.** The quartic detector fails in the Hahn field `k((t^Q))`
  (Example 51.1), `T ↦ T + 1` survives for `G = Z`, and characteristic `p` breaks
  both the sparse bound and the criterion (Example 51.2).

Part VII (source 17; Sections 53–59). `D_0(Σ r_g ω^g) = Σ q_0(g) r_g ω^g`, where `q_0(g)`
is the constant coefficient of the exponent `g`; `𝖢_0 = ker D_0` is real closed and
contains `ω^ω`; `ℰ_{0,s}(x) = Σ D_0ⁿ(x) sⁿ/n!` and `L̂_0 = No(ℰ_{0,s}(No))` in `No((s))`.

- **Theorems 53.1 and 55.2, Corollary 55.3.** `No(s)` and `ℰ_{0,s}(No)` are linearly
  disjoint over `𝖢_0`, since `No(s)` and the whole Laurent field have constant fields
  `𝖢_0` and `ℰ_{0,s}(No)` for `D_0 − d/ds` (no additive slice: `ct(D_0 y) = 0`). All
  polynomial relations of a transformed tuple descend from `𝖢_0`, and a trajectory is
  algebraic, or rational, over `No(s)` exactly when `x ∈ 𝖢_0`.
- **Theorem 55.4.** `s` is transcendental over `L̂_0`, although `e^s = ℰ_{0,s}(ω)/ω ∈ L̂_0`.
- **Theorems 53.2 and 56.5, Corollary 56.6.** For every ordinal `α`,
  `Ξ_α = Σ_n ω^{ω^{α+2} − n(ω^{α+1}+1)}/n!` is a countably supported purely infinite
  omnific integer; the `Ξ_α` are algebraically independent over `𝖢_0(ω)` (they satisfy
  `D̃_0 Ξ_α = ζ_α Ξ_α` with `Q`-independent constants `ζ_α = ω^{−ω^{α+1}}`), so `L̂_0` has
  independent families of every set cardinality and no set-sized transcendence basis.
- **Theorems 53.3, 57.2, 57.3, Corollaries 57.4, 57.5.** For `Υ_v = (1+v)^{D_0}` and
  `u = 1 + v`, the image and `No(u)` are linearly disjoint over `𝖢_0(ωu)`; `Υ_v(x)` is
  rational over `No(u)` iff `x ∈ 𝖢_0(ω)` and algebraic iff `x` is algebraic over `𝖢_0(ω)`,
  with equal degrees; `u = Υ_v(ω)/ω` lies in the orbit field.
- **Proposition 58.1, Examples 58.2, 58.3, (58.1).** `Υ_v(ω^g)` is rational iff
  `q_0(g) ∈ Z` and algebraic iff `q_0(g) ∈ Q`, of degree the reduced denominator;
  `ℰ_{0,s}(ω^g)` is algebraic iff `q_0(g) = 0`; lcm degrees.
- **Theorem 58.4, Proposition 58.5, Theorem 58.6, Corollary 58.7.** The surcomplex
  case; the orbit fields are generated by omnific inputs; the abstract theorem for any
  characteristic-zero differential field; and (merge) descent for every Euler flow of
  Part II.

Part VIII (source 18; Sections 60–66). `NF(B)` is the class of normal forms supported in
`B`, `𝖪_S = NF(NF(S))`, and `Σ_2(A)` the inner supports of the outer exponents of `A`.

- **Theorem 60.1.** For every set `S` and nontrivial left-orderable set group `G`, a
  faithful action by strongly additive, real-fixing, monomial-permuting automorphisms
  preserving `Oz`, `ct` and the floor, with `Fix(σ_g) = 𝖪_S` and `Fix_Oz(σ_g) = Oz ∩ 𝖪_S`
  for every `g ≠ 1`, faithful on `Oz`; conversely set groups acting faithfully on `No`,
  or on `Oz` by ring automorphisms, are left-orderable. **Corollaries 60.2, 60.3**:
  `Fix = 𝖪_{Σ_2(A)} ⊇ A` for any set of parameters; fixed field `R` and fixed ring `Z`,
  free actions outside them.
- **Proposition 61.2, Theorem 61.5, Proposition 61.6.** The lifts `ι_φ` and `M_{1,ι_φ}`;
  exact two-level fixed supports; `S ↦ 𝖪_S` is injective and `𝖪_{Σ_2(A)}` is the least
  field of this form containing `A`.
- **Lemma 62.3, Theorems 62.4, 62.6.** Free insertion of ordered fibers at all cut orbits,
  a free action on an order with the set-cut property, hence on `No`, and exact fixed
  index sets `S`.
- **Corollaries 63.2–63.4.** Left-orderable ⇔ faithful on `No` ⇔ faithful on `Oz`;
  every nonidentity automorphism of `Oz` has infinite order;
  `Frac(Fix_Oz σ_g) = Q ⊊ Fix σ_g = R`; unrestricted set products.
- **Section 64.** Index translation (fixed field `R`), dilation (`R((ω^R))`), a two-point
  index set, the countable dynamical route, and the Klein bottle group (left-orderable, not
  bi-orderable).
- **Theorem 60.4, Section 65.** Conjugation-compatible faithful actions on `No(i)` or `Oz[i]`:
  exactly `G_0` and `G_0 × C_2` with `G_0` left-orderable; a fixed nonreal parameter excludes
  `C_2`; complex fixed fields `𝖪_S(i)`; a parity tower; the phase twist `Φ_ph` has fixed
  fields `C((ω^{𝖤_n}))`, not algebraically closed.

Part IX (source 19; Sections 67–75). `R` is one of `Oz`, `Oz[i]`, `No`, `No(i)`; `s` is a
formal variable.

- **Theorem 67.1, Corollary 68.5.** Every derivation of `Oz`, `Oz[i]` maps into `Π_R` and
  preserves it (since `Π_R = ⋂ nR`), and `δⁿ/n!` is its unique iterative integral
  Hasse–Schmidt extension: **Question 19.2 is answered**. **Proposition 68.6**: the same for
  `Z ⊕ Π(Γ)` over every set-sized ordered group.
- **Theorem 69.3, Corollary 69.5.** `exp` and `log` identify `s Der(R)[[s]]` with the
  `s`-fixing automorphisms of `R[[s]]` tangent to the identity; unique roots; stabilizers.
- **Theorems 70.1 and 70.4.** Every jet lifts; the `N`th jet group has class exactly `N`,
  and its central extensions do not split for `N ≥ 2` (`[D_0, ωD_0] = ωD_0`).
- **Theorems 71.1 and 71.4.** Residue sections correspond to the formal automorphisms;
  their common core is `Z`, `Z[i]`, the real algebraic numbers or `Q̄`.
- **Corollary 72.2, Theorem 72.7, Proposition 72.8.** The quartic formula defines `A` in every
  intermediate ring of `K(U^G)` (with 16), but holds of every element of `Oz[[s]]`,
  `Oz[i][[s]]`, `No[[s]]`, and in `No(i)[[s]]` up to an order parity.
- **Theorem 73.2, Corollaries 73.3, 73.4.** No set of parameters defines the canonical
  coefficient copy in `R[[s]]`, or any residue section, although `R[[s]]/(s)` is
  interpretable.
- **Theorem 74.2, Corollary 74.3.** Pointed finite-type parameter families are trivial for
  the class rings, so no nonstandard formal section factors through finite type.

Part X (source 20; Sections 76–82). `k = R` or `C`, `No_R = No`, `No_C = No(i)`,
`𝖵_k = ker ct = Π_k ⊕ 𝔪_k`; `σ_g = M_{1,ι_{φ_g}}` for a free increasing index action `φ_g`.

- **Theorem 76.1.** Left-orderable ⇔ faithful on `No` ⇔ faithful on `Oz` (Part VIII's
  theorem, derived independently); the actions can have `Fix(σ_g) = R` (`C` on `No(i)`) for
  every `g ≠ 1` and, **new**, the orbit of `ω` algebraically independent (Proposition 77.3).
- **Theorem 77.5, Remark 77.6.** For a set `A ⊆ No(i)` and `𝖩 = (u, u+1)` above `Σ_2(A)`, an
  action fixing `A` with `Fix(σ_g) = 𝖪_{No∖𝖩,k}` for every `g ≠ 1`, a **proper class**
  strictly containing Part VIII's set-sized `𝖪_{Σ_2(A)}`; `{ω^{ω^a} : a ∈ 𝖩}` is algebraically
  independent over it.
- **Theorem 78.5.** For `σ = M_{1,τ}` and `c ∈ k^×` the weighted Green operator solves
  `(σ − c)x = f` exactly when `ϖ_{Γ_τ} f = 0`, uniquely with `ϖ x = 0`; `ker(σ − 1)` is the
  fixed field and `im(σ − 1) = ker ϖ` (the single-dilation resolvent with `χ = 1`).
- **Theorem 76.2, Corollary 78.7, Theorem 79.1.** For the global action: `σx − x = b` iff
  `ct(b) = 0`; `σ − 1` is bijective on `Π_k` and `𝔪_k`, with omnific primitives unique up to
  `Z`; every nonzero Laurent polynomial in `σ` is bijective on `𝖵_k`, and `𝖵_k` is a
  `k(𝖸)`-vector space (Corollary 79.3). Example: `x = Σ_{n≥1} ω^{ω^{−n}} ∈ Oz` solves
  `σ^tr_1 x − x = ω`, while `σ^tr_1 x − x = 1` is unsolvable.
- **Lemma 79.4, Theorems 79.5, 79.7.** `ι_φ − 1` is bijective when `φ` has no fixed point;
  `σx/x = a` iff `lc(a) = 1` globally; for any `φ` the retraction `mr_B` gives three
  obstructions (`lc(a) = 1`, `ϖ^in_B γ(a) = 0`, `ϖ log(unit) = 0`).
- **Theorem 80.1.** `σx − ax = b`: unique solution if `lc(a) ≠ 1`; otherwise solvable iff
  `ct(b/σu) = 0`, `u` the normalized gauge with `σu/u = a/lc(a)`.
- **Theorem 80.2, Corollary 80.3, Remark 80.4, Proposition 80.5.** For groups with a central
  nonidentity element every cocycle is a character plus a coboundary (`H¹ = Hom(G, k)`,
  `Hom(G, k^×)`), also relative to parameters; commuting systems; free groups have extra
  invariants.
- **Section 81.** Named-conjugation classification as Part VIII's Theorem 60.4; a choice-free
  ZFC Hahn model for every left-orderable group (Proposition 81.1) and free actions on
  `η_κ`-orders of size `κ` when `κ^{<κ} = κ` (Proposition 81.2).

## What the report does not claim

Appendix B lists every source's non-claims: 13 from 09, 13 from 04, 12 from
08, 11 from 02, 18 from 10, 13 from 11, 14 from 12, 12 from 13, 16 from 14, 17
from 15, 14 from 16, 15 from 17, 15 from 18, 14 from 19 and 22 from 20.
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
    claimed for automorphisms preserving `Oz[i]` but not conjugation (for
    involutions rather than copies, `saut:fs:thm:large-family` gives `2^𝔠` strong
    valued `Oz[i]`-preserving involutions, pairwise nonconjugate under all field
    automorphisms; batch-32 note after Corollary 30.5);
  - the support-bound result is for regular uncountable `κ`; no singular case and
    no birthday cutoff (for singular `κ` the characterization fails:
    `fkc:sb:thm:sums`, batch-32 note after Proposition 31.1);
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
- Source 15 (Part V):
  - only compatibility with **every** Hahn sum is excluded: ring topologies
    without the summation requirement are not excluded, and the discrete topology
    always exists;
  - **joint** continuity is essential: the pairing topology (Section 41) is
    Hausdorff, realizes all sums and is only separately continuous;
  - dense `Γ` is assumed for the ring classification; truncated rings for
    non-dense groups such as lexicographic `Z²` are open (Question 42.1);
  - the cyclic case is existence only, not a classification;
  - the countable-only strengthening needs the positive buffer of the class `No`
    and fails as a proof for `Γ = Q`;
  - automatic strongness and its machinery are credited to 12 and 13; the
    disjoint-row detector is an alternative proof, not a priority claim;
  - unrestricted Gaussian automatic strongness is not proved; admissibility of
    monomial prescriptions is not solved; invariance is not definability;
  - self-duality needs set-sized groups; the detector needs a full Hahn field or
    enough detectors; the isomorphism argument uses surjectivity;
  - the pairing topology uses discrete coefficients and is not Flynn–Shamseddine's;
  - finite checks do not test the infinite covering lemmas or arbitrary
    topologies; unrefereed, no Lean, priority not certified, its reading of this
    report incomplete, no repository build.
- Source 16 (Part VI):
  - not refereed, no Lean, priority not certified; targeted repository comparison;
  - no Conway factorization conjecture and no unrestricted automorphism problem is
    solved; `Aut(No)` and `Aut(No(i))` stay coefficient data;
  - the general Theorem 49.2 and Theorem 49.5 depend on Lin–Wang's Theorem 4.5, an
    unrefereed preprint, which is not reproved;
  - the field formula does not define `Oz` (or `R`) in the pure field `No`; the ring
    formula lives in `R[U^M]` and needs an inequation;
  - the set `𝔆` is infinitary; all-order root membership is not first order;
  - nothing on Gaussian stabilizers, Hahn summation or conjugation: these are
    finite-support extensions, not Hahn completions;
  - characteristic zero, domains and cancellative torsion-free monoids only;
    injectivity is needed; noninjective maps and reduced parameter rings are not
    treated;
  - the infinite-rank failure is proved only for `Q^(κ)`;
  - its classical inputs (Mason–Stothers, sparse multiplicity, units, rank,
    defect freeness) and 02's framework are not claimed; finite checks are not
    proofs.
- Source 17 (Part VII):
  - Taylor morphisms, Euler derivations, independence of exponential solutions, the
    constants and linear-disjointness lemmas, the logarithmic-derivative obstruction,
    Vandermonde, Eisenstein and scalar extension are not new; no identification with a
    Galois hull (Ng, Heiderich, Kolchin are background);
  - only `D_0` is treated: no transfer to a derivation with a slice (Example 54.8) or to a
    changed Hahn presentation;
  - `s` and `v` are formal: no surreal is substituted, and no independence-preserving
    evaluation into `No` is claimed (independence over `No` cannot survive it);
  - no single proper-class transcendence degree; no algorithm for `𝖢_0(ω)` or its relative
    closure; the formal flows are not internal automorphisms of `No`;
  - nothing on other real forms or arbitrary surcomplex automorphisms; `D_0` is not the
    Berarducci–Mantova derivation;
  - no named conjecture; finite checks are not proofs; no Lean, no peer review, no
    priority; targeted comparison with truncated connector reads.
- Source 18 (Part VIII):
  - the double lift and the existence of nontrivial or nonabelian omnific automorphisms
    are not new (Kaplan–Krapp–Serra Construction 3.10, Kuhlmann–Serra, this report);
  - no classification of `Aut(Oz)` and no claim that arbitrary automorphisms are strong
    (for `Oz` Part III now proves they are); no classification of all fixed subfields or
    conjugacy classes; minimality of `𝖪_{Σ_2(A)}` holds only within the family `𝖪_S`;
  - the maps preserve the monomial class, not the omega-map, the Gonshor exponential,
    derivations, simplicity or birthdays; no birthday-cutoff transfer;
  - not claimed that every automorphism of `No` fixes `R`; no classification of complex
    actions without a named conjugation; Rivas' dynamical realization is used only for
    the optional explicit route;
  - no Lean, no peer review, no priority; finite checks do not cover cut filling or class
    recursion; guide-level source inspection.
- Source 19 (Part IX):
  - no classification of derivations by support; they are not claimed `R`-linear or strong;
  - the integration result is not the Hahn-evaluation question; no surreal evaluation of `s`;
  - formal Lie theory (Hazewinkel, Narváez-Macarro–Tirado Hernández, Bagayoko),
    Riemann–Hurwitz and strong invariance (Hirano), and Part II's results are not new;
  - only marked residue sections are classified; `𝖰` is existential, not
    positive-existential, with no optimality; the surcomplex-field completion has a parity
    exception, and the finite-jet universality is a nilpotent phenomenon;
  - nondefinability of the canonical copy does not forbid interpreting the residue ring;
    nothing on the whole of `Aut(Oz)`, no canonical real form of `No(i)`;
  - no Lean, no peer review, no priority; checks use `Z + XQ[X]` only; the audit notes
    truncated reads and packaging after midnight UTC.
- Source 20 (Part X):
  - manuscript proofs only; not refereed, no Lean, no repository build; the two Hahn lifts
    (Kaplan–Krapp–Serra, Kuhlmann–Serra) and the centralizer factorization (`saut:thm:axis`)
    are prior; priority not certified (targeted review of five guides);
  - no named problem solved, in particular none of Kaplan–Krapp–Serra's Section 5 questions;
    the maps need not preserve simplicity, birthdays, the omega-map (`σ^tr_1(ω) ≠ ω^{σ^tr_1(1)}`),
    the Gonshor exponential or the Berarducci–Mantova derivation;
  - higher-order variable-coefficient and matrix equations are not classified; `(No(i), σ)` is
    not difference closed (`σx − x = 1` is unsolvable);
  - the leading-coefficient-only multiplicative criterion holds for the global action only; the
    relative action has three obstructions; `mr_B` is not a field homomorphism and not
    `Oz`-preserving; `ϖ` and `ct` are not multiplicative; `k(𝖸)` acts by operators, not scalars;
    formal logarithms only on `1 + 𝔪_k`;
  - no Galois correspondence; Theorem 77.5 does not identify all fixed fields, and its
    proper-class independence is only through finite subsets; no weighted inverse with
    coefficients beyond `k`;
  - Theorem 76.1 classifies groups that embed, not full automorphism groups or conjugacy
    classes; the complex classification needs named conjugation; not claimed that every field
    automorphism of `No` fixes `R`;
  - the cut completion is not a Dedekind completion and gives no free action on the real line;
    `η_κ`-orders carry no birthday cutoff; exact sequences and `H¹` are shorthand, not quotients
    of classes;
  - finite checks certify no infinite, class or priority statement; its questions are
    directions, not published problems.
- **Status (batch 33).** 02's non-claim that only a lower bound holds for the full formal
  image is kept as its record; for `D_0` Part VII now describes the full image. 02's
  non-claim that it classifies no derivations stays true: Part IX shows all derivations
  integrate, not what they are.
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
    recorded with it. Batch 33: 18's realizations lie in the monomial factor, not in
    `U_Oz`, so they do not bear on it (a single one can fix exactly `𝖪_{Σ_2(A)} ⊇ R((t^{V_A}))`);
    batch 34: nor do 20's relative actions (fixed field `𝖪_{No∖𝖩}`, Remark 77.6); open.
  - 11.4: generation and exhaustion (04 Q4 with 08 Q1 and 10's generation
    question). 15 asks it again (batch 32); a topology realizing all Hahn sums
    offers no shortcut, since on `No` every one is indiscrete. Open.
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
  - 32.1: the unrestricted Gaussian stabilizer (12, 13, 14, 15). Still open; 14
    proposes `C((t^Q))`, then a rank-two lexicographic group, as first targets.
    15 notes that compatible topologies cannot help (they are indiscrete on
    `No(i)`); 16 recovers `No(i)` as a coefficient field but not its conjugation.
    The surcomplex automorphism report's valued results (`saut:fs:rem:gaussianstrong`,
    `saut:fs:thm:main-involutions`) assume the valuation and do not address it.
    Batch 34: still open; that report's source 03 asks it again
    (`saut:gr:sec:questions`) and adds `saut:gr:q:nonvalued` (can an involution
    preserve `Oz[i]` but not the valuation?), whose first clause a positive
    answer here would settle negatively.
  - 32.2: must an embedding `f` of `No` with `f^{−1}(Oz) = Oz` be strong, also
    when `ct ∘ f = ct`, and what survives without strongness (12, 13, 14; 11)?
    **Negative answer under a measurable cardinal**: the large-cardinal report
    ([`large-cardinal-embeddings-and-normal-forms`](../../foundations-and-computation/large-cardinal-embeddings-and-normal-forms/))
    shows that applying an elementary embedding `j` with critical point to sign
    sequences gives an ordered field embedding of `No` that fixes `R`, preserves
    and reflects `Oz`, preserves `ct` and is not strongly additive. It is not
    onto, so it does not conflict with Theorem 23.2. Without large cardinals the
    question stays open, as do 11's clauses on dense images and images neither
    closed nor discrete. Batch 32: by `lce:mf:thm:spectrum` and
    `lce:mf:thm:equivalence`, in a universe without measurable cardinals a
    coefficient-fixing counterexample must fail a countable sum
    (`lce:mf:q:countable`, open).
  - 32.3: target tests for coefficient-fixing embeddings (13, 14). **Negative
    under a measurable cardinal** (batch 32): `lce:mf:thm:target` gives a
    pulled-back test with no source multiplier (already implied by Theorem 25.2
    and 32.2's status); the strong-embedding version is `lce:mf:q:targetstrong`,
    open.
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
  - 32.11: the proper-class strong dual (12, 14, 15). **First clause answered**
    (batch 32) by 15's Proposition 40.5: the strong `R`-linear functionals on `No`
    are exactly the class coefficient functionals whose support meets every
    well-ordered set finitely. The second clause (which operators have
    set-supported transposes) is 15's Question 9 and stays open.
  - 32.12: singular support bounds (12, 13, 15). **Partial information** (batch 31,
    Remark 35.4): the image family is Hahn summable with the right sum; only the
    size of the union of its supports remains open. 15 asks it again (batch 32).
    `fkc:sb:thm:sums` bears on it (summability in `K_{<κ}` for singular `κ` is
    not decided by counting members) but does not answer it.
  - 32.13: other rings and coefficient fields (12, 14, with the merge's clause on
    general `(k, 𝔬)`). **Partial information** (batch 32): for `Γ = No` and
    `𝔬 ∈ {Z, Z[i]}`, automorphisms of `ℛ_𝔬` preserve `k` and `Π`
    (`saut:fs:prop:reconstruction`) and valued ones are strong
    (`saut:fs:rem:gaussianstrong`); without the valuation it stays open.
    Batch 34: still open; `saut:gr:sec:questions` (its source 03's Question 5)
    asks the `(k, 𝔬)` clause again, notes that `⋂ n𝔬` must be controlled, and
    `saut:gr:q:charp` asks the positive-characteristic analogue.
  - 32.14: isomorphisms of small integer parts (13, 14). 14 asks the automorphism
    case with uniqueness; **uniqueness is answered** by Proposition 36.5 (merge),
    existence stays open.
  - 32.15: exponential, omega-map and differential structure (11, 12, 13, 18, 20). 18 asks it
    for its group realizations (batch 33): which left-orderable groups survive when the
    Gonshor exponential, the omega-map or a derivation must be preserved; 20 asks it again
    (batch 34, its Question 1); open.
  - 32.16–32.18: restricted workspaces and compositions (11); formalization
    (11, 12, 13, 14, 15; 15 proposes formalizing the collapse over abstract
    ordered monomial systems first). For 32.17, image inclusion and intersection inside one
    independent family with `ρ = id` are settled by `isc:thm:boolean` (batch 31
    status note); composition and the general case stay open.
- **Question 37.1** (Part IV, 14), new: can the countable detector property be
  weakened to a necessary and sufficient closure condition for product
  detection, and which computable or transseries subfields satisfy it? Example
  35.3 shows that some closure is needed. 14's other seven questions are merged
  into 32.1, 32.2–32.3, 32.11, 32.13 (with 11.7), 11.2 (with 11.4), 32.14 and
  32.18 (Section 37.1). 15 asks it again (batch 32); **partly addressed** by the
  sufficient condition of Definition 35.1 and Proposition 35.2, open.
- **Questions 42.1–42.6** (Part V, 15), new: Hausdorff compatible topologies on
  truncated rings for non-dense groups, first lexicographic `Z²` (42.1); minimal
  families of countable monomial sums forcing the collapse, answered for the full
  omnific rings by Proposition 39.8 but open for `Γ = Q` (42.2); maximal summation
  laws realizable in a valuation topology (42.3); a summation-sensitive tensor
  framework (42.4); which parts of the summation law must be dropped to separate a
  chosen set of scales (42.5); definability of summation beyond automorphism
  invariance (42.6). 15's other six questions are merged into 32.1, 37.1, 32.12,
  32.11, 11.4 and 32.18 (Section 42.1).
- **Questions 52.1–52.10** (Part VI, 16), new: intermediate fields between
  `k(U^G)` and the Hahn field that keep quartic rigidity (52.1); removing the
  inequation from the ring formula (52.2); refined root certificates (52.3);
  positive characteristic (52.4); cancellation for nonabsorbing infinite-rank groups
  (52.5); monoids without divisibility (52.6); coefficient definability for other
  root-covered domains (52.7); definability of the monomial subgroup (52.8);
  real-form recovery in larger surcomplex extensions, related to
  `odg:def:q:realform` and 32.1 (52.9); staged formalization (52.10). 16's Question
  12.8 is 19.3. Batch 33: 19 found 16's ring formula independently and asks 52.2 again
  (tagged 16, 19; open); its Theorem 72.7 shows the formula holds of every element of the
  omnific formal completions, which bears on 52.1 without answering it.
- **08's Question 2** asked whether `C` is first-order reconstructible from
  the pure ring `Oz[i]`. It is **answered** by `odg:def:cor:internal`, and
  independently by 09's Pell-divisibility route, so it is dropped.
- **02's questions** are 19.1–19.3. Question 19.2, on formal directions, was
  **partly answered** by Part I: positive-shift derivations preserving `Oz`
  are classified, and those with a common shift set integrate to automorphisms
  inside `No`. **Answered** in batch 33 by source 19 (Theorem 67.1, Corollary 68.5):
  every derivation of `Oz` or `Oz[i]` maps the ring into `Π` and preserves it, and `δⁿ/n!`
  is its unique iterative integral Hasse–Schmidt extension, with no strongness,
  `R`-linearity or common-shift hypothesis; the class is all of `Der(Oz)`, strictly larger
  than the Euler family (it contains the non-`R`-linear `ω d_*`, Example 71.2). What remains
  is a structural description of all derivations (Question 75.1) and evaluation inside `No`
  (Question 59.6). Question 19.3 (reduced parameter rings) is asked again by 16 (batch 32),
  whose domain proofs do not reach it, and refined by 19 (batch 33); open. Question 19.1
  (groups with an order unit) is addressed by neither.
- **The lower bound after Corollary 17.9** ("only a lower bound is asserted for the field
  generated by the formal images of all Hahn series") is **answered for `D_0`** by
  source 17 (Theorems 53.1, 53.2): the full image is linearly disjoint from `No(s)` over
  `ker D_0`, with no set-sized transcendence basis. For every Euler flow the image descends
  to `F/F^{D_χ}` (Corollary 58.7); the size for other characters is open (Questions 59.1,
  59.2). The monomial statements of Theorem 17.5 and Corollary 17.9 stand.
- **Questions 59.1–59.10** (Part VII, 17): other exponent characters (59.1); set-sized
  Hahn fields (59.2); the algebraic core by supports (59.3); several commuting Euler
  directions (59.4); formal clocks with algebraic trajectories (59.5); **internal
  evaluation of formal flows** (59.6, merged from 17's and 19's questions); a proper-class
  differential Galois object (59.7); arithmetic restrictions on witnesses (59.8); finite
  certificates for relation descent (59.9); **formalization of Parts VII–X** (59.10,
  merged from 17's, 18's, 19's and 20's questions). All open.
- **Questions 66.1–66.8** (Part VIII, 18), new: which real closed fields are exact fixed
  fields (66.1); beyond the two-level family (66.2; **partly answered** in batch 34 by 20's
  Theorem 77.5, which realizes the proper-class `E = NF(No∖𝖩)` for every left-orderable set
  group); conjugacy of free-complement actions (66.3, with 20's Question 3 merged); centralizers
  and normalizers (66.4); birthday-controlled realization (66.5, related to 32.16); arithmetic
  invariant-fraction fields (66.6); surcomplex actions without a named conjugation (66.7,
  related to 32.1, with 20's Question 5 merged); fixed fields with orbit types (66.8). 18's
  question on additional transcendental structure is merged into 32.15, its formalization
  question into 59.10. Question 11.3 (full relative fixed fields in `U_Oz`) is **not
  addressed**: 18's automorphisms lie in the monomial factor (note after it).
- **Questions 75.1–75.7** (Part IX, 19), new: a structural description of all
  derivations (75.1, what remains of 19.2); orbit-field transcendence (75.2, **answered for
  `D_0`** by Part VII, open otherwise); structure admitting a definable residue section
  (75.3); several formal parameters and the jet Lie algebra (75.4); centralizers and formal
  conjugacy (75.5); fixed exponent groups and bounded parameters (75.6); coefficient
  intersections in other completions (75.7). 19's other four are merged into 59.6 (Hahn
  evaluation), 52.2 (definitional complexity, now tagged 16, 19), 19.3 (reduced parameter
  spaces) and 59.10 (formalization).
- **Questions 82.2–82.9** (Part X, 20), new: fixed sets beyond two-level complements (82.2;
  **partly settled** by Part VIII for every set and by Theorem 77.5 for complements of bounded
  open intervals; status after it); full automorphism-group realization (82.3); higher-order
  variable coefficients (82.4); matrix difference equations (82.5); relative first-order
  equations with coefficients in the relative fixed field (82.6); centerless groups and higher
  cocycles (82.7); small workspaces and birthday bounds (82.8, related to 66.5 and 32.16);
  effective Green operators (82.9). 20's other four are merged into 32.15, 66.3, 66.7 and 59.10.
  None of this report's or the single-dilation and surcomplex reports' named questions is
  answered by 20.

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
- **`odg:def:q:coeffpe`** (lower-complexity recovery of `R` or `C` from the
  integer-part ring): **not answered** by 16 (batch 32). Its quartic formulas
  recover `R` inside `R[U^M]` and `F` inside `F(U^G)`; with trivial parameters the
  ring formula is vacuous, and neither defines `Oz` or `R` inside `No`.
- **The congruence topologies** of `odg:eq:profinite` and of the paragraph after
  `osq:thm:completions`, and their Lean formalization: **explained**, not changed
  (batch 32). They are pullbacks along `ct`, hence Hahn-compatible, and by
  Theorem 39.7 every Hahn-compatible ring topology on `Oz` is such a pullback, so
  their failure to be Hausdorff is forced (Remark 39.6). The other reports are not
  edited by this merge.

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
  delivered audits are listed above ("Fifteen sources, one report").
- **Checked true:**
  - "the catalogue lists 51 reports", at the pins;
  - the antecedents in `saut` and `odg` that the sources name;
  - no report contained an `Oz`-automorphism classification.
- **15's statements (batch 32).** 15 first answered Question 11.1 itself, then
  found 12 and 13 and credited them, claiming only the topology; that claim holds
  at the merge (no report classifies Hahn-compatible ring topologies; the collection
  had particular topologies only). Its two article blobs and three audit blobs are
  as it says. Its reading of this report was incomplete (no Part IV, no congruence
  topologies); that is recorded, not corrected, since it asserts nothing false. No
  mathematical error was found in 15.
- **16's statements (batch 32).** Its pin, tree, description of source 02, build
  hashes and statement that 02's reducible-parameter question is open are
  accurate. No mathematical error was found in 16; its general criterion rests on
  Lin–Wang's unrefereed preprint, which was not rechecked.
- **Status notes (batch 32).** Questions 11.4, 19.3, 32.1, 32.11, 32.12, 32.18 and
  37.1 carry batch-32 notes; Question 32.11's first clause is marked answered.
  Pointers were added after Theorem 15.5 and in Remark 34.4. No label, number or
  earlier sentence was removed.
- **Cross-report notes (batch 32).** Unnumbered notes record the batch-32
  additions of three neighbouring reports: the surcomplex automorphism report's
  finite-symmetry sections (after Corollary 30.5 and Questions 32.1 and 32.13),
  the first-`κ` coefficient report (after Proposition 31.1 and Question 32.12) and
  the large-cardinal report's first-failure theorems (after Remark 23.3 and
  Questions 32.2 and 32.3). Question 32.3 is marked negative under a measurable
  cardinal; the others stay open. No label or number changed.
- **Status notes (batch 33).** Question 19.2 is answered by 19: the status after the
  question, the item in Section 19 ("… are not covered") and the sentence in Section 52.2
  ("… stay as they were") carry batch-33 notes. The lower bound after Corollary 17.9 and
  02's sixth non-claim carry notes that 17 answers it for `D_0`. Questions 11.3, 19.3,
  32.15 and 52.2 and Theorem 7.6 carry notes or pointers from 17–19. No label, number or
  earlier sentence was removed; the non-claims of 02 and 18 are kept as source records with
  a status note (Appendix B).
- **17's, 18's and 19's statements (batch 33).** Their pins and their accounts of this report
  are accurate at their pins (17 and 18: eight-source text; 19: nine-source text); the
  catalogue listed 61 reports at both pins; "left-orderable" occurs in no other report of the
  collection; 17's build-record hashes match. 19's quartic formula was new at its pin and is
  16's at the merge (printed once, Corollary 72.2). No mathematical error was found in 17, 18
  or 19.
- **20's statements (batch 34).** Its pin `e93a06d`, its reading of five guides and its
  credits (the lifts to Kaplan–Krapp–Serra's Construction 3.7 and Proposition 3.9, rechecked
  against arXiv v3; the centralizer to `saut:thm:axis`) are accurate. Its contribution
  statement (universality, exact fixed fields and difference solvability as a new package) is
  **stale** at the merge for universality and fixed fields, which are Part VIII's, and was
  **incomplete at its own pin** for the difference core, which the single-dilation report
  already contained (`dsup:thm:resolvent`, `dsup:cor:poly`, `dsup:thm:multsingle`,
  `dsup:cor:simultaneous`, `dsup:thm:dilationcohom`, `dsup:thm:surreal`). Both are credited and
  only the material listed in Section 76.2 is printed as new. Its finite-subgroup clause is
  weaker than `saut:thm:torsion`. No mathematical error was found in 20; every proof and worked
  example was rechecked.
- **Status notes (batch 34).** Question 66.2 is marked partly answered; Question 11.3 carries a
  note that 20's relative actions do not bear on it; Questions 32.15, 66.3, 66.7 and 59.10 gain
  20's merged questions (their source tags now include 20). No label, number or earlier
  sentence was removed.

## Relation to the neighbouring reports

- [`omnific-diophantine-geometry`](../omnific-diophantine-geometry/) (`odg:`).
  - Its reconstruction section (`odg:def:`) is the source of everything that
    this report cites about what `Oz` remembers.
  - This report adds the automorphisms and the nondefinability, and records
    negative information for `odg:def:q:realform`.
  - Its global monomial clearing `odg:thm:fractions` and `⋂ nOz = Π`
    (`odg:eq:divkernel`) are the inputs that sources 17, 18 and 19 reprove; they are cited
    in Parts VII–IX. The ideal identity is what makes every derivation of `Oz` integrate
    (Theorem 67.1).
- [`set-sized-quotients-of-omnific-integers`](../set-sized-quotients-of-omnific-integers/)
  (`osq:`).
  - Its `osq:q:invisible` is partly answered: the second clause by Corollary 24.4
    (from 12 and 13, and again from 14's factorization and automatic
    strongness), the first clause not. Since batch 31 the quotient report
    records this in its status of the question.
  - Its `osq:prop:classder` derivations are Part II's `D_b`; they are also 17's `D_0` and
    19's `D_η` (Parts VII and IX), whose fresh-direction choice (Lemma 73.1) shows that no
    set of parameters defines the coefficients in `Oz[[s]]`.
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
  - Its batch-32 finite-symmetry sections reprove Theorem 30.2 for valued
    automorphisms (`saut:fs:rem:gaussianstrong`), classify the valued
    `Oz[i]`-preserving involutions (`saut:fs:thm:main-involutions`) and give
    `2^𝔠` pairwise nonconjugate ones (`saut:fs:thm:large-family`); notes after
    Corollary 30.5 and Questions 32.1 and 32.13. Questions 32.1 and 32.13 stay
    open.
  - Part VIII (18) uses its centralizer decomposition `saut:thm:axis` (Lemma 65.2, with a
    ring clause for `Oz[i]`), its torsion theorem `saut:thm:torsion` (every nonidentity
    automorphism of `Oz` has infinite order, Corollary 63.2) and its phase twists
    `saut:thm:phase` (18's twist is `P_{−2π}`, Proposition 65.5); 18's conjugation-compatible
    group classification (Theorem 60.4) is new relative to it. Part X (20) credits
    `saut:thm:axis` too; its clause that finite subgroups are trivial or `C_2` is weaker than
    `saut:thm:torsion` (Section 81.1).
- [`exponential-automorphism-rigidity`](../exponential-automorphism-rigidity/).
  Every exponential 1-automorphism of `No` is the identity, so the shears are
  not exponential.
- [`single-dilation-hahn-support`](../../surcomplex/single-dilation-hahn-support/)
  (`dsup:`). The dilation `S_2` defines the monomials, and `(No, Oz)` does
  not. Batch 34: Part X's difference theory re-derives its resolvent, fixed fields,
  polynomial operators, multiplicative obstruction and commuting systems
  (`dsup:thm:resolvent`, `dsup:cor:fixed`, `dsup:cor:poly`, `dsup:thm:multsingle`,
  `dsup:cor:simultaneous`) for `Oz`-preserving double lifts of the class `No`; the formulas
  agree with the chambers swapped (Remark 78.6). Part X's first-order criterion, cocycles of
  groups with a central element, free groups, the operator field and the inner difference
  lemma are not there. Its `S_q` is a dilation, not 20's `S_s`.
- [`autonomous-dilation-relations`](../../surcomplex/autonomous-dilation-relations/)
  (`adr:`; batch 34). Its remark that `(No(i), S_d)` is not existentially difference closed
  (`S_d x − x = 1` is unsolvable; after `adr:sr:cor:free`) is the same observation as Part X's
  for `σ` (after Theorem 80.1).
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
  batch 31). Its copies lie inside `No`, whereas Part VII's Taylor embeddings land in an
  external formal Laurent field; neither construction substitutes for the other (17).
  Its monomial lifts are the maps `J_{h,id}` of Theorem 26.3.
  `isc:cor:parameters` extends the fixing clause of Theorem 29.6 to an
  `On`-indexed family whose pairwise intersection is exactly the full Hahn
  field `R((t^H))` on the rational span `H` of the supports of `A`, jointly
  linearly disjoint over it (note after Theorem 29.6; for its explicit `H = 0`
  copies Theorem 28.3(ii) gives closed, uniformly discrete images, a `[merge]`
  observation). `isc:thm:boolean` settles image inclusion and intersection
  inside one independent family with `ρ = id` (status note after Question
  32.17); its second research question is the pair version of Question 32.8
  (note after that question). Both questions stay open in general.
  Its batch-35 Hahn-join part counts `2^{2^κ}` non-strong automorphisms of a
  complex full Hahn join fixing the compositum of its two factor fields
  (`isc:hj:thm:automorphisms`), and `isc:hj:rem:omnificaut` combines
  Corollary 23.4 with its strong rigidity: none but the identity both
  commutes with conjugation and stabilizes the Gaussian omnific ring of the
  join (note after Remark 23.3, following the batch-32 one).
- [`large-cardinal-embeddings-and-normal-forms`](../../foundations-and-computation/large-cardinal-embeddings-and-normal-forms/)
  (batch 30, written concurrently; cited by directory only until batch 32, then
  by its `lce:mf:` labels). Under a measurable
  cardinal its sign-sequence embedding answers Question 32.2 negatively; it is not
  an automorphism, so Theorem 23.2 stands. Under the same hypothesis it shows that
  14's embedding question (merged into 32.2–32.3) needs hypotheses beyond
  constant-term compatibility and preservation and reflection of `Oz`. Its
  batch-32 first-failure theorems (`lce:mf:thm:spectrum`,
  `lce:mf:thm:equivalence`, `lce:mf:thm:target`) are recorded after Remark 23.3
  and Questions 32.2 and 32.3.
- [`first-kappa-coefficients`](../../surcomplex/first-kappa-coefficients/)
  (`fkc:`; batch 32). Its `fkc:sb:thm:sums` shows that Proposition 31.1's
  summability characterization fails for singular `κ` (note after Proposition
  31.1); it bears on Question 32.12 without answering it.
- [`foundations`](../../foundations-and-computation/foundations/) (`found:`).
  Its `found:sub:tsum` (with `found:ex:geometric`, `found:ex:archimedean` and the
  rank-one `found:ex:boundedrankone`) shows that strong summation is not
  topological summation for particular valuation topologies; Theorem 39.12 is the
  general form for full Hahn fields: outside `Γ ∈ {0, Z}` no Hausdorff ring topology
  realizes all Hahn sums (Remark 39.13).
- The Diophantine and quotient reports' congruence and `p`-adic topologies on `Oz`
  (`odg:eq:profinite`; the paragraph after `osq:thm:completions`), formalized in
  `Surreal/Foundations/OmnificCongruenceTopology.lean` and
  `OmnificSeparationTopology.lean`, are instances of Theorem 39.4 (Remark 39.6).

## What was run

For the merges all fifteen suites were rerun on copies, with Python 3.14.4 and
SymPy 1.14.0 (10's for the batch-28 addition, 11's, 12's and 13's for the
batch-30 addition, 14's for the batch-31 addition, 15's and 16's for the batch-32
additions, 17's, 18's and 19's for the batch-33 additions, 20's for the batch-34 addition).
Each reproduced its recorded result:

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
| 15 | 27,139 assertions in 14 categories (pairing 700, coefficient extraction 1,431, disjoint rows 3,800, sparse detector interpolation 4,000, cancellation boundary 198, monomial transport 1,050, rank-two Vandermonde 3,000 and inverse 3,000, order reflection 3,003, negative interval 3,081, fixed product 3,081, bounded increasing support 248, valuation non-escape 248, cyclic remainder 299), seed 20260923, `passed`; the written record is identical to the shipped one |
| 16 | 1,314 checks in 12 categories, seed 20260923, `PASS`; the written record differs from the shipped one only in `python` (3.14.4 against 3.13.5) and `elapsed_seconds` |
| 17 | 30,900 assertions in 24 groups (SymPy 1.14.0, about 22 s), `passed`; the record written with `--output` differs from the shipped one only in `python_version` (3.14.4 against 3.13.5), up to line endings |
| 18 | 11,330 assertions in 19 categories, seed 20260923, `PASS` (about 1 s); the record written with `--output` is identical to the shipped one up to line endings |
| 19 | 1,576 checks in 17 groups, seed 20260923, `passed` (about 2 s); the record written with `--output` is identical to the shipped one up to line endings |
| 20 | 5,555 assertions in 29 groups, seed 20260923, `PASS` (about 1 s); the record written with `--output` is identical to the shipped one up to line endings |

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
directory; the auxiliary files are not kept here. The batch-35 note after
Remark 23.3 took the build from 220 to 221 pages and changed no number (all
729 labels and 27 citation numbers compared in the `.aux` files against a
build of the committed text).

Fourteen of the shipped scripts can write files (thirteen check scripts and 16's build
script; 19's `build.sh` creates two empty directories before failing, and 17's and 20's
Makefiles would rebuild this report in place), so rerun the checks on a copy, outside
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
python 15-topological-collapse-verify.py --output rerun-15.json    # standard library
python 16-coefficient-recovery-verify.py --output rerun-16.json    # standard library
python 17-formal-orbit-fields-verify.py --output rerun-17.json     # needs sympy==1.14.0; about 22 s
python 18-exact-symmetries-verify.py --output rerun-18.json        # standard library
python 19-formal-symmetry-verify.py --output rerun-19.json         # --output is required, see below
python 20-universal-symmetries-verify.py --output rerun-20.json    # standard library
```

Do not run `16-coefficient-recovery-build.py`: it is 16's delivered build script and
expects `verify.py` and `article.tex` beside it.

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
- 15's and 16's scripts print their reports and write `verification.json` next to
  themselves unless `--output` is given; run in place they would create
  `code/verification.json`, not touching the prefixed records.
- 16's `build.py` creates `build_logs/` next to itself and then runs `verify.py`
  and `pdflatex article.tex` three times in its own directory, rewriting
  `article.pdf` and `verification.json` there; in this report those delivered names
  are absent, so run in place it would create `code/build_logs/` and stop.
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
- 17's script writes `--output`, by default `verification.json` in the **current working
  directory**, and prints its report.
- 18's script writes `verification.json` next to itself unless `--output` is given; run in
  place it would create `code/verification.json`.
- 19's script writes `../data/verification.json`, relative to its own directory, unless
  `--output` is given; run in place it would create an unprefixed `data/verification.json`
  here (not overwriting `data/19-formal-symmetry-verification.json`), and run from the flat
  copy above without `--output` it would write into the parent of `$D`. Always pass
  `--output`.
- 20's script writes `verification.json` next to itself unless `--output` is given; run in
  place it would create `code/verification.json`, not touching the prefixed record.
- The shipped records of 17, 18, 19 and 20 have LF line endings; the files these scripts write
  on Windows have CRLF line endings.

The nine Makefiles of 09, 02, 10, 11, 12, 15, 17, 18 and 20 and the build scripts
`04-preserving-automorphisms-build.sh`, `13-omnific-isomorphisms-build.sh`,
`16-coefficient-recovery-build.py`, `18-exact-symmetries-build.sh` and
`19-formal-symmetry-build.sh` are shipped as delivered. They name the manuscripts' own
files (`omnific_automorphisms.tex`, `surreal_embeddings.tex`,
`Surreal_Arithmetic_Topological_Collapse.tex`, `article.tex`, `verify.py`, `build.sh`,
`verify_finite_identities.py`, `verify_finite_models.py`, `code/verify.py`), which
are not present here under those names, so they do not run as-is. Do not run them here:
17's and 20's Makefiles would run `latexmk` on this report's `article.tex` in place
(and 20's `clean` target runs `latexmk -c` on it); 18's `build.sh`
stops at its first step, and the `clean` target of its Makefile deletes `article.*`
auxiliary files in the working directory; 19's `build.sh` creates `code/build/` and
`code/data/` and then fails on the absent `code/code/verify.py`. The `clean` targets of
`10-support-cut-Makefile` and `12-automatic-strongness-Makefile` delete
auxiliary files named `article.*` in the working directory; do not use them
here. 13's `build.sh` expects its delivered layout (`code/verify.py` and
`article.tex` beside the script) and stops at its first step here; in its
delivered layout it runs the checks with the default output path above.
