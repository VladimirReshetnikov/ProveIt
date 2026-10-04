# Scoped review of batch 89 placement and the naming follow-up

The byte placement is reproducible, but the first commit does not contain four of the manuscript integrations advertised in its subject. A later commit completes the naming report and repairs its replay documentation; it still refers to the other planned parts as though they were present. These are publication and relocation findings, not mathematical refutations.

No finite paid ordinary-input Diophantine compiler was found in the reviewed material. The results concern countable products, ordinal or class coding, model-theoretic schemes, and internal embeddings into surreal structures. They supply no new fixed-arity integer polynomial, complete arithmetic source, positive-witness theorem, or operation bound.

## 1. Immutable scope and method

The initial review is exactly the direct-parent diff

```
8311efdd4fce0ca3a9ccb16344f2a16821888a78
  -> 23adb85f97b86687c604db936333025a8d6abe32
```

It contains 21 added files and five deleted ZIPs, with no modified files. The added files total 149,040 bytes. All 21 are byte-identical to members of the five ZIPs as stored in the parent commit. Those archives contain 36 members in total, all inventoried and hashed without executing their contents.

The separately scoped follow-up is

```
e9dc168f10cf2893775f84c28104155df66ff143
  -> aa9a7ec80d12e52bfe7fe3362893462537e3cbfe
```

Only its three naming-report changes are covered: README.md, article.tex and the newly added article.pdf. Intervening arithmetic, ant and reciprocal-note changes are outside this review.

I read the complete applicable `Algebra/SurrealNumbers/AGENTS.md` (Git blob `78367178df40750c18c189f5076726ee0a4dea7a`). In particular, research-report claims are not treated as formalized declarations; weak object-theory assumptions remain separate from host-level axioms. No source, archive script, build, historical verifier or proof-assistant process was executed. Fresh read-only Git/ZIP/hash/diff calculations were used. No repository or frozen artifact was modified.

## 2. Findings at the placement commit

### F1. The advertised integrations are absent from the committed diff

The subject of `23adb85f9` advertises global choice as Part XV of `surreal-well-orders`, Presburger embeddings as Part X of `polish-models-of-omnific-arithmetic`, and cuts/choiceless universality as Parts VI–VII of `birthday-cutoffs-and-hereditary-sets`. Its body explicitly says the four manuscripts and their READMEs were “not staged”. The actual tree agrees with that limitation, rather than with the broader subject:

| Existing report, under `Algebra/SurrealNumbers/docs/foundations-and-computation/` | Last numbered part actually present | Advertised namespace absent from both article and README |
|---|---:|---|
| `surreal-well-orders` | XIV, article line 40555; followed by unnumbered questions at 48599 | `swo:gcz:` |
| `polish-models-of-omnific-arithmetic` | IX, article line 18815 | `pma:emb:` |
| `birthday-cutoffs-and-hereditary-sets` | V, article line 3634 | `hset:zr:`, `hset:kw:` |

Each report's article.tex and README.md is byte-identical to its parent version. This is not a claim that none of the mathematical ideas occurred earlier: the new packages themselves identify overlap with existing results. It means the claimed new manuscript parts are not published by this commit. Their archived source remains recoverable through the immutable parent Git objects. They must not be described as reviewed published Parts XV/X/VI–VII on the strength of this placement.

The naming report is different: its original 1,041-line article is actually added under `SetTheory/Cardinals/docs/reports/ordinals-and-order-types/naming-elementary-embeddings/`. Its delivered README is also added, but its PDF is not yet present at this initial commit.

### F2. Relocated scripts retain their original flat-layout assumptions

At `23adb85f9`, the naming README lines 54 and 59 instruct `bash build.sh` and `python3 verify_finite.py --output verification_results.json` in the report directory. Both scripts are instead under `code/`. Even explicitly invoking `code/build.sh` would not resolve the article: line 4 changes into the script's directory, and line 13 passes `article.tex` there, whereas the source is one directory above. The README also describes article.pdf at line 12 although that file is absent at this revision.

Two other placed scripts have the same kind of relocation boundary:

* `polish-models-of-omnific-arithmetic/code/16-presburger-embeddings-build.sh`, lines 3–7, changes into `code/`, then expects unprefixed `verify_examples.py` and `glazer_presburger_embeddings.tex` there. Neither is at those committed paths.
* `birthday-cutoffs-and-hereditary-sets/code/10-cuts-replacement-build.sh`, lines 3 and 6–8, changes into `code/`, then expects `code/verify_finite.py` below that directory and `article.tex` beside itself. Those are the original archive-relative paths, not the placed layout.

These conclusions follow from literal paths; no script was run. The bytes themselves are authentic. Rebuilding the original packages requires restoring their original layout or documenting a suitable scratch-copy procedure. This review does not authorize editing those preserved source bytes.

## 3. The later naming write repairs part of the publication state

At `aa9a7ec80`, the naming README is 346 lines and article.tex is 1,112 lines. The PDF is added, 458,247 bytes. The new README accurately identifies which build-audit hashes describe delivered rather than rewritten files.

The README now explicitly documents the relocation limitation at lines 272–288. It gives the actual checker path at lines 299–303 and two scratch-copy PDF build recipes at lines 320–326. The second recipe puts article.tex and code/build.sh beside one another before invoking the unchanged script. These instructions resolve the earlier naming documentation defect without claiming that the raw script works in place. Their paths were inspected; the commands were not executed here.

The article adds the corresponding layout note at lines 1062–1065. After removing the new `nee:` prefixes, the full original 1,041 lines occur unchanged and in order: the only remaining diff operations are nine insertions totaling 71 lines, at new lines 94–98, 101, 121–122, 124, 191–236, 767–770, 883–886, 982–985 and 1062–1065. Thus the delivered theorem/proof text is retained, with added provenance, notation, overlap, status and replay notes. The label count changes from 64 to 66, as claimed. This checks source preservation, not PDF numbering or a new theorem certification.

**Remaining placement mismatch.** The follow-up README lines 165–188 and 199–201, and article lines 196, 204, 206 and 983, describe the other batch-89 additions as existing Parts VI/VII/X/XV. All six existing article/README blobs in F1 are still unchanged at `aa9a7ec80`. These cross-references are ahead of the committed publication state. The archive-level mathematical comparisons may be read as comparisons with the delivered manuscripts, but cannot yet be read as links to the claimed published parts.

## 4. Mathematical scope and finite-compiler relevance

This section reports the manuscripts' claims and the boundaries visible in the passages read. It is not an external-literature audit or a full independent correctness certificate.

**01, global choice and surreal coding.** The proposed refinement uses a countable-set selector plus Separation in the expanded language to derive nonconservativity over Zermelo set theory with Choice. The exact Glazer countermodel interface is stated in source lines 526–546 and used at 550–589; it is inherited, not reconstructed. I have not independently verified that published countermodels provide this exact abstract interface. The rank-model results concern `(V_lambda,P(V_lambda))` in an external ZFC metatheory and separate selection, ordinal coding and class-image bounds. No finite existential arithmetic encoding is supplied. The absence of a numerical test here is correctly explained at lines 1255–1263.

**02, Presburger embeddings.** The domain is `M_alpha=(Q^alpha lex Z)_{>=0}` for countable ordinals alpha, with full rational products and the discrete-factor product topology. The main theorem concerns elementary maps, row-finite matrices, closed coefficient subspaces and the distinct omega/omega*2 thresholds. Multiplication is absent from the Presburger language (lines 134–140); the omnific realization is additive and ordered and explicitly does not assert ring closure (1310–1313). Finite matrix checks cannot verify wild functionals or the infinite topology (1262–1273). This is not an ordinary-input Diophantine compiler and does not resolve the separate ATR0 question (153–157).

**03, cuts and Replacement.** The important restriction survives the README, proof-status note and theorem statements: actual set cuts require no Replacement, while definable-family interpolation characterizes ordinal bounding over the stated Zermelo base. Full Replacement/Collection equivalence is asserted only after adding the separately stated hierarchy axiom H (193–205, 414–438). The atom-support models use an external choice-satisfying universe; pure-valued Collection can survive even when expanded-language Replacement fails. These are set-existence schemes, not finite integer witness bounds.

**04, choiceless universality.** “Polynomial universality” here means embedding arbitrary-variable free rings/fields into omnific/surreal targets. The double-monomial evaluation uses finite normal-form independence, but its values are surreal objects; it is not a polynomial equation over ordinary natural inputs and finitely many integer witnesses. The positive theorems are scoped to ZF with their stated surreal interface. The negative example is internal to a specified ZFA permutation model, and no transfer to pure ZF is claimed (666–668). Separate finite-stage embeddings do not give a coherent global map (670–695). None of these results supplies a paid universal arithmetic circuit.

**05, naming elementary embeddings.** I read the entire delivered article. Its principal criterion concerns the union of small component-type blocks of finitely many named atom injections, with a separate finite-cutoff condition. The one-name/two-name cofinality thresholds and the CH equivalence are restricted to this explicit kernel-model family, with ambient Choice. “Finitely many names” counts language symbols, not Diophantine witnesses. The full Collection/reflection criterion is kept distinct from Replacement, and the partial-reflection discussion explicitly warns against importing Collection through quantifier normalization. No internal truth predicate or proof-assistant certification is claimed. No immediate scope contradiction was found in this read; inherited set-theoretic literature and all infinite-cardinal claims have not been independently re-proved here.

The follow-up accurately retains these mathematical boundaries and gives a proposed expanded-language formalization route. Its reproduction of the earlier Hilbert's-tenth routing at README lines 150–163 is consistent with that limited purpose. Nothing reviewed changes the existing finite paid universal polynomial frontier.

## 5. Exact read scope

Line numbers below refer to the original archived members, before label prefixing, unless a follow-up revision is explicitly named. Complete archive inventories and whole-file hashes do not imply that every manuscript proof or program was read.

| Archive/member | Lines actually read |
|---|---|
| 01 `global_choice_surreal_coding/README.txt` | all 1–59 |
| 01 `global_choice_surreal_coding/global_choice_surreal_coding.tex` | 74–226, 524–646, 1199–1264, 1437–1491 |
| 02 `glazer_presburger_embeddings/README.md` | all 1–81 |
| 02 `glazer_presburger_embeddings/SOURCE_AUDIT.md` and `PROOF_REVIEW.md` | all 1–100 and 1–62 |
| 02 `glazer_presburger_embeddings/glazer_presburger_embeddings.tex` | 94–261, 1197–1363, 1545–1588 |
| 03 `Surreal_Cuts_Replacement_Atom_Support_Spectra/README.md` and `PROOF_STATUS.md` | all 1–54 and 1–58 |
| 03 `Surreal_Cuts_Replacement_Atom_Support_Spectra/article.tex` | 92–211, 352–439, 680–774, 858–907 |
| 04 `Glazer_Surreal_Choice/README.md` and `SOURCES_AND_STATUS.md` | all 1–72 and 1–77 |
| 04 `Glazer_Surreal_Choice/article.tex` | 84–174, 240–329, 645–766, 835–881 |
| 05 `Naming_Elementary_Embeddings/README.md` and `SOURCE_AUDIT.md` | all 1–63 and 1–79 |
| 05 `Naming_Elementary_Embeddings/article.tex` | all 1–1041 |

Also read in full: the three added build scripts (10, 18 and 24 lines), all seven added JSON build/verification records, both commit messages, and the applicable AGENTS.md. The section and standard theorem-environment headings in all five manuscripts were scanned. The four Python verifiers were inventoried and hashed, not executed or independently audited.

For `aa9a7ec80`, the complete 346-line naming README and every added article span listed in Section 3 were read. The complete article was compared mechanically with its already-read predecessor after removing label prefixes. Its new PDF was hashed, not rendered, and the claimed build/test runs were not replayed. The other existing reports were checked by exact blob equality and part/namespace scans; their tens of thousands of unchanged lines were not newly read in full.

## 6. Provenance and byte mappings

All archive bytes below are from `8311efdd4fce0ca3a9ccb16344f2a16821888a78:docs/incoming/NAME`. They are recoverable by read-only `git show` even after deletion. Exact SHA256s identify the archive contents independently of later placement.

| No. / archive | Git blob | SHA256 | Members |
|---|---|---|---:|
| 01 `global_choice_surreal_coding.zip` | `9ace436cfa67751e75475ab7b558b472c129f041` | `6246d8b88b5965c3c3a30bcf4d19aa5f179a65e96854aae76666c935a6d87227` | 3 |
| 02 `Glazer_ProveIt_Embeddings_and_Thresholds.zip` | `ff6250559eabf81e636e109549d509b7a5ccae5b` | `1aa1de81477be1aa90b57eb67d4bb3cb391c035914be79b1937fd5f0252824ec` | 9 |
| 03 `Surreal_Cuts_Replacement_Atom_Support_Spectra.zip` | `7d4e718dd8986031b781fb28b165412da4c70c18` | `bada37bda97f5cff56ec26c9752d1fc24c3335df341f339d6ec24f0f166014a0` | 9 |
| 04 `Glazer_Surreal_Choice_Research.zip` | `01520f0a8353add81a82f56e63f7cdb680f3cf60` | `b509752f93fb1e803c9e6a162aded91cfd2a720e1004ae12089d002f966d3442` | 7 |
| 05 `Naming_Elementary_Embeddings_Research.zip` | `44922a7ccc63ace6b52582e2b98c9fcc5a3fcd5e` | `263144bff673039c9f82273afa72a6bc67862786049535c34f7997a305a567fa` | 8 |

Every added file has exactly one matching archive member. The destination mappings are:

* Archive 01: no member added to the publication tree.
* Archive 02: `build.sh` and `verify_examples.py` go under the Presburger report’s `code/` with prefix `16-presburger-embeddings-`; `BUILD_REPORT.json` and `verification_results.json` go under `data/` with that prefix; `SOURCE_AUDIT.md` and `PROOF_REVIEW.md` go beside the article with that prefix. Six matches.
* Archive 03: `build.sh` and `code/verify_finite.py` go under the birthday-cutoffs report’s `code/` with prefix `10-cuts-replacement-`; the two `data/` records retain that directory with the same prefix; `PROOF_STATUS.md` goes beside the article with that prefix. Five matches.
* Archive 04: `verify_finite.py`, `verification_results.json` and `SOURCES_AND_STATUS.md` go under `code/`, `data/` and the birthday-cutoffs report root respectively, with prefix `11-choiceless-universality-`. Three matches.
* Archive 05: article.tex, README.md and SOURCE_AUDIT.md go to the naming report root; build.sh and verify_finite.py to `code/`; BUILD_AUDIT.json and verification_results.json to `data/`. Seven matches.

These are exact byte matches, with no text normalization. Original archive PDFs and checksum manifests were inventoried, not rebuilt. The later naming README/article/PDF are a separately authenticated write, not claimed byte-identical to delivery.

The six unchanged target blobs are the same at the baseline, placement and naming follow-up:

| Report / file | Git blob | SHA256 |
|---|---|---|
| `surreal-well-orders/article.tex` | `05807d292fbed8b68aa5744b502fece703057c74` | `260ccd127bc14f9b7784d0f7c9ac3a8e2ebdafff75f0993d181070b34248b3e0` |
| `surreal-well-orders/README.md` | `df07b2c04f6ff183c7f10ecc8527271afafc0ae1` | `59e7b942f57f27b2e4b21e12557a5638ce1f4bedca1379d2c7350d1edabed540` |
| `polish-models-of-omnific-arithmetic/article.tex` | `13e011ff7a290ac655f948d32ea258c19b2cca81` | `f311e9063087ab93cd95915f455e242c5e55c790c1de321826178553b089bc05` |
| `polish-models-of-omnific-arithmetic/README.md` | `3c4153b2f7e29741b71a83be79eed232366367df` | `bd563be861542e62008126aea900aa1da26850c26ddf1173f40859031e387797` |
| `birthday-cutoffs-and-hereditary-sets/article.tex` | `79052bdf8642c562844b080a0d9b7ca943037e30` | `fe32f68de19e04a55121cd0be83fdd3c25c90c556220c7d5ce47ba5b7bd02571` |
| `birthday-cutoffs-and-hereditary-sets/README.md` | `c3faa2b151cb26ea01609af4b3d75352b75fd20d` | `8cf2547546d0e9a3dd5e494d41f4a1ef0cf5c60f1c0cfdd14bba715de6662640` |

The original five manuscript SHA256s are:

| Archive | Member basename | SHA256 |
|---|---|---|
| 01 | `global_choice_surreal_coding.tex` | `773f23e85a85891c2ef5e4bf60eb9019abd8df274dfb27a0abb847822046fc75` |
| 02 | `glazer_presburger_embeddings.tex` | `d84f2ed25648e1481924d1f7b3f1ec9baa1be730ecdebed1e709fd7d08d62507` |
| 03 | `article.tex` | `68397d93a0b692f6c575ccd305ab88ec1e6644bcbfabb3aceb95c983a47ba862` |
| 04 | `article.tex` | `17cf8b4115ccd965564838df306b06314dbee7618f6d31da9142ef5d984fdb34` |
| 05 | `article.tex` | `3c85457c7e6f903443ea21dce2bffd6ad3bb3b1cf2eb41f51356f2bc4289e870` |

At `aa9a7ec80d12e52bfe7fe3362893462537e3cbfe`, the naming write has:

| File | SHA256 |
|---|---|
| `README.md` | `fb5528ffd07286f7feaca68c06d37377d036fa75b066bf3e57d46e83bf600435` |
| `article.tex` | `e46976cbe04c1fd39a90b942ba54f8565f0b83cfa5edacfc4ba5ca1d739db965` |
| `article.pdf` | `45b31272af480e3883edb24ff5c652c48085d13ac17741bcf72bca48303d3557` |

No later commit is silently substituted for either reviewed revision. Findings F1/F2 remain historical facts about the initial placement; Section 3 records exactly which naming issues the follow-up addresses.
