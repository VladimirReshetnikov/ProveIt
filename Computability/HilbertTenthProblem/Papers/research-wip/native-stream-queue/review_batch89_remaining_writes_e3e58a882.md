# Scoped review of the remaining batch-89 topology writes

This is a bounded publication and hypothesis review, frozen to the revisions below. The previously missing global-choice Part XV and cuts/choiceless Parts VI–VII are now present. The main statements read retain their important logical boundaries. There are two small delivered-label-count errors in the birthday-cutoffs article and one compressed README hypothesis to read with the actual theorem. Presburger Part X remains absent at the checked merge. None of this supplies a finite ordinary-input Diophantine compiler or changes the current 84-operation universal bound.

## Revisions and scope

The two independent patch comparisons are:

- `aa9a7ec80d12e52bfe7fe3362893462537e3cbfe` → `193e2e942a7a8c22d091bda367b470ef23661c9e`: `surreal-well-orders/{README.md,article.tex,article.pdf}` only.
- `e3d731c6fd954a29b3e7eabb81aeacf25b5cca15` → `e3e58a8820593857650bb7a0193a11ec32db67d6`: `birthday-cutoffs-and-hereditary-sets/{README.md,article.tex,article.pdf}` only.

All six resulting files are byte-identical at merged revision `2efca7042cca95c3c39552b746a05fbfc696d49e`. Paths below are relative to `Algebra/SurrealNumbers/docs/foundations-and-computation/`, unless stated otherwise. Line numbers name the exact article revision in this table, not a mutable later file.

| File | Git blob | SHA-256 |
|---|---|---|
| `surreal-well-orders/README.md` | `455ff8928e760242db505fb56a87ed5cc3c55a91` | `66b706888df204353885a967846f07ef7ef9c074941c9ecc8eeb7cf77322ae56` |
| `surreal-well-orders/article.tex` | `d2efe7e91d6e3fa45ed15ac53a18c0f0b03866cc` | `d46df5384056413536d4f693232060a80a81d60b70c644436dc6acb6a0fcfcf7` |
| `surreal-well-orders/article.pdf` | `1030952ef1f93a7fd96288931e1e5723ab20ef32` | `d53b2e766bd3b9ff2545b3b0570f4f095588cc2711d7d8bb9ef7322ac6f12843` |
| `birthday-cutoffs-and-hereditary-sets/README.md` | `cef52ea4e979a11701d45ac9edea10b2e132a016` | `746aa779ff42d9c8bd93c3c2fb2902f6a7b1c1c78c3c385412f3867ac0aa41ed` |
| `birthday-cutoffs-and-hereditary-sets/article.tex` | `2c920efe07cdb50d7d20dd46ec933fade7b41f77` | `1f9e18e9351e73bdef2516812969fca5c3bf858ac8303d0aad9fae4ea0f3ec92` |
| `birthday-cutoffs-and-hereditary-sets/article.pdf` | `53c68d47bc84ef806021dacba98ed4c9b6851369` | `a2ba5755763aa32b9a44d28af6d91fcc78676cd4885acf803e4be21225da90fa` |

The PDFs were hashed only; their typesetting, page counts and compiled numbering were not independently checked. No archived or placed program, build script, predecessor helper, Lean or LaTeX build was executed. Repository files were not edited.

Read coverage:

- The complete applicable `Algebra/SurrealNumbers/AGENTS.md` and the complete installed prior note `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_batch89_topology_23adb85f9.md`.
- Both textual patch hunk inventories and all added README text, with surrounding context for the claim, scope, label and reproducibility passages.
- `surreal-well-orders/article.tex`: front-matter additions at 302–331 and 1354–1409; Part XV introduction and settings at 48944–49190; uniform-presentation theorem at 49260–49335; Glazer interface, main theorem and rank-model thresholds at 49424–49986; dependency ledger, source audit and conclusion at 50203–50387. Other additions were searched for headings and labels, not treated as fully read proofs.
- `birthday-cutoffs-and-hereditary-sets/article.tex`: front-matter additions at 181–204, 407–430 and 526–551; Part VI overview, hypotheses and notation at 4151–4435; set-cut/family/Replacement argument at 4500–4630; expanded-language and pure-valued boundary at 4820–4916; source-10 provenance at 5150–5169; Part VII introduction, interface and coding statements at 5198–5460; coordinate-universality and code-level target statements at 5512–5638; internal counterexample and coherence at 5870–5926; non-claims and provenance at 6094–6183.
- Fresh text-only label counts over the full old/new articles and the three original archive manuscripts. This is not an independent line-by-line preservation proof for every paragraph or a certification of the manuscripts' transfinite theorems.

The guidance file has Git blob `78367178df40750c18c189f5076726ee0a4dea7a` and SHA-256 `ecf44fe89f365a1b88d7d5e94e23bf3ab6a713d01a4ee8c44f72f234a4295039`. The prior review has blob `d5aa0dad5d066ba8a8a90eda81ee234752b2798e` and SHA-256 `e421519232d496a8ce4023f2fad9df28300157c8d9bdc89a2473cf78afbce1fc`. In accordance with that guidance, manuscript placement is not Lean formalization or an entry certifying the collection's proofs.

## Which earlier placement findings are resolved

The prior note's missing-text finding F1 is resolved for three sources:

| Source | Actual new destination | Exact label evidence |
|---|---|---|
| Global choice and surreal coding | Part XV begins at article line 48944 | 77 `swo:gcz:` labels; all 47 delivered labels occur once with that prefix |
| Cuts, Replacement and atom supports | Part VI begins at article line 4151 | 65 `hset:zr:` labels; all 42 delivered labels occur once with that prefix |
| Choiceless universality | Part VII begins at article line 5198 | 74 `hset:kw:` labels; all 52 delivered labels occur once with that prefix |

The surreal-well-orders article has 1,876 labels, up from 1,799; every old label survives, and no label is duplicated. The birthday-cutoffs article has 296, up from 156; every old label survives, no label is duplicated, and the additional existing-question label is `hset:q:axiomatics`. These counts support the READMEs' label inventories; they do not independently verify the claimed preservation of every compiled statement number.

The source-label comparisons read inert archive bytes at `8311efdd4fce0ca3a9ccb16344f2a16821888a78`, using `git show` and ZIP member reads only:

| Archive under `docs/incoming/` | Manuscript member | Member SHA-256 |
|---|---|---|
| `global_choice_surreal_coding.zip` | `global_choice_surreal_coding/global_choice_surreal_coding.tex` | `773f23e85a85891c2ef5e4bf60eb9019abd8df274dfb27a0abb847822046fc75` |
| `Surreal_Cuts_Replacement_Atom_Support_Spectra.zip` | `Surreal_Cuts_Replacement_Atom_Support_Spectra/article.tex` | `68397d93a0b692f6c575ccd305ab88ec1e6644bcbfabb3aceb95c983a47ba862` |
| `Glazer_Surreal_Choice_Research.zip` | `Glazer_Surreal_Choice/article.tex` | `17cf8b4115ccd965564838df306b06314dbee7618f6d31da9142ef5d984fdb34` |

Presburger is unchanged at the checked merge: `polish-models-of-omnific-arithmetic/article.tex` and its README are byte-identical to the prior baseline, and neither contains `pma:emb:`. Their respective SHA-256 values are `f311e9063087ab93cd95915f455e242c5e55c790c1de321826178553b089bc05` and `bd563be861542e62008126aea900aa1da26850c26ddf1173f40859031e387797`; their blobs remain `13e011ff7a290ac655f948d32ea258c19b2cca81` and `3c4153b2f7e29741b71a83be79eed232366367df`. Thus the requested Presburger Part X was not supplied by these writes.

The earlier source-10 build-layout issue is now explicitly documented in the birthday-cutoffs README, lines 509–529: the retained delivered script is not to be run in the placed layout, and source-specific replay is distinguished from the merged manuscript. This is a documentation resolution, not a repair or successful execution of that script. The prior naming follow-up remains a separate review; these two commits do not modify it.

## Hypotheses and interpretation of the new statements

**Part XV.** The actual uniform-presentation theorem `swo:gcz:thm:uniform` fixes well-orders on both `D` and its code set `C_D` and uses Separation in the relevant expanded language. Ordinary Choice supplies the code well-order in `ZC`. The countable-selector nonconservativity theorem `swo:gcz:thm:main` is explicitly stated over `ZC` or `ZC_F`, with a selector and `Sep(c)`. Its dependence on the exact interface to Glazer's countermodels remains unreviewed here; the integration flags that dependence in the abstract, front matter, Part introduction and theorem's preceding subsection. The rank-model results are in an external ZFC metatheory with **all** external subclasses admitted as classes. They concern the sign carrier, not a field at every cutoff, and full-class Replacement, not automatically the pure first-order schema or arbitrary definable-class models. The new text keeps these distinctions.

**Part VI.** `hset:zr:thm:equivalence` is over Zermelo with Foundation, without Replacement or Choice. Actual set cuts have a bounded-container simplicity proof. Definable set-indexed families are a different assertion: their six schemes characterize ordinal bounding. The upgrade to full Replacement and Collection in `hset:zr:thm:ranked` explicitly assumes the hierarchy axiom `Hier`, including coverage of every set. The atom-support results use an ambient full urelement universe with Choice. Naming an external enumeration changes the language to which Separation/Replacement/Collection apply. Pure-valued Collection surviving that expansion is not full ambient Collection. The new cross-report comparison explicitly says the older hereditary-universe theorem and the weak-base theorem do not contain one another.

**Part VII.** The positive results state ZF together with the identified classical surreal interface, including real closedness, monomials and finite normal-form independence. This review has not independently rebuilt that interface over choiceless foundations. `hset:kw:thm:equivalences` concerns coordinate and free-algebra embeddings, not arbitrary prescribed orders. Its optimal `U_kappa` theorem is a code-capacity statement for infinite initial ordinals; it does not assert an optimal birthday formula. The ordered-field counterexample `hset:kw:thm:orderedcounter` is internal to the stated ZFA permutation model. No pure-ZF transfer is supplied. `hset:kw:thm:coherence` requires a single set-coded compatible family, not just individual finite-stage embeddings. These boundaries are retained in both the statement passages and the new summary/non-claims.

In particular, “polynomial universality” here concerns free polynomial rings on possibly arbitrary sets of variables and surreal/omnific targets. It is not a finite integer polynomial representing a c.e. ordinary-input language. No paid arithmetic source, unbounded history certificate, or universal-operation reduction follows from this integration.

## Findings

1. **Two minor provenance counts are wrong in the article, but correct in its README.** At `e3e58a882`, birthday-cutoffs article line 5158 calls source 10's delivered manuscript “45 labels”; the exact archived manuscript has **42**. Line 6150 calls source 11's manuscript “64 labels”; it has **52**. The twelve question labels in the latter were added during integration, as the following paragraph itself says. Counts used the `\label` command with its optional type argument supported and TeX comments excluded; all original labels were matched to the integrated article. These are metadata errors, not missing labels or defects in the theorem statements.
2. **Read the short uniform-presentation summary with its parameters.** Surreal-well-orders README lines 657–660 says “Over Zermelo set theory” without repeating the fixed well-orders on `D` and `C_D` or expanded-language Separation. The cited theorem at article lines 49261–49272 explicitly requires them. The summary should not be promoted to a parameter-free assertion over bare Zermelo. No corresponding omission occurs in the main countable-selector theorem's actual statement.
3. **Presburger Part X remains a publication gap at this revision.** This is unchanged from the prior bounded placement review, not a theorem refutation.

No further scope mismatch was found in the front matter and central statements actually read. The manuscript's claimed build/test results, external literature matches, all-source textual preservation, transfinite proof correctness, and formalization remain outside this review's certification scope.
