# Independent bounded review: support complexity at 20262718e

Frozen proof-only review of commit `20262718efdb5ef8545da72c2543c90c074bccf9` (parent `03683e579fd54a681ad649bd659cc51b1f450829`). All paths below are relative to the repository. Let **host** denote `Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/`.

**Result.** Proposition 270.1 and the selected strong-family/effectivity arguments pass this bounded independent challenge. Two editorial summaries omit the trivial exponent group: the guide's Section 270 paragraph and the article's Batch 96 commentary in Part XVII. Pascal located the latter; I independently read its standing hypotheses and the paragraph. The same three-case correction fixes both. This is not a certification of the complete publication, its roughly ten-thousand-line diff, or every imported descriptive-set-theoretic foundation.

## 1. Immutable sources and actual read scope

Whole-file pins authenticate the source containing the reads; they do not mean the whole file was read. Spans are one-based, inclusive, extracted from immutable Git blob bytes with line terminators retained.

| Source | Git blob | Bytes | SHA-256 |
|---|---|---:|---|
| host `README.md` | `198906d49d5c81bbba82d5b972be4127e607f40a` | 169187 | `a15d78b23f01fd1584aba0fcfa226f0f0d0b617ee8b5c215a8dee97c4157d952` |
| host `article.tex` | `cb5a8e0c47c68b861c88afe003e44e561927b999` | 2527864 | `a4f387f08e34730cb14262dd2d4b5c237b0a0b32d6d88b498d3623f8e6d83f19` |
| `Algebra/SurrealNumbers/AGENTS.md` | `78367178df40750c18c189f5076726ee0a4dea7a` | 9634 | `ecf44fe89f365a1b88d7d5e94e23bf3ab6a713d01a4ee8c44f72f234a4295039` |
| `docs/incoming/README.md` | `b0ac55c2c0ca25d3d187bd4d51d848fd17c48904` | 73104 | `d6888d4292c4f092436c24a7b4a8e9c20f3b34cb00775c0f777309910c059e38` |

| Read | Purpose | Span SHA-256 |
|---|---|---|
| guide 1019–1046 | Part XIX and Section 270 summaries | `5ab93ef85a6bf487a92d0d19c3e4d0d7b911455aecdb0ec986bd7081fb548068` |
| article 35400–35422 | Part XVII standing hypotheses, explicitly permitting the zero group | `5d1eaaa4f3591ea182530761f70d06782b9d3cbc9e6f0e0e98974b47630367f8` |
| article 36712–36760 | Question 237.1 context and the additional faulty summary | `dc2c96e758869f0373c8708a1580ba6782afb89ddcda595d333c1bf421e8b16b` |
| article 39390–39485 | Part XIX provenance/status interfaces | `77592a84ad330aaec65f2170d4ed5c3ea43d97134b3c165b8ee887309c056071` |
| article 39540–39670 | Introduction, classification and scope | `ed51c4a4a89d449a8dbe12acf6ea2e8189ec20bb49a45a17f641fc857c6fd8fb` |
| article 39865–40681 | Height/classification chain, group cases, strong families, sum topology, integer/real certificates, regularization and naming barrier | `180d5cc80874166805754176aa4f46554363ee6ce04323943f6bd6a24f43effe` |
| article 41110–41265 | Section 270 proposition, proof, effectivity, two computational obstructions and following transition | `c9d057dd6de0b9c832100bb82e2b6ec414113385e096805207f159844983e407` |
| AGENTS 1–182 | Applicable instructions, full file | `ecf44fe89f365a1b88d7d5e94e23bf3ab6a713d01a4ee8c44f72f234a4295039` |
| incoming guide 422–442 | Standing retention rule | `fb42be5afa7233dd8aa59af440f7d945a1584e29722b1a70ada521834769ded8` |

The article spans total 1,272 lines without overlap; the guide scope is 28 lines. Additional searches supplied locators only. Fresh inline metadata code read Git bytes and computed the hashes above; no author, archived, supplied, predecessor or frozen helper was executed or imported. No repository writes or builds occurred. No PDF, archive placement, full label inventory or full publication diff is certified here.

## 2. Retained editorial finding and valid correction

**Retained review finding 1.** The immutable guide, lines 1040–1044, says:

> For countable Γ ≤ R the code set of all well-ordered supports is Σ⁰₂-complete for cyclic Γ ≠ 0 and Π¹₁-complete otherwise, and is standard Borel iff L is scattered.

The article's Batch 96 note at 36739–36744 repeats the first classification, using `\Sf` and `\Pc`, after standing hypotheses at 35406–35408 expressly permit Γ={0}. For Γ={0}, every subset of Γ is well ordered: the binary support domain is the whole two-point space and the real coefficient domain is all of R. Neither is Π¹₁-complete. The guide's `L` is also unbound in this subgroup sentence; `Γ` is the applicable order. These are editorial defects, not defects in Proposition 270.1, which includes the zero case explicitly.

A correct replacement classification for countable subgroups Γ≤R is:

| Γ | Single-series domain VΓ / well-ordered-support predicate | Strong-family domain SΓ |
|---|---|---|
| {0} | Whole ambient space | Σ⁰₂-complete |
| Nonzero cyclic | Σ⁰₂-complete | Π⁰₃-complete |
| Noncyclic | Π¹₁-complete | Π¹₁-complete |

For both domains, with their inherited Borel structures, standard Borel is equivalent to Γ being scattered. Thus a concise guide replacement may state the single-series three cases and this equivalence; if it also mentions strong families, it must use the distinct third column. Root reports correcting both summaries with a numbered retained remark. This note validates that mathematical correction; it does not independently authenticate the later working-tree edits or rebuilt PDF. The immutable wrong claims remain recorded above under the standing retention rule.

## 3. Independent checks of the proposition and strong-family distinction

The relevant proposition is `pma:spc:w-prop:archimedean`, article 41144–41178. Its first part applies to countable ordered abelian groups, not merely subgroups of R. The cited classification gives Borel domains for scattered groups and coanalytic-complete, hence non-Borel, domains for non-scattered groups. If a subset A of a Polish space X has a standard inherited Borel structure, its inclusion into X is Borel and injective; Lusin–Souslin makes A Borel in X. Conversely a Borel subset of a Polish space is standard Borel. This proves the equivalence in precisely the asserted measurable-space sense. It does not assert that the raw subspace topology is Polish.

For a subgroup of R, a least positive element u implies Γ=Zu by Archimedean division. A nontrivial noncyclic subgroup consequently has no least positive element, is a countable dense order without endpoints, and contains a copy of Q. This gives the proposition's three cases from the earlier classification; the zero group is scattered and remains separate.

Strong summability requires both a well-ordered union of supports and finite incidence at every exponent. At Γ={0}, the latter says that a real sequence is eventually zero. This is Fσ and is Σ⁰₂-hard by restricting coefficients to {0,1}, where it is `Fin`. At a nontrivial scattered group, take u>0 and place binary row i at exponent iu; the union is contained in the well-ordered set {iu:i≥0}, while finite incidence at each exponent is exactly `Fin^N`. This explains the Π⁰₃ lower bound, including Γ≅Z, rather than importing the single-series Σ⁰₂ classification. The height conditions and finite-incidence formula supply the stated upper bound. For non-scattered groups the single-series lower bound embeds into families in one row. No contradiction arises between these standard-Borel cases and the article's nowhere-continuous/Baire-1 summation statement on a non-Baire raw domain.

The classical Lusin–Souslin theorem, standard complete-set facts, and the imported order-theoretic/descriptive foundations used in the read classification chain are accepted inputs here; their external proofs have not been newly certified. The omitted portions of Part XIX, its bibliography, and its Lean surroundings are outside this review.

## 4. Effective interfaces and the finite-integer boundary

The integer and real certificate constructions carry entire countable sequences of support-height and incidence bounds. They are not finite certificates merely because each entry is finite. Given those bounds, each requested sum coordinate reduces to finitely many rows. The real bounds still permit such a cutoff locally, which supports continuity on the certified space.

Remark 270.2 correctly makes the regularization computation conditional on computable exponent enumeration, height table and finite-window lists, with real inputs represented by fast Cauchy names. Its soft thresholds, ramps and finite maxima are computable real operations; no exact zero test or computable convergence modulus is assumed. Coordinatewise computability of each regularization does not imply computability of the limit.

I independently checked both new halting observations at 41207–41228 in the larger recorded span. For the first-halting array X[n,e], each entry is decidable, the union lies in N, and every column has at most one active row. Its sum is nevertheless the halting characteristic. A computable incidence bound decides halting by bounded simulation; a computable real bound gives an integer upper bound by fixed-precision approximation. Thus legal computable input need not admit a computable certified name. For Y^(e)[n,0] indicating that machine e has halted by step n, finite incidence holds exactly for nonhalting e. A uniform reduction from arbitrary computable-array indices to finite ordinary existential Diophantine solvability would enumerate the nonhalting set, a contradiction. The reduction uses only total binary coefficient programs and does not depend on effectively transferring a boldface completeness theorem.

These arguments do not obstruct evaluation on already supplied certificates or on explicit finite data. Conversely, no positive algorithm follows from a bare promise of finite but undisclosed support; a support cutoff and an explicit finite list are additional information. No paid arithmetic circuit, finite ordinary-integer evaluator for arbitrary raw arrays, gate reduction, or universality result is supplied by the reviewed interfaces. I found no additional concrete mathematical defect in the selected statements and proofs.
