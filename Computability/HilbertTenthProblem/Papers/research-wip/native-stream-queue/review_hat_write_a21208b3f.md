# Hat Part V publication review at a21208b3f

**W1/W2 correction and source preservation pass in the stated scope; two new write-side errors require correction.** The main finite-public and private endpoint results survive. The guide incorrectly transfers the private uniform success gap to finite public seeds, and the new prescribed-seed proof has an equality that fails when its atomic and diffuse output labels coincide. Both erroneous claims and their counterexamples are retained below. This reviews immutable publication bytes, not any subsequent repair.

## 1. Immutable publication and evidence

Publication `a21208b3ff14a07a4c8318dbf916d543acbef043`, parent `52a34387969be9cf56e36c1c9241e0eb1407a72c`, changes exactly `README.md`, `article.tex` and `article.pdf` under `SetTheory/Cardinals/docs/reports/ordinals-and-order-types/measurable-box-games/`. This is an actual Part V write, unlike the preceding ancillary placement. The source contains Sections70–81 and AppendicesH–I. The changed PDF is authenticated as bytes only.

| Publication file | Git blob | SHA256 |
| --- | --- | --- |
| README.md | `14c3ed8b305960fd9cc9a19d877e8eeb621e4888` | `d5ab9ff61892d6538745d52cdb0bee538cbc6d7877570a9fae5e18af68e91982` |
| article.tex | `1e99e7b311fc03b24b56cc8e54b946108cbe7356` | `7d78de4dcaa462472227b3702b240d10bf9610eaf23fd7b69cdd41eeabc49298` |
| article.pdf | `ca95c6bd87f3fae9dacc25ecde8174417203bd93` | `3832fd2a0550db28ece7e1607d9096e72766b1a461fe051d98543ece01523a48` |

The original archive is `26e036956381b07bb43de0187965f8dcdf9194fb:docs/incoming/hat_randomness_frontier.zip`, SHA256 `eccc49ac838592997e1c7d8ef0c5ba7c1a95bd76abbb8f12814f552dc34b9e20`. Its eight members are inventoried and hashed afresh. The original1660-line TeX member has SHA256 `7d6c4815a4be0363a6d0deee1189396b4818033102ee28b21eb04b8102b47c71`. The five placed ancillary files are byte-identical to their archive members at both publication endpoints; none changed in this write. There is no delivered internal checksum manifest.

The fresh companion `review_hat_write_a21208b3f.py` has SHA256 `e725ef26ec0751d2300c90cc2a7c386ef44f86c551d5c55b562ad404b0aabf76`; receipt `review_hat_write_a21208b3f.json` has SHA256 `1ab7d73754fb9b6a6ed21706d655af42dcbe6035703d13584cf97e530c26b308`. The receipt pins parent/publication blobs, exact raw diffs, member and placement bytes, normalized comparisons, and inclusive human-read line spans. Its source hash binds the fresh checker. Its normal and `-O` exact receipt checks passed from `/` before freeze.

## 2. Finding F1: the finite-public guide gap is false

Publication README lines685–688 says:

> with independent private seeds and `E Q_i ≤ 1` for every `i`, `P(D_n → +∞) < 1`, indeed `≤ 1 − 1/5184`; the same with a public seed that is almost surely finitely valued.

The last clause falsely extends the uniform numerical gap. Article Theorem75.5 proves nonattainment of probability one for finite mass-one public support, not a universal gap below one. Its Proposition79.3, article lines9320–9343, explicitly proves that a two-valued public seed can give success arbitrarily close to one at cap one.

A concrete parameter choice suffices. Take a private almost-sure winning strategy with uniform cap at most `c=19999/19998>1`, permitted by Proposition77.1. Turn it on with a public Bernoulli gate of probability `r=9999/10000` and use constant zero-query guesses otherwise. Then its unconditional cap is at most

`rc=19999/20000<1`,

while its divergence probability is at least

`r=9999/10000>5183/5184=1−1/5184`.

The public support has exactly two values and total mass one. Thus the sentence is false even with the repaired definition. There is no contradiction to the private result: the players now share a gate. There is also no contradiction to the conditional-public-cap corollary: when the gate is on, the conditional cap is greater than one.

Recommended replacement: “For a public seed with finite mass-one support, Theorem75.5 gives `P(D_n→+∞)<1`; there is no uniform gap below one, by Proposition79.3.” Preserve the former guide claim in a dated, numbered correction remark with the example above and attribution to this review. The article's existing private and finite-public proofs need no alteration for F1.

## 3. Finding F2: atomic output collisions invalidate an exact probability equality

New Corollary75.7, article line8820, treats a finite atom set `A` and diffuse mass `c>0`. It sets `g(theta)=theta` on `A`, and `g(theta)=j` on the j-th diffuse interval of mass `c*2^(-j)`, then claims:

> Then `Pr(g(Theta)=j)=c*2^(-j)>0` for every `j>=1`.

The equality can fail because an atom's value can itself be the integer `j`. For example, let `Theta` have mass1/2 at the atom1 and mass1/2 uniformly distributed on `(2,3)`. In the stated construction, the first diffuse interval has mass1/4 and maps to1; the atom1 also maps to1. Therefore `Pr(g(Theta)=1)=3/4`, not `c/2=1/4`. A Borel embedding and the quantile partition used by the proof exist for this explicit space, so the collision is within the stated hypotheses.

The theorem and its construction survive: the valid inequality is `Pr(g(Theta)=j)>=c*2^(-j)>0`, which is all that is needed to obtain infinitely many positive-mass values. Alternatively use tagged, disjoint atomic and integer output labels. This is a minor actual proof-equality error, not merely an unproved generalization. Preserve the old equality and this counterexample in the dated correction record. Root independently confirmed both F1 and F2; this frozen review does not certify root's later edits or PDF build.

## 4. Original W1/W2 repairs and added interfaces

The earlier frozen correction `review_hat_seed_definition_correction.md`, SHA256 `91323ce99a38e5b6951eb5940ccbba034a658259c07fcb61c8c658d5320a9701`, distinguishes finite atom count from a finite set carrying the entire law. The new Definition71.1 explicitly requires `Pr(Theta in {t1,...,ts})=1`; Theorem75.5 repeats that hypothesis. Their corrected wording supplies precisely the missing premise of the weighted conditional-cost argument. In particular, `sum_r p_r=1` makes both `E z_i<=1` and the centering identity valid. The unchanged stopped-process/private argument then applies.

Numbered Remark75.6 retains both delivered wrong phrasings and gives a genuine one-atom-plus-diffuse counterexample: `Theta=B*U`, with a fair bit `B` independent of a uniform variable `U` on `(0,1]`. Its effective shared integer has the original public-endpoint law with parameter1/2. The floor formula's interval-endpoint convention changes only a null set, so its probability calculation is valid. The remark accurately identifies the failed centering when the atomic mass is1/2.

The abstract now says “countably infinite support.” Its correction note explicitly distinguishes a prescribed finite seed from a public seed of our choice. This respects W2's quantifier issue: the original theorem table's existential “of our choice” reading was already correct. The publication qualifies the earlier arrival and endpoint reviews as having silently used the mass-one interpretation, retains their original records, and does not retract their independent-private conclusions.

Corollary75.7's equivalence for a prescribed standard Borel seed is supported after the F2 inequality correction. The finite-atom/diffuse split supplies a countable image with infinitely many positive masses; the infinite-atom case does so directly. The standard-Borel embedding premise is stated, not a claim about arbitrary measurable seed spaces.

Corollary75.8 correctly recovers the uniform `1−1/5184` gap when the budget is imposed conditionally on the public seed: independence, joint measurability and Fubini reduce almost every fixed public outcome to the private theorem. A countable intersection handles all players at once. Its private admissible caps `(1,infinity)` and deterministic conditional caps `[2,infinity)` agree with the supplied hypotheses. This does not repair F1's unconditional assertion.

The added research questions retain the finite-prefix heuristic, measure-theoretic prerequisites, and unsubstantiated preparation-stage independent-review claim with explicit limitations. The new Fourier-limit and coordinate-flip explanations are consistent in the read scope. No external literature or novelty audit is claimed here.

## 5. Normalized preservation and exact review scope

The fresh checker reconciles the **entire original main body**, from its first section through AppendixB, against PartV after documented transformations: label/reference and bibliography-key renaming, the five declared variable renamings, norm/indicator/almost-sure typography, editorial provenance/notation notes, added environments, and appendix layout. The only permitted substantive main-body replacements are the W1 definition and theorem hypotheses and the two sentences retained in the new research questions. After those explicit exclusions, the normalized50523-character bodies are identical, SHA256 `8032fab6ecde8e78979063cc4dd6942f3389dd3b0e2c43cf31d46a6880dc2c46`.

Separately, all42 original statement environments are matched:40 are equal after the declared normalization, and only the W1 definition/theorem differ. All29 attached original proofs and all38 labeled equations are unchanged after normalization, including the private, finite-public, public-mixture and upper-construction proofs. This is textual preservation evidence, not a fresh proof certification of every unchanged result. The source's80 labels all acquire the specified prefix; twelve labels are added. All335 older host labels remain, giving427 unique labels, with no unresolved simple literal references detected. This does not substitute for rendered numbering or a TeX build.

Human reading in this pass includes the full publication commit message; the full557-line README diff; TeX raw-diff lines1–180 and1780–1911; and these publication-TeX spans:7934–8240,8290–8305,8540–8592,8600–8890,8925–8940,9015–9029,9058–9070,9290–9375,9400–9450,9465–9705,9958–9986. These cover the new provenance/notation/correction text, added editorial notes and research questions, private/finite-public arguments, all three new numbered interfaces, and the public-mixture contradiction. The original manuscript's lines1–110 were also reread; the full member was mechanically compared. Prior source proof coverage is inherited only as recorded in the pinned original reviews and correction note, not advertised as a new full-manuscript read.

No source, archived, predecessor or frozen program was executed or imported. No saved finite test result was replayed. No PDF was rendered or built. The article's claimed499552 checks and the remote author's build/visual claims remain attributed saved evidence. No repository file was modified. The incoming retention rule was read and applied to both original and newly found wrong claims.

The model counts expected hat inspections while allowing arbitrary measurable computation and external random bits for free. Neither this publication nor the checked corrections supplies a paid ordinary-integer Diophantine compiler, an arithmetic gate reduction, or a uniform finite evaluator for the permitted measurable functions.
