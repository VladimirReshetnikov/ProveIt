# Parts V–VI of the signal-machine report: publication transfer at ef114b0bb

The source transfer passes within the bounded scope below. Two new presentation claims need narrow corrections: the README reverses the explicit compiler quantifiers, and the threshold table turns an unasserted reversibility property into a negative assertion. Neither is a defect in the imported source theorems. The [proposed text patch](signal_batch80_quantifiers_ef114b0bb.patch) was applied and checked only in a private temporary directory; no maintained file or PDF was changed.

This review is of commit `ef114b0bb400c2f21e1885dd16cc90a0e346b3f4`, against parent `ecc9185aaba684dfa80c804511537cbea4738f3b`, for `signal-machine-collision-certificates`. The commit changes exactly `README.md`, `article.tex`, and `article.pdf`. The four source archives are read from immutable arrival `4e270aa4648c5fd7e18626507531046715976535`. The [checker](review_signal_batch80_typesetting_ef114b0bb.py) and [receipt](review_signal_batch80_typesetting_ef114b0bb.json) authenticate both versions of all three publication files, every source archive and its main TeX member, the separate independent challenge, and all exception blocks used by the census. They do not import or execute report programs.

## Two presentation corrections

**P3 — README lines 66–71, compiler quantifiers.** The new summary gives “a fixed” CA which “simulates every separated” reversible two-counter machine, immediately tying that statement to the direct canonical gap and per-source-step interface. The actual source-14 compiler theorem, article lines 3864–3872, says: for each finite separated reversible source machine `M`, effectively construct a rule `F_M`. Its alphabet, control labels, type counts and canonical `(q,a,b)` encoding depend on `M`. The next theorem fixes a universal source to obtain one fixed rule with undecidable observation. The new article introduction at line 415 already distinguishes these steps correctly. Source 15 also warns at line 4660 that its wrapped source compiles to a different rule and set of control types.

The patch restores “every finite separated ... M compiles to ... F_M” and then explicitly fixes a universal source for the fixed-rule conclusion. This does not deny that one universal compiled source can simulate other machines through an additional effective interpreter/input encoding. It prevents that further encoding from being conflated with the stated direct, machine-dependent canonical interface.

**P3 — article line 428, reversibility attribution.** The new mass-threshold table says that the Alhazov–Imai abstract supplies a five-particle construction which is “not reversible”. The reviewed source and the publication's own new literature paragraph say only that reversibility is **not asserted**, with the full paper unchecked. The new table has strengthened absence of a claim into a negative theorem. The patch changes precisely those words to “reversibility not asserted”. The preserved bibliography identifies the [publisher abstract](https://ieeexplore.ieee.org/document/7818615) and [paper DOI](https://doi.org/10.1109/CANDAR.2016.0045). A fresh direct publisher retrieval was inaccessible during this bounded review; no new full-paper or current-literature conclusion is asserted. This correction restores the already documented evidential limit.

The patch leaves all imported mathematical statements, formulas, programs and data unchanged. Its SHA-256 is `7c802a987012d3c552889bf258f475d22034ad0010881e7e3cf93bda58d0bedd`. Private `git apply --check` and application both pass. The resulting README hash is `556305f4477507d35bed72450066036f2d479faf5030e0c637da9592c768b14a`; the resulting TeX hash is `d4ceb6dc79cd4df708c454131f17e69794652e0409cc34c0ab6090118c964d35`. Applying the TeX correction to the maintained report would require rebuilding its PDF; this packet does not supply that rebuild.

## Source preservation, with occurrence multiplicity

The four original manuscripts had already received substantive mathematical and executable reviews in [the three-mass review](review_batch80_three_mass.md) and [the low-mass review](review_batch80_low_mass.md). This audit reads the new README text, new front matter and all new editorial comparisons, limitations, questions, provenance and bibliography passages, and checks the transfer of the original formal statements, proof environments and displays. It is not a new whole-book audit of Parts I–IV or a repetition of the original computational suites.

| Printed source | Original main member | Formal/proof occurrences | Displays |
|---|---|---:|---:|
| 14 | `three-mass-release/three-mass-report.tex` | 22 retained, 1 proof pointer | 40 retained, 5 declared deduplications |
| 15 | `clean-target-release/clean-target-report.tex` | 14 retained, 1 proof pointer | 26 retained, 2 declared deduplications |
| 16 | `single-unit-three-mass/single-unit-mass-three.tex`, attribution revision | 16 retained | 13 retained |
| 17 | `four-mass-bound/four-mass-decidability.tex` | 19 retained, 2 proof pointers | 19 retained |
| Total | | 75 accounted for: 71 retained + 4 pointers | 105 accounted for: 98 retained + 7 deduplications |

The checker consumes a separate target occurrence for every source occurrence, within that source's printed section, and requires increasing target indices. It does not reduce formulas to sets. It checks environment counts and balance, records source/target indices, line numbers and normalized hashes, and rejects an unlisted omission or surplus. Thus repeated identical statements or displays cannot silently disappear.

Normalization is limited to whitespace/comments, labels/tags, the four declared label prefixes, `\N` to `\NN`, numbered-versus-unnumbered equation wrappers, source 16's explicit `(2)` to the new equation reference, and explicitly bracketed `[write]` editorial notes. Every original mathematical macro definition is checked against the target definition, with only the declared natural-number macro rename and equivalent `\mathbb` bracing. It does not algebraically simplify or discard hypotheses. This is a normalized text-occurrence census, not a TeX parser or a formal proof assistant.

The four proof replacements were read against the original proofs and their cited statements. They are source 14's bounded-diameter proof (source line 702, target line 4470), source 15's repeated forward-certificate proof (source line 349, target line 4959), and source 17's two small-packet proofs (source lines 108 and 144, target lines 5796 and 5819). Their original and replacement bytes are separately pinned. The seven display omissions are confined to source 14's five mass-two reproof displays (source lines 636–665) and source 15's two mass-two restatement displays (source lines 225 and 231). The article explicitly redirects those arguments to the earlier Part IV result; no new source theorem statement is omitted. The checker does not claim that all ordinary source prose is retained byte-for-byte: the publication explicitly deduplicates prose as well.

## Semantic conclusions within this publication

The model distinction survives the transfer. Many weight-one labels can hold finite control in the weighted reversible simulator; the single-unit-symbol theorems do not apply to that alphabet. Conversely, the single-unit result concerns fixed finite rules, positive weights, a unique zero-weight vacuum and finite support. It does not declare arbitrary weighted three-unit systems decidable. The mass-three timed Presburger relation is uniform in positions and time for each fixed rule. The mass-four decision result uses an untimed fixed-input orbit description; the explicit binary shuttle disproves a corresponding general timed Presburger claim.

The new notes keep separate pattern occurrence somewhere, anchored observations, exact whole-configuration targets and global halting. The exact-pair construction has an input-dependent target and a fresh-entry wrapper; it is not a target independent of the input or an identity between microscopic forward and reverse paths. Its compact/full witness correspondence is a natural-zero-fibre statement, not equality of the complete polynomials away from zeros or a map of the whole real orthant. The finite-horizon degree-two certificates still have an externally specified source horizon and growing witness families. The bounded loader is not a free exponentiation oracle, and no new fixed-arity universal polynomial or improvement of the 87-operation bound follows.

The new reference to the strong branch gate is sound. For nonnegative real selectors, `(sum(e)-1)^2` together with `(E-e_j)(e_j+u_j)` forces one-hot selection and vanishing inactive bases: both factors are globally nonnegative in the original selector coordinates. The arithmetic divisibility interpretation of the selected branch still requires natural witnesses. The publication says exactly this; it does not infer real fibre exactness from the real one-hot lemma.

The added quartic degree-minimality claim at README lines 1055–1061 and article line 6237 is also properly restricted. The displayed hit relation is

`H = {(x,t) in N² : exists k in N, t = k² + (2x+3)k}`.

Its `x=0` section has successive gaps `2k+4`, hence is not eventually periodic and is not semilinear. The cited classification concerns integer polynomials jointly nonnegative on the entire real nonnegative input-and-witness orthant, with finitely many existential **natural** witnesses. In that class, every degree-at-most-three projection is semilinear; the displayed squared residual realizes `H` at degree four. This proves minimality in the stated class even with extra witnesses or without single-foldness. It does not exclude the unsquared quadratic residual, which changes sign, and it does not assert exactness under existential real witnesses. The real false witness at `(x,t)=(0,1)` remains disclosed.

The [separate independent quantifier/classification read](review_signal_batch80_quantifiers_ef114b0bb.md), with its [pinned record](review_signal_batch80_quantifiers_ef114b0bb.json), independently confirms the README correction and this restricted degree argument. The main checker authenticates both companion files, every source/publication pin they cite and their exact line anchors.

## Publication and replay boundaries

The complete 218-file directory inventory agrees with the README listing. The other 215 files, including all placed executable/data companions, are unchanged by this commit. The delivered source-17 vector figure is byte-identical. The five intentionally excluded source-14 exports total exactly 20,752,637 bytes, as stated, and are absent from the publication tree; their original bytes and hashes are recorded without regenerating them. Earlier placement/replay results support the documented compiler and export commands. No fresh claim of executing those commands is made here.

All 252 earlier label names remain in order among 417 unique labels. All 36 earlier bibliography keys remain in order among 48 keys. The checker resolves 846 literal `ref`/`eqref`/`pageref` occurrences and 156 citation-key occurrences. This checks named-reference integrity, not rendered page/section numbering or every external URL.

The earlier source-13 correction notices, historical restoration recipes and previously identified editorial patch status are inherited from prior commits. They are not counted as new defects in `ef114b0bb`, and this review does not assert that all older recommended patches have been applied. Likewise, the unchanged Part-III abstract's earlier scope issue is outside this new-transfer finding set.

No author suite, TeX build or PDF visual inspection was run. The PDF's bytes are authenticated, but its pagination, fonts, layout and rendering are not independently certified by this packet. There are no repository or Git mutations.

Replay from any directory, keeping the two independent challenge files beside the checker:

```sh
python /path/to/review_signal_batch80_typesetting_ef114b0bb.py \
  --repo /path/to/Proofs \
  --expect /path/to/review_signal_batch80_typesetting_ef114b0bb.json
```

Use `--output` to save a receipt and `--patch-output` to save the deterministic proposed patch. The receipt comparison uses canonical JSON serialization, preserving Boolean-versus-integer distinctions. The source rejects optimized Python mode so its proof-checking assertions cannot be disabled. Authoring and a fresh read-only replay both passed on the frozen checker.
