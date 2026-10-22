# Independent review of Round12 runtime and quotient proposals

Read-only source/mathematical review; no census rerun and no received code execution. No substantive unsound inference was found. This is not compiler validation.

## Opaque-prefix residual contracts

Reviewed runtime README, check_templates.py, analyze_symbolic.py, OpaquePrefixHome.lean.proposal, and current KHome.home_word/scanBound_sound.

* Ordinary symbolic execution explicitly refuses to inspect opaque tokens. Normalization preserves their identities/orientations and cannot merge them into a bit/run segment. Its deletion of terminal left zeros is justified only by the standard blank-left exterior, which the stated contract retains.
* Home's reset across the suffix/prefix boundary needs P ending in1, not merely absence of eight zeros. The proposal includes that condition. The reversed opaque prefix is required to be the final scan chunk. Its conservative count7 is not used to continue scanning another literal chunk; the guard1 resets the eventual actual count. Thus the code does not treat the unknown count as an exact value.
* The Lean sketch's use of scanBound_sound supplies an existential actual terminal state j'<8. Appending the guard via rows.reset then matches home_word's required final state2. The entire arbitrary right frame is preserved by that existing theorem.
* Source-operation framing is logically separate from residual tape matching. Continue requires enough ones inside S; break requires enough zeros inside S and a non-overflowing increment of the stripped suffix. These conditions establish the output P++S' for arbitrary P. Finite agreement of concrete endpoints would not suffice by itself.
* For actual source paths, input gap n+(64-|pc|) equals n'+16 with n'=n+48-|pc|≥0. Since the output PC is P++S', the length difference is |S|-|S'| and does not depend on |P|. No hidden prefix-length-dependent shift was found.
* Strict progress is retained through moved and Reach1. Zero-length symbolic scan rules alone must not be counted as positive progress; the checker does not do that.

Remaining obligation: define the extended opaque-segment interpretation and prove EVERY extended interpreter rule, then the recursion/progress theorem, and bind all source occurrences to it. Neither the finite template census nor the Home lemma alone establishes universal residual correctness. Existing arithmetic BoxLemmas and uncompressed exceptional guards must remain. The README states these limitations correctly.

## Shared QHyp model core

Reviewed REPORT.md, staged adapter/compatibility examples, paired QuotientModel/KQ1Model definitions, and raw separation/power support.

* The two quotient carriers use the same underlying V and the same Eqv mem relation. Their setoid law fields and quotient-lift well-definedness arguments are proofs. Lean proof irrelevance therefore supports the expected definitional compatibility after transparent unfolding. There is no identified hidden representative choice in these particular compatibility equalities.
* Exact rfl elaboration remains an acceptance test, not an observed build result. This argument must not be transferred to Rocq conversion or strengthened into a claim that the final endpoint no longer uses classical choice or quotients.
* The nine QHyp fields are preserved, not postulated. Existing stronger CP/GIC providers supply them with the same witness. The K tagged-domain provider must stay on QHyp directly; forcing it through the stronger old model premise would change its obligations.
* The obvious cyclic migration is real: making old QuotientBasic/Power facades call an adapter that imports those same files is invalid. The proposal correctly avoids it by moving formula-only syntax and raw providers first. The reviewed separation_instance uses translated raw formulas and GIC, not the actual quotient-separation theorem; this is a legitimate extraction boundary.
* Source duplication counts are gross inventory, not removable-line or speedup claims. The adapter and explicit old-signature wrappers require compilation after extraction, with an import-cycle check and unchanged endpoint axiom reports.

The structural build_proposal.py now rejects Python -O/-OO before assertions. Ordinary execution passed; an optimized invocation was verified to reject. MANIFEST.json records the updated owned-checker hash.
