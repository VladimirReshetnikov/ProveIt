# Native site-30 jump sentence

`PA194Site30JumpSentence.nativeIPRA` proves the universally quantified exact
40-step packed literal-machine equality for the site-30 jump in native
`standardTheory`. `modelSentence` establishes the equality in each PRA model;
`classicalPRA` and `nativeIPRA` transfer it to actual derivations. Its inputs
include arbitrary model-valued register-file data and suffix. This finite jump
does not establish arbitrary source-step simulation or either consistency
implication. `check-site30-jump-sentence.sh` rebuilds both physical and sentence
modules from pinned sources against the same staged object roots as the site-30
checker; it also audits the reported axioms. See `SITE30-JUMP.md` for the
staged-object caveat and physical layout.
