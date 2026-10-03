# A four-bit discrepancy in the published Grill Tag encoding

The creator's [Grill Tag proof, revision 181950](https://esolangs.org/w/index.php?title=Grill_Tag&oldid=181950)
has an inconsistent description of encoding E. Its second variable grill is
described as having **a−2 ones**. That makes the full encoding four bits longer
than the claimed width. The displayed width calculation and the actual
production list instead require **a−4 ones**. This is a defect in the published
description, not a counterexample to Grill Tag's computational universality.

Here a grill with r ones is `0(10)^r`, of length 2r+1. For a symbol indexed by y,
the published E description has total length

    (14y+7) + (2a−5) + 15 + (2a−3) + (3a−14y−10)
      = 7a+4.

For an even-width symbol it adds another 7a zeros, giving 14a+4. The claimed
widths are 7a and 14a. Replacing only the second grill's count by a−4 gives
length 2a−7 for that component and restores the claimed totals. The published
L/R-to-E run lengths a−3, 7, a−4 independently support this correction.

This matters to the simulation: widths determine the next instruction phase.
An extra four bits per encoded symbol changes that phase. It is not merely an
incorrect complexity estimate.

## Independent bounded compiler check

The [checker](review_grill_encoding_e.py) independently transcribes the published
run formulas for two nonhalting Genera symbols, indices 0 and 1, with a=84. It
does not import or execute the creator's interpreter or compiler. The
[receipt](review_grill_encoding_e.json) covers all 256 two-symbol production
tables, all four width pairs modulo two, five initial symbol strings and both
initial positions. Every production has exactly two output symbols.

For each of the 10,240 cases, it compares whole strings and phases through two
generations:

    corrected E → L/R encodings of the Genera successor → corrected E.

All 20,480 string identities and 20,480 phase identities pass. The uncorrected
published E string gives the wrong first-generation string and phase in every
one of those cases. Run positions are checked for collisions, range and parity.
For example, with a=84 the published E lengths are 592/1180; the corrected and
claimed lengths are 588/1176.

The test is exhaustive only over that stated finite fragment. It does not
prove the general compiler, test the special halt-symbol protocol, establish
an ordinary-binary-input loader, or produce a universal polynomial bound. The
arithmetic discrepancy itself follows directly from the length identity above;
finite tests provide separate evidence for the proposed correction.

Reproduce using standard Python:

    python review_grill_encoding_e.py --output /tmp/fresh-grill-encoding.json \
      --expect review_grill_encoding_e.json

The checker rejects `python -O`, uses explicit exceptions for failed checks,
and compares receipts recursively with exact types. Root ran the complete
10,240-case check before committing these artifacts.

## Source provenance and distinct orientation repair

The [current Grill Tag page](https://esolangs.org/wiki/Grill_Tag), retrieved during
this review, identifies its permanent revision as 181950. The creator's
[2023 announcement](https://codegolf.stackexchange.com/a/265539) explains its
finite-tape interpreter and the reduction through
[Genera Tag](https://esolangs.org/wiki/Genera_Tag). These are an informal creator
construction, not a separately checked universal compiler in this repository.

A different typo was already discussed and corrected by the creator in
[May 2026](https://esolangs.org/w/index.php?title=Talk:Grill_Tag&oldid=181840):
the microcommand `11` appends `01`, and a run is n copies of `11` followed by
`10`. This produces the macro appendant `0(10)^n` used here. The new E-length
finding is independent of that orientation correction. No external page or
delivered report has been modified.
