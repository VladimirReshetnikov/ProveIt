# Verification scope

## Mathematical review

The fixed-radius residue deformation, unbounded entrance-delay split, effective Fatou defect and tail, all-finite-order forward transfer, first correction, fixed-depth-shift rule, and amplitude positivity argument received independent mathematical review. The integrated real-model inverse and separate discrete threshold enclosure were also checked. No global half-plane continuation, arbitrary-radius invariance, or sharp logarithmic remainder degree is required or claimed.

The additional exact rational Abel-defect majorant and the coefficient/remainder generator were independently reviewed. Finite symbolic tests corroborate their implementation; the report supplies the arbitrary-order analytic construction.

## Executable checks

The production interval certificate uses 2048 full angular panels, 20 rational moment terms, 64 total iterates, and 30-decimal interval precision. Its independently replayed outer-integral enclosure was

    [2.148710226926796756397661371493759,
     2.423911766794793944536818666505863]

The verifier asserts the rational conclusion 214/100 < J < 243/100. With the analytically established absolute cut bound below 1/2, this proves 2 < C < 4. The finer numerical amplitude 2.86540798 is not certified.

Exact recurrence calculations match all 18 official exported terms of each sequence and include 72 independent small EGF checks. Default symbolic replay produces three correction orders, checks recurrence cancellation and polynomial degrees, and generates rational analytic Abel-remainder bounds.

The interval calculation relies on mpmath.iv providing valid outward enclosures for its arithmetic and elementary functions. This dependency is explicit and has not been replaced by a proof-assistant-verified arithmetic implementation. The mathematical argument is likewise not proof-assistant formalized.

## Artifact checks

All twelve revised PDF pages were rendered and visually inspected. No clipping, missing mathematical glyphs, overfull lines, or unresolved references were found. The package contains editable source and offline verification commands. A clean extraction replay is recorded separately from the producer replay.

No sequence database or public repository was modified or submitted to as part of this work.

## Attribution revision

The source-specific comparison credits Prellberg’s 2002 pre-sum formula and parabolic-coordinate method, as reproduced in Mishna’s 2005 seminar summary. The original mathematical review remains applicable to the unchanged proof and programs; historical attribution is reviewed separately in review/attribution-review.md. The original frozen identities are retained in review/original-frozen-sources.json.
