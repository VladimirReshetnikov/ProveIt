# Attribution

The original compact calculus, native set theory, register proof-search program
and 254-state machine are credited to Mira-Cult. Upstream Rocq/Coq verification
is credited to Jeff Ketchersid and contributors. The compiler framework is
credited to Andrew James Wade. ProveIt and its earlier incoming reports retain
credit for the subsequent program, routing, initializer and state reductions,
and for their logical and formal consistency calibrations.

The exact input to this work is ProveIt's `candidate-rotation240` at commit
`13ec39ed43148b1807f51ed6e6528e1c84659562`. The original 240-state notices are
retained in `reference/baseline240-ATTRIBUTION.md` and
`licenses/ATTRIBUTION-source80.md`. Earlier notices can discuss their own state
counts and dates; those historical statements have not been relabeled as new work.

The universal affine/list checker and `independent_runtime.py` helper are
unchanged Source 80 bytes. Their original “self-authored” comments describe
their original authorship, not this task. Replaying one engine through two
drivers is not two independently implemented universal verifiers.

New work prepared for this request with ChatGPT comprises the concrete
coordinated helper-row reduction to 239 states; its guarded local simulation;
the universal right-neighbor instrumentation; independent open-tape, bootstrap
and source-extraction checks; research screens and counterexamples; the
mathematical report and reproducible package.

For the alternative equational frontend, Source 79 supplies the native stack
and original complete codec. Source 40 supplies the general false-class
witness-slice idea. Earlier Source 78/79 reviews supply truth-constant fusion.
The new concrete specialization is class NAND `J=P`, composed with the particular
member-selector allocation `Pick(x)=W(x,d)` and that existing truth fusion.
The inherited raw-EPSC calibration and the McCune et al. Sh1 Boolean basis remain
explicit dependencies. See `foundations/ATTRIBUTION.txt` and `foundations/sources.json`.

All inherited licenses and notices remain under `licenses/`; no inherited
material is relicensed. Newly generated research was prepared for incorporation
into the user's ProveIt repository, with no additional licensing restrictions
asserted. No personal author is inferred from tool names, filenames or agent labels.

The new claim is this particular machine, its ordinary mathematical proof and
its evidence. No global historical priority for every technique, minimality
of 239 states, unconditional consistency, or new proof-assistant endpoint is claimed.
