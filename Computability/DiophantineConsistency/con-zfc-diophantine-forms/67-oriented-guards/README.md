# Oriented guards and smaller Diophantine consistency equations

Start with report.pdf (complete article) and report.tex. This research iteration
reviews the six original wave8 archives at arrival7331974b696693a8eed2aa5f0f64f1c19d9569f0,
placed atbeb0192cb8dc36f78c369c080f2adfbc1887a486. Full archive and Git blob hashes
are in INCOMING_PINS.json. All six original root replays passed;72 selected
literal circuits were independently counted. Original source trees were untouched.

## Main results

Each endpoint is one fixed integer polynomial. Named registers add no unknowns.
The mathematical proof composes new transformations with explicitly identified
inherited compiler/arithmetic theorems and establishes, formalizably in ZFC,
that absence of solutions on the stated domain is equivalent to Con(ZFC).
It does not prove consistency or inconsistency.

- 42 unrestricted integers: degree4, sum of27 quadratic residuals,391 symbolic
  terms. Improves the incoming45-integer quartic by3 unknowns and1 residual.
- 36 unrestricted integers: degree6, sum of21 cubic-or-lower residuals,435 terms.
- 32 unrestricted integers: degree8, sum of17 quartic-or-lower residuals,395 terms.
- 9 positive integers: degree1,731,700 /462 operations, versus1,910,404 /473.
  Lower-degree alternative1,494,006 /487, with intermediate tradeoffs.
  The natural-coordinate versions add7 gates:469 and494 respectively.
- 10 unrestricted integers: degree3,327,556 /519 operations. Uses Sun2026.
- 13 unrestricted integers, without Sun2026: degree10,461,744 /519 operations,
  a degree improvement over11,543,632 /518 at one extra gate.
- 14 positive integers: degree30 /87 operations; five-equation system maxdegree15
  at78 operations. Saves one variable over incoming15-positive30 /79, at8 gates.

The42/36/32 integer low-degree routes do not use Jones's universal expression
or Sun's ten-integer reduction. Their native compiler still calibrates K215.
The user did not require either K215 or Jones: alternatives/ separately assesses
direct provability, other constructive DPRM compilers and fixed-input universality.
No competitive new non-K215 endpoint was established in that exploration.

All operation counts charge live binary addition, subtraction and multiplication,
including multiplication by numerals; fixed coefficient leaves and shared register
reuse are free. This is not bit complexity. The incoming66-operation degree157
fifteen-positive equation remains the operation incumbent. Degree24/90 and26/88
fifteen-positive constructions also remain useful; no all-metrics or global
minimality claim is made. Current twelve-positive242/94 and258/89 are not displaced.

## Structural improvements

1. In the quartic, replace w=u² by the cofinal restriction w=4u². This establishes
   |E|>3R+1 before Pell rank recovery, so a single eta*zeta positivity guard can
   safely replace two separate guards. The negative common-sign branch would
   force n>R, contradicting the independently recovered p=R and p>n.
2. Exact monic coordinate elimination gives the36-integer sextic and32-integer
   octic with explicit integer-polynomial inverse reconstruction.
3. A new108-weight code and global row negation lower source convolution height
   2161→1954 and give positive leaders in all three degree-specific kernels.
4. Higher Pell majorants expose additional cancellations in the9-positive norm.
5. The new two-root congruence finalizer combines with the smaller source. Clearing
   an irrelevant low mask bit and removing a leading high bit preserves divisibility
   after dividing its fixed threshold coefficient by4.
6. The14-positive carrier restores q³|Y first, making the adaptive modulus4qY
   valid and less costly in degree than4q⁴.

## Domains, coefficients, proof boundary

Every JSON declares its domain. Do not interpret a positive-domain equation over
all integers. The source small-variable families keep the complete original31
Wang943 tuple, not a portwise mixture. positive/ keeps the whole590069 compact
tuple. quartic/ uses the whole package34 mixed-parity-unrounded1064921 tuple,
not the distinct original31 tuple with the same radix exponent. High masks are
already shifted. Actual raw/gzip payloads or precise fixed integer recipes and
complete binding/provenance statements are supplied.

These are ordinary mathematical proofs with exact finite certificates and
AI-assisted independent reviews, not a new end-to-end Lean/Rocq proof or an
exported derivation in the repository's object-language ZFC calculus. Recent
local Lean progress is reported accurately in review/baseline/; it does not
certify the new literal circuits automatically. No arithmetic-soundness
assumption is substituted for syntactic consistency.

## Replay

Python3.10+ and SymPy1.14.0 suffice (tested Python3.12.14). No network access is
needed for the new release's root replay:

    python verify.py
    python negative_controls.py

The root checks the sealed manifest, makes an isolated copy, executes the
listed stages and compares each REBUILD_FILES.json artifact byte-for-byte.
It leaves the sealed originals unchanged. Component tests include explicit
negative controls; root corruption tests are byte-integrity checks only.
Normal and optimized Python results are distinguished. The root replay is
run normally; individual independent checkers also have optimized-run receipts.

Build the PDF with a normal TeX Live installation:

    sh build_report.sh

The seven section copies and SECTION_LAYOUT_MAP.json are reproducible. Original
component TeX is retained. PDF metadata may change on recompilation.

Original incoming-archive replay scripts in review/baseline/ are intake evidence;
repeating them requires those original archives, not just this additive release.
They are not part of the offline root replay. The portable quartic literal audit
checks every retained source hash; its historical direct original-tree comparison
is recorded from intake, and is repeated only when that separate tree is present.
The unchanged intake script is preserved beside the portable version.

## Layout

- quartic/: main42-integer equation and36/32 monic projections, complete proofs,
  full literal systems and expanded polynomials, whole coefficient/source subtree.
- encoding/: compact108 source certificate, proof, exact tests and signed padding.
- nine/: all9-positive/natural cost-degree variants, full proof and independent checks.
- signed108trim/: recommended10-integer circuit and complete Sun/congruence proof.
- signed13/: Jones-only13-integer degree tradeoff and correct cubic-epsilon threshold.
- signed/, signed108/: earlier10-integer composition variants, explicitly comparisons.
- positive/:14-positive adaptive-modulus polynomial/system.
- alternatives/: independently sourced architectural exploration, no claimed endpoint.
- review/: immutable baseline, mathematical audits, corrected transport-offset note,
  coefficient/degree/circuit receipts. root_checks/: aggregate endpoint audit.

The incoming Q45 prose shifted a transport quotient by one; the literal Q45/Q50
row is preserved and corrected positive-z recovery is documented. No original
source was silently rewritten. The rejected unscaled shared-sign proposal and
superseded degree34 positive draft are not new validated endpoints.
