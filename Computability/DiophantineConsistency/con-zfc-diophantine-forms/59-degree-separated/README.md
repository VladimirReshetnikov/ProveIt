# Degree-separated encodings and an ordinary-root merger for Con(ZFC)

Start with report.pdf and its editable report.tex. This package reviews all
eight wave-seven archives at arrival 4b4349064a750ba6347293b55874a7f92abdd0db,
placed as 46–53 at 6d375f2d2deac0519e659bbce5b48087023c1430. INCOMING_PINS.json
records the exact archive SHA256 and Git blob identities.

## Main improvements

Every expression is an explicit integer polynomial with fixed coefficients.
Named registers add no quantified unknowns. Operation counts charge binary
addition, subtraction and multiplication, including scalar multiplication
and fixed-power evaluation.

- 9 positive integers: exact degree 1,910,404, 473 operations.
  Natural-domain version: same degree, 480 operations.
- 10 unrestricted integers: exact degree 8,469,528, 533 operations.
  This route uses Sun's2026 bridge; the other main routes do not.
- 13 unrestricted integers: compact Jones variant, exact degree 11,543,632,
  518 operations. The positive-threshold baseline is11,546,112/520.
- 12 positive integers: exact degree 316, 102 operations, versus 897/108.
  Its three-equation system has degrees 2, 26, 288 in 95 operations, or 94
  after the justified positive transport shift.
- 14 positive integers: exact degree 52, 79 operations, versus 56/79.
- 15-positive short-circuit tradeoffs (operations/degree): 67/125, 68/101, 
  69/91, 70/84, 71/80, 72/74, 73/60, 74/50, 75/46.

The nine- and ten-variable main forms improve both degree and gate count
against the smallest-degree and cheapest relevant points in the newly
reviewed packets. Unknown counts are not new universal bounds. The inherited
66-operation degree 157 form remains the operation record, and the included
76/44 short form is explicitly historical, not new. There is no global
simplicity minimum claim.

For each validated equation on its stated domain, the ordinary mathematical
proof establishes in ZFC that absence of solutions is equivalent to Con(ZFC).
The proof uses identified inherited compiler and number-theoretic results.
It does not prove either consistency or inconsistency, supply a new
end-to-end Lean/Rocq certificate, or export an object-language ZFC derivation.

## Late parallel comparisons

Two releases arrived during packaging. See the final report section and
review/ for hashes and scoped checks. Combining Free Coordinate with our source
produced the recommended 1,910,404/473 nine-positive form, improving both
metrics over Separated Degrees' 2,628,944/499. Its ten-integer 8,317,400/544
remains a slightly lower-degree, higher-operation tradeoff against ours. Its twelve-positive 242/94 and 258/89 dominate our
316/102 point, which is retained as a distinct construction, not a current
record. Free Coordinate gives fifteen-positive 54/73 and 46/74, superseding
some short tradeoffs here. The earlier comparison is explicitly the pinned
46–53 snapshot, not a claim against these later releases.

The new thirteen-positive degree-126/91 equation is a lower-degree,
higher-operation tradeoff against the late degree-132/83 form.

## New structural ideas

1. Separate homogeneous degrees: G=D2 U²+D1 U+D0, rather than homogenizing
   everything with a dummy coordinate. Linear and quadratic labels may
   collide safely. Two elementary row operations reduce the source to 89
   records; 22,544 exact interactions certify 22 target identities. Source
   convolution height falls 5556→2161.
2. Combine that architecture with a shared positive-coordinate word,
   sparse borrow-tolerant padding and calibrated binary population.
3. Use exact CRT parametrization and positivity-first Pell separation for
   the nine-variable finalizer, then compose the late free-coordinate and
   shorter carry-block ideas to obtain the recommended adjunct.
4. Put the second radicand in a coprime guard factor, eliminating an
   unnecessary external weight in the thirteen-integer norm. The zero
   spectator branch is excluded by an ordered source-positivity bootstrap.
5. Retain the ordinary Pell root f instead of its multiplier. A weighted
   square-class argument and Pell saturation recover the omitted witnesses;
   an exact denominator-deflated norm gives degree 316 in12 positives.

## Coefficients and domains

The six initial families and the new nine-variable composition use the
WHOLE original source 31 Wang943 121x8801
native tuple: B_native=2^1064921, beta=B_native−1, K0=K, MC, MF=MF_source.
The high mask is already shifted. Four uncompressed payloads total 533,099
bytes. Sun/signed use source floor 2^2134940; the primary nine form uses
2^2134939 with its separately checked bounds. All additional fixed leaves
are literal integers specified by explicit recipes or fixed powers of two.

Nine's separately retained comparison circuits use a different, complete
packet52 tuple and presentation. Their bindings are explicit. No individual
port or transport row is spliced into the main tuple. In particular, the
475-operation degree9336884 comparison is a tradeoff, not the primary form.
The thirteen-positive adjunct instead retains the entire coherent late
590069-bit tuple, with its own binding and proof. No coefficient ports are
shared across these instances. No new coefficient-byte record is claimed.

## Reproduce without modifying the sealed release

Use Python 3.10+, NumPy and SymPy (tested with Python 3.12.14, NumPy 2.3.5 and SymPy 1.14.0):

    python verify.py
    python negative_controls.py

The root driver checks SHA256SUMS.json, copies the complete package into a
temporary directory, runs 25 stages, and compares every file listed in
REBUILD_FILES.json byte-for-byte. No network access is needed. Run the root
driver without -O. Nine's primary verifier deliberately rejects -O/-OO;
that rejection is a tested policy, not an optimized success claim. Its
separate independent checker works in both modes. Component receipts
clearly state what was run.

Ten source-certificate corruption tests are mathematical/data controls;
three root corruption tests are byte-integrity controls only. Neither is
misrepresented as an unbounded consistency proof.

Build the main PDF with a normal TeX Live installation:

    sh build_report.sh

build_sections.py creates layout-only copies under sections/, avoiding a
duplicate equation label and fitting one register matrix. Original component
TeX is not edited. SECTION_LAYOUT_MAP.json authenticates both versions and
states each layout change. PDF metadata may differ when rebuilt.

## Layout

- encoding/: canonical degree-separated code, kernels, proof and checker.
- sun/: ten-integer polynomial, explicit finalizer, proofs and fixed binding.
- nine/: initial nine-variable forms and clearly bound tradeoff comparisons.
- nine_free_adjunct/: recommended nine-variable composition with the late release.
- positive13_adjunct/: lower-degree thirteen-positive quotient tradeoff.
- signed/: coprime/CRT thirteen-integer forms, compact proof and audits.
- positive/: twelve-positive ordinary-root merger and systems.
- short/: audited short-circuit combinations and historical comparisons.
- root_checks/: independent cross-family and mathematical reviews.
- review/: pinned formal status and input-entry-point evidence.

The imported native compiler, K215 calibration and representation results
remain explicitly named dependencies. All inherited licenses and notices
are retained. Internal reviews are AI-assisted, not external human
endorsements. The source search programs are not part of the definition;
the explicit certificate and exact checker are sufficient.
