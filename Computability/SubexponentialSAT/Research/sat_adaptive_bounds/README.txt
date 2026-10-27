ADAPTIVE CONTRACTION BEYOND THE OCTOBER 26 SAT FRONTIER
Research prepared for Vladimir Reshetnikov
Task date: October 26, 2026 (Pacific time)

RESULT

Three new leading-coefficient bounds improve the strongest explicit
comparable contraction certificates in the twenty reviewed packets.
All coefficients multiply s/sqrt(log2 s) in a base-two exponent, where
s is the normalized Boolean-wire budget.

1. General degree <= ceil(s^(9/10)), polynomial space:
   time coefficient 55.709478318910 -> 46.184845586731.

2. General degree <= ceil(s^(9/10)), cached:
   time coefficient 35.354588058401 -> 34.325282797285.
   New space coefficient 34.024178007491.

3. Root degree <= ceil(s^(1/12)), cached:
   time coefficient 15.3919331988 -> 13.379649066270.
   New space coefficient 13.253024933008.

Safe eventual coefficients are respectively 46.19 (polynomial space),
34.33 time / 34.03 space, and 13.38 time / 13.26 space.

The new mathematics is:
- Adaptive streamed separators selected from complete binary linear flags.
- A centered entropy estimate for an adaptive triangle partition, combined
  with recursively constructed group tables and paid child evaluations.
- Complete compatible integer/rational schedules.

SCOPE

These are mathematical refinements relative to the imported exact
contraction identities. The worst-case SAT order remains
poly_k(n,m) * 2^O_k(n log log n / sqrt(log n)).
The conditional n log log n / log n target remains unproved.
There is no end-to-end SAT solver, practical SAT speedup claim, or new
Lean/Rocq formalization in this packet. Finite checks supplement the proofs;
they do not independently verify the full upstream ETH claim.

REVIEW

Initial repository snapshot:
fd0edd17e6a29117179b40a453c0def59165bd7c

Closing snapshot:
dde01c4a63b822c25b8eb345299346c36f837b49

Placement commit reviewed at closing:
450252e9d86c155f188b485629b9755c5c665371

The initial fifteen filed packets and five incoming archives were reviewed.
At closing, the five archives had been filed under Research/. All 230
members match the reviewed archive bytes by Git blob SHA. The prior report
contents are unchanged; two replay scripts were restored and the omission
ledger corrected. See provenance/ for exact source identities.

CONTENTS

report/report.pdf        Complete mathematical report.
report/report.tex        Main LaTeX source; all included sections are supplied.
code/                    Standard-library finite mathematical checkers.
results/                 Normal and optimized verification outputs.
audit/                   Independent proof and arithmetic review.
provenance/              Source hashes, arrivals, closing relocation check.
PROOF_STATUS.json        Machine-readable new/imported/unproved claims.
INTEGRATION.txt          Suggested repository placement and summary wording.

REPRODUCE

On the untouched extracted archive:
    python3 verify_manifest.py

Run both checkers, normally and under python -O:
    python3 run_checks.py

Build the PDF (requires pdflatex and standard TeX Live packages):
    python3 build_report.py

The checks require only Python 3 and its standard library. The checker
results are exact except explicitly labeled decimal/timing display fields.
Normal and optimized mathematical results are compared automatically.
Rerunning timed checks or rebuilding the PDF can change the delivered hashes.

No upstream manuscript binaries or input ZIPs are duplicated here.
No remote repository changes were made by this research run.
