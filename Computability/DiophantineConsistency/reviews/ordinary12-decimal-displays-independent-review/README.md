# Independent review of the 94- and 95-operation decimal displays

The reviewed versions pass the external transcription and arithmetic checks
below; no equation or coefficient mismatch was found. The review covers the
pinned artifacts in [`terminal.json`](terminal.json) and
[`independent.stdout`](independent.stdout), not arbitrary later revisions.
It is not a Lean proof about files or an iPRA derivation.

The independent [`audit.py`](audit.py) parses every `let` row in the pinned
95-operation Lean source and checks the 95-row JSON. It checks the 94-row
JSON's 89 shared rows and its exact five-gate sum-of-squares tail. It checks
all twelve typed variable indices and four port indices, reconstructs each
TeX operation from the corresponding graph, checks every PDF-extracted
operation, verifies the declared positive-variable domain and final equation,
and independently traces all 94 and 95 operation nodes to the respective
outputs. The `rNN` names are evaluator abbreviations; only `a`–`k` and `ℓ`
are unknowns. As a possible clarity improvement, the display could explicitly
say that intermediate rows use integer subtraction and may be negative.

For each display the audit compares all 943 printed 14-digit selectors,
in order, to the table computed from the 943 ordered rows in the pinned Lean
source, and compares all 41 printed slots to the pinned list source. It checks
the displayed TeX coefficient formulas and computes their integers from the
printed selectors and slots. All four computed integers agree in their
entirety with the little-endian gzip payloads, including the once-shifted
`MF_source`. This is an external source/bytes comparison: it does not turn
JSON, TeX, PDF, gzip, or file bytes into a Lean theorem. Separate work
records the relationship of these Lean recipes and the represented machine.

Both PDFs have four US-letter pages. I visually inspected both graph pages
and the 94-PDF constant and table pages, including the beginning and end of
the selector list. `pdftotext -bbox` places every extracted word within its
page with minimum reported margin 28.028 points in each PDF. This is a
finite rendering check, not a general guarantee about every PDF viewer or
all graphical objects. Because Poppler emits a control character for a
math delimiter, the bbox XML check discards XML-invalid control characters;
it does not use extraction to verify mathematical formula layout. The
formula page was visually inspected, while the full formula text is checked
in TeX.

The previously checked model bridge relates the 94 square expression and
95 literal at the same valuation in IΣ₁ models, and has positive and shifted
model-level equivalences. Its closed byte recipes are Lean expressions, not
filesystem data. The separate [94-candidate independent review](../ordinary12-sum-squares-independent-review/README.md)
records its exact hypotheses and provider limitations. A model equivalence
is not by itself an iPRA derivability theorem, and no coherent compact iPRA
endpoint, full inherited-object ancestry, formal file/PDF binding, proof of
consistency, or global optimality is established here. The 94/95 operation
counts refer to the positive-coordinate DAGs; a representation which counts
additional `x+1` shifts needs a separate count.

`python3 -I -S -B run.py` ran the independent audit and repeated the author's
94 and 95 external checkers, each with exit 0 and empty stderr. The runner
captures source hashes before and after the calls. It does not compile Lean
or rebuild the PDFs. The result is in [`terminal.json`](terminal.json), and
the corresponding full outputs are [`independent.stdout`](independent.stdout),
[`author94.stdout`](author94.stdout), and [`author95.stdout`](author95.stdout).
Sampled source/output hashes are:

- `audit.py`: `fd042358292ca18ae3cc3ac72ae79616da80c2a9ff5b622cbf9eaf4447fb5919`
- `run.py`: `b8eb94748236c4ba506538fea7b68be34dfaa6256487299d9fd2e346cf02d8e8`
- `independent.stdout`: `b2fb6d748759289bf87714b353fadc8510ee7316e0a920d20c5649ccb178ee52`
- `terminal.json`: `fe1e52fc54890e4576cc71f3176671613c2447c6fd4a6e401860a3dee63833de`
