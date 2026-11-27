# Universal prime fingerprints at list-decoding capacity

Research packet, 27 November 2026. The main result uses Dirichlet GRH as exported by the supplied Lean project; the information-theoretic converse is unconditional. See the paper for hypotheses, proof, bounds, and limits. The prime list may be selected by weighted sampling without replacement; the proof gives a probability of success tending exponentially to one in the list length. The new theorem is not Lean-formalized or independently refereed, and the upstream proof was not rebuilt here. The novelty claim is a candidate, not a certified literature-priority claim.

## Contents
- `prime_fingerprint.tex`, `prime_fingerprint.pdf`: research note, LaTeX source and compiled PDF.
- `check_fingerprints.py`, `example.json`: exact finite enumeration with wildcards and adversarial errors and erasures. It checks a small instance, not the asymptotic theorem or GRH.
- `SOURCE_NOTES.md`: GitHub provenance, statement dependency, and formalization roadmap.
- `SHA256SUMS`: digests of the deliverable files.

## Reproduce
In this directory:
```
pdflatex -interaction=nonstopmode -halt-on-error prime_fingerprint.tex
pdflatex -interaction=nonstopmode -halt-on-error prime_fingerprint.tex
python3 check_fingerprints.py > reproduced.json
cmp reproduced.json example.json
sha256sum -c SHA256SUMS
```
The Python program uses only the standard library. It accepts `--help` for parameters; exhaustive enumeration scales exponentially in the requested sample length and errors. The default random seed generates a fixed prime list, which is independently verifiable by the exhaustive loop.
