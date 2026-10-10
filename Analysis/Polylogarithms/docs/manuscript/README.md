# Polylogarithms and their Arithmetic Bridges

The collective manuscript, authored by **ProveIt Contributors**, is [polylogarithms.pdf](polylogarithms.pdf):
**228 pages, twelve chapters**, a literature appendix preserving 94 distinct
historical question leads, and a central bibliography of 65 works. Its editable
source is [polylogarithms.tex](polylogarithms.tex) and the files in `chapters/`.

The book consolidates the original 39 drafts and all six nested continuation
packages in the requested directory. The recursive inventory covers **109
textual source files**; assembled articles and their fragments are provenance
files, not independent results. The [editorial ledger](EDITORIAL-LEDGER.md)
maps the sources and explains which later proofs replace earlier claims.
Original drafts, code, data and PDFs remain historical evidence. This book is
the canonical reading artifact.

The development follows mathematical dependency: conventions and Nielsen
calculus; cyclotomic coordinates; algebraic arguments and ladders; depth,
inverse-color reductions and harmonic sums; signed kernels and certified
computation; gamma certificates; CM lattices;
integrated zeta jets; differentiated jets and uniform distribution ranks;
Stieltjes zero geometry and spectral asymptotics; Herglotz arithmetic and
optimal truncation; and experimental discovery. Experiments motivate the
exact identities, rank proofs and analytic asymptotics, with proof status
stated at each transition.

The [validation report](VALIDATION.md) records fresh native Wolfram and
independent Python checks, exact rational certificates, the converged build
and rendered review. [WORKLOG.md](WORKLOG.md) records the completed integration.
Numerical period independence and minimal depth are not inferred from failed
searches. Gamma completeness beyond the stated relation system and Stark
regulator predictions retain their conjectural scope. There is no
proof-assistant formalization.

## Reproduction

From this directory, with LuaLaTeX, Python (mpmath, sympy, PyMuPDF and Pillow)
and Wolfram Language available:

```powershell
python verification/check_document.py
python verification/check_identities.py
wolfram -script verification/check-identities.wls
python verification/check_additional_corrections.py
python verification/check_nielsen_inversion.py
python verification/replay_ranks.py
python verification/replay_cyclotomic.py
python verification/replay_spectral.py
python verification/build.py
python verification/inspect_pdf.py --render-directory C:/path/to/local/review
python verification/verify_receipts.py
```

`build.py` runs three serial LuaLaTeX passes. The committed hash receipts pin
the reviewed PDF: a rebuild may differ in binary metadata and requires its
own rendered review. `verify_receipts.py` checks the committed evidence; it
does not rerun mathematics or confer review on a changed artifact. Additional
continuation replays and their exact configurations are listed in
[verification/REPRODUCTION.md](verification/REPRODUCTION.md). Every replay
uses a separate manuscript output directory, preserving historical receipts.
