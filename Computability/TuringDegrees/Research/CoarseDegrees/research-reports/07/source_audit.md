# Source audit and research-status boundary

Audit date: 18 September 2026 (America/Los_Angeles).

## Supplied source

`/mnt/data/turing_degrees_unified.tex`, 1,773 lines in the uploaded source.
The relevant material is C1 and the following coarse-spectrum diagnostic
lemmas (source lines 494–558). The input was read directly; it was not
silently replaced by a generic list of computability problems.

## Primary public sources checked

1. Peter M. Gerdes, *Comparing Notions of Dense Computability on omega^omega
   and 2^omega*, arXiv:2508.06925v1.
   - Abstract and submission history: https://arxiv.org/abs/2508.06925
   - Full text: https://arxiv.org/html/2508.06925v1
   - PDF: https://arxiv.org/pdf/2508.06925
   - Exact target: Question 7, PDF page 64 (zero-based page index 63).
   - The recorded submission is 9 August 2025; only v1 was displayed.
   - The question explicitly includes a least Turing-degree representative
     in each nonuniform coarse class, alongside other variants.

2. Denis R. Hirschfeldt, Carl G. Jockusch, Jr., Rutger Kuyper, and Paul E.
   Schupp, *Coarse Reducibility and Algorithmic Randomness*.
   - Abstract and submission history: https://arxiv.org/abs/1505.01707
   - Full text: https://arxiv.org/html/1505.01707
   - The status-relevant result is Theorem 4.2.
   - The arXiv submission is 7 May 2015. The HTML rendering's regenerated
     internal date must not be confused with the original submission date.
   - Author's publication record:
     https://www.math.uchicago.edu/~drh/Papers/coarsereducibility.html
     records Journal of Symbolic Logic 81 (2016), 1028–1046.

The available PDF displays were inspected during the source audit; source
numbering was not inferred from search snippets alone.

## Conclusions justified by the audit

The negative coarse answer to C1 follows from the older theorem and the
short implication explained in Section 1 of the report. It is not claimed
that the older paper used C1's exact later wording. No speculation about the
reason for the later question is necessary.

The weighted minimal-pair theorem is proved independently in this report.
Its proof does not use Theorem 4.2, a randomness theorem, or an imported
minimal-pair construction. However, independence of the presented proof is
not evidence of historical novelty. Targeted searches did not establish
priority for this formulation, the bridge argument, or the relative
infimum result. No exhaustive novelty certification is claimed.

The effective-dense version and a general classification of representative
spectra are outside the conclusions of the proof. Questions suggested at
the end of the report are research limits, not a certified list of newly
open problems.
