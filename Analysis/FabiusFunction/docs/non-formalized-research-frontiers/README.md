# Non-formalized Fabius research frontiers

This directory is the quarantine boundary for mathematical claims about the
Fabius function and Rvachev's up-function that do not yet have an exact,
audited Lean theorem covering their full hypotheses and conclusions.

The authoritative artifacts are the standalone LaTeX/PDF dossiers in the
subdirectories below. They remain separate so that each document can be
audited, promoted, rebuilt, and cited without copying a stale snapshot into a
second monolithic source.

- [Fabius_Dyadic_Asymptotic_Bridge](Fabius_Dyadic_Asymptotic_Bridge/)
- [Fabius_Dyadic_Formulae_and_Alternative_Representations](Fabius_Dyadic_Formulae_and_Alternative_Representations/)
- [Fabius_Dyadic_Formulae_to_Asymptotics](Fabius_Dyadic_Formulae_to_Asymptotics/)
- [Fabius_Dyadic_q_Connections](Fabius_Dyadic_q_Connections/)
- [Fabius_Integration_Research_Frontiers](Fabius_Integration_Research_Frontiers/)
- [Fabius_Inverse_and_Saddle_Research_Frontiers](Fabius_Inverse_and_Saddle_Research_Frontiers/)
- [Fabius_Thue_Morse_Convergence_Rate](Fabius_Thue_Morse_Convergence_Rate/)
- [Fabius_Thue_Morse_Convergence_Rate-2](Fabius_Thue_Morse_Convergence_Rate-2/)
- [Repeated_Integration_and_Rvachev_Up](Repeated_Integration_and_Rvachev_Up/)
- [Rvachev_Up_from_Repeated_Integration-2](Rvachev_Up_from_Repeated_Integration-2/)
- [Small_Argument_Asymptotics](Small_Argument_Asymptotics/)

The
[Primary_Exposition_Gap_Register](Primary_Exposition_Gap_Register/)
is a compact disposition record for smaller claims removed from the primary
exposition. It records the missing Lean obligation and the source provenance;
it is not itself evidence that a claim has been formalized.

Some passages in a frontier dossier may use already-formalized results as
inputs. That does not certify subsequent deductions. Conversely, once a
particular claim is promoted to the primary exposition, adjacent exploratory
material can remain here if it is still clearly labeled and still has an open
formal obligation.

## Placement and promotion rule

A mathematical claim belongs in the primary exposition only when a current
public Lean declaration proves the exact statement, including its domain,
normalization, hypotheses, endpoint convention, and conclusion or error term.
The declaration and its defining module must be recorded next to the claim or
in the primary document's audit map.

A related definition, a theorem with stronger hypotheses or weaker
conclusions, an executable computation, a paper citation, a numerical match,
an .olean file, an agent report, or an apparently immediate derivation is not
an exact counterpart. Material supported only in one of those ways stays in
this directory, however standard or plausible it appears.

Promotion is claim-by-claim:

1. verify the exact Lean declaration in current source;
2. integrate the supported material organically into
   [Fabius_Function_and_Rvachev_Up.tex](../Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex)
   without duplicating material already there;
3. remove or mark the matching frontier obligation as discharged while
   preserving any adjacent claims that remain unformalized;
4. rebuild and inspect every affected PDF.

Research drafts are temporary inboxes, not archives. Once every part of a
draft has either been integrated into the primary exposition or preserved in
an appropriate frontier dossier, delete the processed draft. Delete the draft
directory itself when it becomes empty.

## Maintenance

Every mathematical dossier remains a LaTeX document in its own directory, with
a committed PDF of the same basename. Build an affected document with exactly
three pdflatex passes, inspect the rendered PDF, and commit the PDF with its
source. Do not commit .aux, .log, .out, .toc, or rendered page images.

When formalization work discharges a frontier obligation, update the
standalone dossier directly. Do not maintain copied or concatenated snapshots:
they drift as soon as one source is corrected and can misclassify proved
results as open research.
