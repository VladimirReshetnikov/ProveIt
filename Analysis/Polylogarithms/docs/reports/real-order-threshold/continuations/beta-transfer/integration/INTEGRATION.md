# Additive integration notes

## Destination

Keep this report intact under
`Analysis/Polylogarithms/docs/reports/beta-transfer-critical-euler/`.
The original threshold source is a preserved historical artifact; do not edit
it in place solely to change a conjecture's later status.

## Proposed manuscript changes

1. Add a cross-reference from the signed-kernel / real-order discussion to the
   new report. The fragment `05-beta-transfer-fragment.tex` uses only labels
   prefixed `betatransfer:` and can be inserted near the critical-line Euler
   material after editorial review.
2. Update the **current** conjecture ledger: predecessor label
   `conj:constant` (Conjecture 12.3, sharp critical Euler constant) is proved by
   the new order-transfer theorem and critical-error argument.
3. Extend the evaluator domain to all positive orders only with the new
   positive divided-difference proof. A signed moment representation must not
   be asserted below `a+b=1`.
4. Add the density cancellation and uniform asymptotic result to the analytic
   continuation / error analysis discussion. Record the N=8 counterexample
   beside any stronger error-monotonicity speculation.
5. Add the rational-profile formula to the integration identities chapter,
   explicitly keeping repeated-pole `Li_{w-1}` terms. The formula evaluates a
   profile, not its beta average.

## Status and correction discipline

No false central theorem was found in the inspected threshold report. These
are a conjecture resolution, extensions, and precautions against invalid
extrapolation. Preserve the proved status of S4 and the unresolved status of
S6. The new proofs do not settle angular uniqueness below the threshold or
period independence.

A bibliographic update is appropriate for Liu–Pego's 2026 corrigendum (DOI
10.1090/tran/9582, TAMS 379, 3009–3010). It corrects a Fuss–Catalan theorem not
used in this report; it is not evidence of an error in the present elementary
moment arguments.

## Fragment dependencies

The fragment expects `amsmath`, `amssymb`, `amsthm`, and existing `theorem` and
`proof` environments. It introduces no global macro names. Its proof is a
compact integration summary; the self-contained full arguments remain in
`article/beta_transfer.tex`. Add a bibliographic entry for that article in the
collective manuscript's own bibliography and replace the textual report
reference according to the manuscript's citation conventions.

No upstream file or branch was modified by this delivery.
