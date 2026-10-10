# Label-anchored integration plan

Base inspected: `a2a4cf58c49c745058c40e4a6748d472a3420f18`.
These files are a proposed integration package, not a remote commit.

## Suggested destination

Place this continuation under
`Analysis/Polylogarithms/docs/reports/cayley-s4-continuation/`.
Keep the article, JSON certificate, both verifiers, and the rational interval
receipts together. The numerical discovery files are historical evidence,
not proof premises.

## Canonical manuscript changes

1. In `chapters/04-shuffle-parity.tex`, replace the entire subsection beginning
   `\subsection{The surviving mixed relation}` and ending just before the
   following self-contained-section comment / parity section with
   `04-cayley-s4.tex`. The replacement intentionally preserves these labels:
   `gaussian:eq:S-mixed`, `gaussian:conj:S4`, `gaussian:eq:S4-short`, and
   `gauss:eq:S4-closed`. Do not insert the replacement alongside the old
   subsection, or duplicate labels and contradictory status statements result.
2. Add `bibliography-entry.tex` inside the central `thebibliography`
   environment, and add its final repository-relative report location after
   integration. The legacy label containing `conj` can stay for link stability.
3. In `chapters/04-depth.tex`, locate the Family 2 paragraph anchored by
   `double:eq:fam2-example`. Replace the unqualified statement that higher-weight
   antisymmetric parts do not reduce in the `(i,1)` basket with the empirical
   wording in `CORRECTIONS.md`, and cite `cayley:eq:mixed-antisymmetric`.
4. In `chapters/10-discovery.tex`, remove this S4 identity from the list of
   unresolved formulas. The S6 relation in the new article remains conjectural.
5. Record the two exact word replays and all three rational interval replays
   in the manuscript's validation ledger. Do not overwrite prior receipts.

## No over-extension of the change

Do not claim numerical independence, minimal depth, completeness of the
standard relation ideal, a proof of S6, or an all-even-index theorem.
The rejected S8 vector belongs only in a numerical-method warning, not among
conjectures. The Cayley map and Euler transformation are established tools;
the new project result is the concrete S4 certificate and its consequences.

## Validation before merging

Run the exact checks from the continuation root, then rebuild the manuscript
and inspect the resulting PDF. The article's visual-review receipt does not
cover the rebuilt collective manuscript. The proposed fragment was also
compiled in an isolated article wrapper, but that is not a test of every
macro or cross-reference in the full current book.
