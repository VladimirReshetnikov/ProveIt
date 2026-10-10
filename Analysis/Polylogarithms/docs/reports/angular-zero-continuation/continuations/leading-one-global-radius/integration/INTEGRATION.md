# Additive integration plan

Source pin: `1539f353af88bdfd63292bb970ac8f585b15794d`.
The target section was confirmed at this pin; other source files are
identified by the inspected blob IDs in `PROVENANCE.json`.

## Main manuscript

Place `05-leading-one-global-radius.tex` in
`Analysis/Polylogarithms/docs/manuscript/chapters/` and add this line to
`chapters/05-certified-computation.tex`, immediately after the existing
input of `05-real-local-radius`:

```tex
\input{chapters/05-leading-one-global-radius}
```

All new labels have prefix `lone:`. The fragment uses the existing theorem,
lemma, corollary, remark, and proof environments and the existing `\Li`
operator. It introduces no global command definitions. It includes the
complete Green-density, strict-mode, reflected-sign, and implicit-radial
proof needed for the main theorem.

In `05-real-local-radius.tex`, preserve the existing coefficient formula
and its proof. Add a status sentence along these lines:

> The full-radius branch at a=1 is proved in Theorem
> `lone:thm:global-radius`; the results below at larger outer orders retain
> their independently stated scope.

Adjust the closing discussion so that it no longer leaves the entire a=1
branch open. Do not change the status of other outer orders, the fractional
quartic problem, S6, or S8 on the strength of this delivery. Check the latest
incoming packages before assigning a residual open range in other parameters.

## Two notation repairs, separate from the new result

In the proof of the Hurwitz--polylogarithm transport theorem in
`05-real-positive-kernel.tex`:

- Replace `with $q=n$` by `with $x=n$`.
- Replace `boundedness of $h$` by `boundedness of $q$`.

These changes repair argument/kernel names, not the identity. They may
already be tracked in incoming work; no first-discovery claim is made.

## Historical report placement

Retain `article.tex`, `article.pdf`, the verification scripts, and received
JSON evidence together under the appropriate thematic report destination.
Follow the repository's existing incoming intake procedure. This package
has not changed the remote repository or retired any incoming archive.

The general Green/Student theorem, global outer cutoff, shifted-order
sectors, complete odd-moment inequalities, radial-curvature counterexample,
and inner-order generating identities appear in the standalone article.
They can be integrated separately after review rather than inserted as
unsupported theorem summaries.

## Replay and evidence

Run scripts into fresh output directories, not over the received receipts.
`verify_exact.py` is standard-library-only. It verifies rational enclosures
of selected fractional powers by integer-root inequalities, and then verifies
both signs and the infinite tail bound for each root bracket. Finite tests
are not substitutes for the universal analytic proofs. No proof-assistant
formalization or exhaustive incoming-archive audit is claimed.
