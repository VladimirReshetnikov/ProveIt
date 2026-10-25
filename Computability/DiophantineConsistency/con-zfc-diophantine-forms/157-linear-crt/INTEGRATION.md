# Suggested ProveIt integration

The archive can first be placed in docs/incoming under its delivered name,
ConZFC_Linear_CRT_2026-10-25.zip. An extracted contribution may live in a
new linear-crt-semantic-radix directory beside the current reports.
No numerical package prefix is assumed.

Review the arithmetic proof in report/report.pdf or proofs/MAIN_PROOF.md
before treating a finite checker receipt as evidence for the unbounded
consistency statement. The proof's crucial order is:

    even F and C -> nonzero B -> nonunit BH -> x and q
    -> y from the q^(y+1) request -> large x
    -> representative signs -> first binomial digit -> B>0 and q>0.

The new F=t^t choice requires the sharpened label lemma; the parent's
stronger hypothesis F>(t+1)^t is not applicable.

The three final profile directories are self-contained polynomial data.
Keep source/, code/, proofs/, review/, and the inherited source closure
with them so that the exact calibration and transformations remain
reviewable. SOURCE_LEDGER.json pins the compared repository and incoming
archives. The final coefficients are ordinary small integers, not large
native-machine coefficient ports.

Recommended finite acceptance:

    python3 -B verify.py --rebuild --receipt ../integration_check.json
    python3 -B -O verify.py --receipt ../integration_check_optimized.json

The first reconstructs the source and final coefficient files byte for
byte. Both check the actual printed principal polynomial and recollect
the predecessor metrics. The reproduction does not require network
access or a parent repository checkout.

Formalization can proceed as separate lemmas: label multiplicity at
F>=t^t; the elementary LCM upper bound; the signed bootstrap with a
nonunit residue class; and constructive parity-compatible CRT completion.
The inherited numerical calculus and logical interface names are listed
in SOURCE_LEDGER.json.
