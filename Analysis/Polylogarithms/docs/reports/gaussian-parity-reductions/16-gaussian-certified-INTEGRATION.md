# Integration map

## Source snapshot

Repository: `VladimirReshetnikov/ProveIt`

Commit: `0599fe867a0c7d0819b4e9f3cd92ce90a3b62b8d`

Source chapter:
`Analysis/Polylogarithms/docs/manuscript/chapters/04-depth.tex`

Chapter Git blob: `6171912ff7724784cabb789a066c61223ab298bc`

This bundle does not modify the repository. A possible destination for the
standalone report is `Analysis/Polylogarithms/docs/reports/gaussian-parity-certified/`;
that destination is a suggestion, not a claim that the folder already exists.

## Six proof-status upgrades

| Existing label | Source coordinate | Proof in this article |
|---|---|---|
| `gauss:eq:wt5-sporadic` | Weight-five four-coordinate relation | Theorem 5.2; generalized by Theorem 5.3 |
| `gauss:eq:g51` | `g_(5,1)` | Theorem 3.1; equation (4.1), with hand calculation |
| `gauss:eq:g42` | `g_(4,2)` | Theorem 3.1; equation (4.2) |
| `gauss:eq:g33` | `g_(3,3)` | Theorem 3.1; equation (4.3) |
| `gauss:eq:g24` | `g_(2,4)` | Theorem 3.1; equation (4.4) |
| `gauss:eq:g15` | `g_(1,5)` | Theorem 3.1; equation (4.5) |

Preserve the source coefficients: the exact checks find no correction to these
six equations. Change only their proof status and add the corresponding proof
or a precise reference to this report. The finite expressions are not period
independence assertions.

## Material suitable for incorporation

After the Gaussian candidate section, insert the endpoint-specialized parity
formula, Gaussian coefficient rule, and infinite odd-weight shuffle family.
Keep Panzer's attribution: his general parity theorem predates this work.
The crucial endpoint step combines the two `Li_b(y)` terms before taking
`y -> 1`, especially when `b=1`.

The moment expansion, explicit resonant formula, and error theorem belong near
the mixed-point evaluation section. They give a new certified alternative to
the historical numerical acceleration procedures; they do not invalidate the
existing exact Lerch correction identity.

The discovery chapter can link to the distinction between analytic proof,
exact symbolic specialization, interval residual enclosure, and numerical
independence. The optional editorial addendum is in
`integration/editorial-ledger-addendum.md`.

## Preserve the remaining conjectures

Do not promote `gauss:eq:S4-closed`. Its certified numerical residual is only
evidence. Likewise this report does not prove the Gaussian triple candidates,
the mixed-point quotient dimensions as numerical dimensions, or any assertion
of minimal depth. It does not re-prove or alter the source's already proved
infinite even-weight odd-denominator harmonic-sum reduction.

## Build and testing

Retain `article.tex`, `generated/`, `code/`, and `data/` together. The flattened
`article-standalone.tex` is a convenience copy, not a second independent source.
After editing a formula, run `python code/verify.py` and regenerate both TeX
forms before compiling. `make all` performs these steps. No external web or
repository access is needed for reproduction once dependencies are installed.

No change to the repository's license, citation conventions, or historical
source inventory is proposed. Do not describe the delivered implementation as
Lean/Rocq formalized or independently peer reviewed.
