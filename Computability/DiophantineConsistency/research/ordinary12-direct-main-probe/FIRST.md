# First-factor norm from the direct-main draft

`DirectMainFirst.lean` works in every IΣ₁ model with the stated ordered-ring interface. For arbitrary natural ports and valuation, an internal zero of the exact draft graph output implies an internal zero of its first residual and then the exact first scaled norm

`magnitude(Z)² = b²*(1+ell*(ell+k))`,

where `b=J*beta`, `q=1+b`, `X=q*w`, `Y=q³*s`, `k=eta+zeta`, and `ell=(X*Y)*(Y*k)`. `Z` is the signed pair obtained by evaluating the exact first-root expression `firstParts`; the Lean source contains its full definition. This result requires no old 95-graph zero, fixed ports, or positivity. It does not yet extract a quotient or prove the rest of graph soundness.

Attempts 01 and 02 failed because required import namespaces were missing; their exact source snapshots, errors, and terminal observations are retained. Attempt 03 passed with no reported warnings; the source locally suppresses `linter.unusedVariables` and `linter.unusedSimpArgs`, so those lint classes were not checked. Its source SHA-256 is `8dc77d35d1727e1228a015bc6e9494bc4c155666474a4103b0a1f650f5ce107d`, its output object is `e24c62d66d61d09135adf82c0b3d6b9b7297fcdffddbc0582fab10dbcb35b257`, and both the draft graph and XQ91 producer objects were pinned and rechecked against their accepted hashes. Both printed theorem axiom reports list `propext`, `Classical.choice`, and `Quot.sound`. `run-first.py` used the unchanged selected 1,291-object union; package, dynamic, and source-to-object ancestry are inherited rather than freshly rebuilt. Resource samples and all command details appear in `observations/first-attempt03/terminal.json`; temporary paths may disappear.
