# Main-factor norm from the direct-main draft

`DirectMainMain.lean` works in every IΣ₁ model with the stated ordered-ring interface. For arbitrary natural ports and valuation, an internal zero of the exact draft output implies an internal zero of its main residual and then the scaled norm

`magnitude(D)² = U²*(1+(H+a²)*c²)`,

where `q=1+J*beta`, `X=q*w`, `Y=q³*s`, `U=Y*q²`, `k=eta+zeta`, `c=eta+Y*k`, `a=X*Y+Y`, and `H=3+4*a`. `D` is the signed pair obtained by evaluating the exact main-root expression `mainParts`; the Lean source contains its full definition. This requires no old 95-graph zero, fixed ports, or positivity. It does not yet identify `D` with the ordered positive/negative pair used by `DirectMainNorm.direct_main_orientation`; that identification and its first-factor bounds remain open.

`run-main.py` produced `observations/main-attempt01/` with exit 0 and no reported warnings. The source locally suppresses `linter.unusedVariables` and `linter.unusedSimpArgs`, so those lint classes were not checked. Source SHA-256 is `a3aa8b924dd535be3cc4ff71f8de3f441287a843c82b46af38b6864347845234`, and the output object is `61ff9f8218a430bc84fc39399f3ee1421c267d42c0a1a7e6cbc40f066048d17d`. Both printed theorem axiom reports list `propext`, `Classical.choice`, and `Quot.sound`. The draft graph and XQ91 producer objects and the selected 1,291-object union were pinned and rechecked; package, dynamic, and source-to-object ancestry are inherited rather than freshly rebuilt. Resource samples and command details appear in the receipt, and temporary paths may disappear.
