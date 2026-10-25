# Eleven-integer product carrier, degree648 /115 gates

The primary `weak_product11_none.json` strictly improves the recovered degree654/117-gate equation in both metrics, using the same eleven unrestricted integer variables and six authenticated source34 numeral payloads. Three audited comparison equations640/118,580/119,574/122 are also retained. Those comparisons are dominated by other recovered frontier equations and are not claimed as advances.

The new mechanism combines one-product square-root saturation with an amplified scale carrier. Soundness derives carrier integrality before early main-root folding, explicitly closing the weak Y=0/A=2 branch. Completeness fixes the guard and then one strong pair before selecting the intersective residue, using the retained supported-modulus theorem.

Reproduce offline with Python3 standard library only:

    python build.py
    python check.py
    python -O check.py

`PROOF.md` is the full ordinary proof and named dependency ledger. `section.tex` is report-ready. `CHECK.json` and `CHECK_OPTIMIZED.json` contain all free-ring bindings, exact leading-coefficient certificates, source authentication and negative controls. The checker does not import the builder and rejects a mutation at every arithmetic gate. Coefficient payloads and their reconstruction recipe are included. All unbounded inherited dependencies are copied and pinned.

No proof of consistency, new ten-variable construction, global optimum, encoded object-ZFC derivation or new end-to-end proof-assistant certificate is asserted.
