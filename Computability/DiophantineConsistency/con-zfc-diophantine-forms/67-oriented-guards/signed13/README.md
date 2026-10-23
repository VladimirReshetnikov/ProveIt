# Signed Jones composition on the split108 source

The active equation is generated/signed_coprime_compact_split_crt.json. It has thirteen unrestricted integer unknowns, exact total degree 10,461,744, and 519 binary arithmetic operations (327 multiplications,169 additions,23 subtractions). It improves the preceding degree11,543,632 construction at the cost of one additional operation. The mathematical proof uses the inherited Jones ratio interface, not the2026 Sun reduction. Lack of integer solutions is equivalent in ZFC to Con(ZFC), with the pinned compiler theorem and arithmetic interface explicitly retained as dependencies.

Run `python3 reproduce.py` to rebuild all emitted polynomial/degree/metric data byte-identically and run normal and optimized checks. `verify.py` uses an independent direct-formula replay, exact actual-coefficient leading-degree propagation, all source isolation identities, and inherited finite guard/CRT tests. It does not prove the imported unbounded compiler theorem or formalize the composite endpoint.

The full current proof is section.tex, rendered as report.pdf. The complete fixed tuple is in coefficients/. FIXED_BINDING.json is authoritative. All inherited source and ratio files are pinned by SOURCE_PINS.json. Only the compact split variant is emitted; upstream/PREVIOUS_SIGNED13_SECTION.tex is historical provenance, not the active source formula.

Important parity distinction: b=2epsilon^2 and Hpop2195 require Nhat=2^(17kappa/2-9)epsilon^3 B^1089. The earlier linear-epsilon threshold is not valid for this new source. The signed polynomial register N is used only through its square; the proof-side positive Jones parameter is abs(Nhat), not an extra circuit operation.

New contribution: lower global-sign source, off-target pad B^1946, explicit signed positivity proof, corrected cubic-epsilon calibration, and the resulting circuit. The coprime spectator/CRT finalizer and Jones theorem are inherited. No global minimality or operation-count record is claimed.
