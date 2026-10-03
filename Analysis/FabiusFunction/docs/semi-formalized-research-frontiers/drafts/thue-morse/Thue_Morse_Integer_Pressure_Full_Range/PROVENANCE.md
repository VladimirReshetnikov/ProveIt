# Provenance and scope

Date: 1 October 2026

The theorem concerns the local integer Thue–Morse pressure in the normalization

    p_m(t/pi) = 2m log cos(t) + log lambda(tan t).

The main result proves strictly positive coefficients at every even degree N with 2m<N<6m, for every integer m>=2. The lower endpoint is a cancellation coefficient. The upper endpoint cannot be included universally, because m=2 gives the negative coefficient -35360872/93555 at degree 12. No claim is made about the sign at degree 6m for every m, or about a first-negative-degree asymptotic law.

The analytic argument improves the weighted source estimate on the same complex disk as the earlier large-order report. It proves m>=112. Exact integer enclosures and a separate a posteriori Fourier residual calculation complete m=2,...,111. The complete finite proof certifies 12,320 coefficients. It is a finite arithmetic proof, not a sample extrapolation.

## Repository normalization

The inspected source was the ProveIt manuscript “Integer Pressure and a Missing Taylor Coefficient,” at commit

    6a98f89bac85cc6b4ba5d5c3b63996037d9824e1

and Git blob

    1973fd17245864bb8a83e1b1d90416ac032ba7c1.

Its unchanged copy is `inputs/repository_integer_pressure.tex`. The versioned source link is

https://github.com/VladimirReshetnikov/ProveIt/blob/6a98f89bac85cc6b4ba5d5c3b63996037d9824e1/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/Thue_Morse_Integer_Pressure/article.tex

The preceding “Full Positive Triangle” note is included unchanged as an explicit mathematical input for the dyadic tangent comparison and the pre-feedback range. Other previously delivered reports remain unchanged.

## Exact finite producers and verification

The producer used for all 110 orders is `finite/producer_v1.cpp`, SHA256

    468c876891c1ab58cc756cd16e63143cf3209a48aaf459572db868e178392109.

The guarded variant differs only by explicit domain checks; both versions and the m=2 bitwise trace comparison are recorded in `finite/producer_versions.json`. The independent C++ residual verifier has SHA256

    4036953bf457cc17f22c4fd577b2535dbbc186580e9671a8809d27b1dd3d5a4d.

The full independent reference manifest has SHA256

    ff438fd49c36c8b4c2e37f45644e7f187742cc651ea71147628f579d63cde79d.

The reference manifest links original pressure data, full traces, fresh residual radii and fresh pressure outputs. Its recorded binary hash is platform-specific; the source and arithmetic define the reproducible proof. Runtime fields may vary. To compare regenerated numerical results without runtime fields, `finite/independent_numeric_index.json` hashes the canonical pressure-bound arrays and the deterministic compressed fresh-radius records.

Each canonical full-state hash is SHA256 of the decimal fields joined by one space. The state includes its order, vector error radius, scalar center, scalar radius, and every independent Fourier coordinate. The exact scale and parity inverse norms are retained in each index. The original full traces total about 2.1 GiB and can be regenerated; the supplied small source and interval archives avoid duplicating them.

The finite producer and independent verifier use only integer and rational arithmetic for the proof. Floating values occur only in progress timings. The scalar interval checkers use the Python standard library. C++ replay requires standard GMP and zlib development libraries. No software installation is performed by the supplied programs.

This is unrefereed ordinary mathematics with computer-assisted exact certificates, not a Lean formalization. No claim of publication priority is made. The stronger raw frozen-tail inequality remains open.
