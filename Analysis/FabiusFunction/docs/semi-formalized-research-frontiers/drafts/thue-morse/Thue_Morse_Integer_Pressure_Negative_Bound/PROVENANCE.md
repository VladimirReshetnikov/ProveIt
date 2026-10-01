# Provenance

Prepared for Vladimir Reshetnikov with OpenAI on 1 October 2026, as a separate continuation of the delivered integer Thue–Morse pressure reports. All input reports remain unchanged.

The repository source is pinned at commit 63a7a325109ba611a1816b61dfd0eb072b896a7a, Git blob 1444c01b4b30020f727172f0ee0060cab644f444:

https://github.com/VladimirReshetnikov/ProveIt/blob/63a7a325109ba611a1816b61dfd0eb072b896a7a/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/Thue_Morse_Integer_Pressure/article.tex

The preceding all-integer-orders PDF has SHA256 5fd05b33da4b4cf3af2f8bc75ef7129095522306eebfa394a3fa4262c72501f7. Its unchanged source archive has SHA256 1c5323125ff09a2e95e6e0d6102488e571099a96c0c7e02da740664de4729f9a. Its Sections 2, 4, and 5 supply the low-degree orbit comparison, weighted C1 Green estimate, and weighted residual used here. The original finite certificates are inputs only to its already established all-m theorem below 6m.

The infinite-sign PDF has SHA256 c7b3bc8b25e593fe1f8f775acddea0a5ddf36445682ae38901a51b0dd33a4e26. It guarantees existence of a negative coefficient above 2m and is not used in the positivity estimate itself.

The new ingredients are the third-Schur-cluster expansion and logarithmic-squared envelope; the full-disk quadratic bound through the C1 Green inverse; and the exact scalar separation on the compact slope interval [3, 3.3]. Uniform lattice local-limit methods and the elementary analytic tools are classical. No global priority claim is made.

The interval helper was copied from the preceding scalar-verification implementation. Its two positivity preconditions were changed from Python assertions to explicit exceptions. The new checkers likewise use explicit exceptions, with no external dependencies or network calls. All package-level content identities appear in SHA256SUMS.
