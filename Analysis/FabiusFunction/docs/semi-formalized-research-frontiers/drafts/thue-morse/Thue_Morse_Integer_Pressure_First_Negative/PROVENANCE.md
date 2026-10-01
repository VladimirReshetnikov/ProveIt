# Provenance and scope

Prepared for Vladimir Reshetnikov with OpenAI on 1 October 2026. This report is a new continuation; the included earlier reports are unchanged.

The repository manuscript is pinned at commit 63a7a325109ba611a1816b61dfd0eb072b896a7a, Git blob 1444c01b4b30020f727172f0ee0060cab644f444:

https://github.com/VladimirReshetnikov/ProveIt/blob/63a7a325109ba611a1816b61dfd0eb072b896a7a/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/Thue_Morse_Integer_Pressure/article.tex

Unchanged input identities:

- All-integer-orders PDF: 5fd05b33da4b4cf3af2f8bc75ef7129095522306eebfa394a3fa4262c72501f7
- All-integer-orders source ZIP: 1c5323125ff09a2e95e6e0d6102488e571099a96c0c7e02da740664de4729f9a
- Eventual6.6m PDF: fd7d6b28457945615e165e91dc66f77d1efd690a051372cd8f277807695e19c7
- Infinite-sign PDF: c7b3bc8b25e593fe1f8f775acddea0a5ddf36445682ae38901a51b0dd33a4e26
- Independent outer-certificate ZIP: 9bd6a8bcaa7014d0f48760d5d853056377e277195cb4b2a6d5022c6192608275

The new mathematical chain consists of the logarithmic actual quadratic asymptotic, the bounded local complex frozen correction, the phase-sensitive outer source estimate, the exact local/outer contour certificates, and the saddle comparison yielding the limiting first-negative slope and logarithmic shift. The main theorem does not use the larger finite first-negative table.

The interval arithmetic uses directed integer rounding on a 10^32 grid, Machin bounds for pi, Taylor remainders, phase-preserving spatial factors, and geometric infinite-product tails. The compact outer certificate uses 2812 boxes; the local certificate uses 127 boxes. Exact tree replay checks coverage as well as every inequality. A larger direct complex-product construction and an independent scalar-factor replay were also verified before the compact certificate was selected.

The flat outer checker modules are portable copies of the independently reviewed scalar and logarithmic-derivative implementation. Their import paths were localized; the saved-leaf wrapper checks the compact partition. The separate outer ZIP preserves its original portable bundle identity. All individual package files are covered by SHA256SUMS.

Related literature is cited as context. Fan–Schmeling–Shen treats the phase-dependent trigonometric-product family; Baake–Gohlke–Kesseböhmer–Schindler treats pressure and scaling for the classic measure. Neither citation is presented as an exhaustive search establishing priority for the current theorem.
