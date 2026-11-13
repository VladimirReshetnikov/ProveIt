# Proposed P72 exact-index client for a positive 84 zero

This **unelaborated source composition** proposes applying the existing
`P72Exact.indices_ordinary` interface to first-index inputs, main-index/balance,
strong norm, and auxiliary norm all extracted from the same positive 84
zero. It retains positive beta, all-positive valuation, four explicit natural
port casts and the inequalities `MC<beta`, `MF<2*beta`. The proposed output
includes `m=R` and `2*n=R+1` alongside the original main carrier balance.
The source passes `i'=slot4` and the first-index residue quotient explicitly;
it does not assume an old 85 graph zero.

This is a draft statement and proof script, **not a checked Lean theorem**.
All component drafts, exact definitional alignments, tactics and source/provider
ancestry need a guarded Lean build and independent audit. Actual compact port
identification and mask-bound instantiation, the remaining gamma/w positivity
and 84↔85 model comparison, the iPRA endpoint, and external file/PDF semantics
remain separate. No compile or endpoint claim is made.

The checker inventories the client and existing interface, replays four
source/finite-control receipts and tests 100 delta identities without running
Lean. It does not validate Lean elaboration, the P72 theorem's arbitrary-model
hypotheses, or a graph zero.

Independent source review is recorded in
`../../reviews/ordinary14-84-p72-exact-indices-draft-independent/`.
