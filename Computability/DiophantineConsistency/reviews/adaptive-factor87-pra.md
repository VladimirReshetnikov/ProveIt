# Candidate-PRA proof of the 87-gate equation rewrite

`AdaptiveFactor87PRA.candidate_proves_equivalence` constructs an actual proof
in the repository's candidate PRA calculus of the language-mapped equivalence
between the parent and 87-gate no-zero sentences. It applies the checked
IΣ₀-to-candidate-PRA proof translation to
`AdaptiveFactor87HA.isigma0_proves_equivalence`. The theorem does not prove
either sentence, connect either sentence to `Con(ZFC)`, or identify the
candidate calculus with a standard presentation of PRA.

The author and independent clients were built at
`/tmp/adaptive-factor87-pra-author-zicpfl4k` and
`/tmp/adaptive-factor87-pra-independent-seq91i74`, using separately matching
IΣ₀/HA providers and independently replayed post-merge bounded-comparison
providers. The main source, object and log hashes match respectively
`9d0998e1903949fd4ae9fcf6f18163f91087f076ee95b9361c816df09761bde6`,
`7ac201a715cc467deede43266be2f949ee31a91c092fb33948ca46441f0d777f`, and
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The check source, object and log hashes match respectively
`e0184b5637ae509020acd9eac1da04fa4257aef8f3bec3dfee99195409226ac8`,
`b56f01dedb0777d7b3a74baffe52560152945b859384f1a0ac85361eb63e6c6a`, and
`8261bb9b81e2733e9d75f7ed47c3c69d92c04fee808d98ce83ba7e7d082e24a7`.
The retained [logs](adaptive-factor87-pra-replay/) report only `propext`,
`Classical.choice` and `Quot.sound`. The two parent chains, Foundation and
Mathlib are inherited boundaries of this final client; their separate replay
receipts give the scope of their authentication. A source reviewer checked the
mapping and the theorem's stated limits.
