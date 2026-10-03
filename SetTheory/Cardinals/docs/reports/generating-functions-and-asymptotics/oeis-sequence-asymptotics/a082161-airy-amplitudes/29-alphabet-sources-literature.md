# Bounded literature / semantic overlap receipt

Checked 2 October 2026. This is not a claim of exhaustive worldwide novelty.

- The primary title is *Asymptotics of relaxed k-ary trees*, by Manosij Ghosh Dastidar and Michael Wallner (not 'related'). arXiv 2404.08415 has only v1, submitted 12 April 2024: https://arxiv.org/abs/2404.08415 . The published AofA 2024 paper is https://doi.org/10.4230/LIPIcs.AofA.2024.15 . Theorem 1 is a relaxed-tree Theta result; published Propositions 8/11/12 supply relaxed/compacted/DFA recurrences. Section 4 explicitly defers compacted/DFA asymptotics to a long version.
- The primary project bibliography https://dmg.tuwien.ac.at/mwallner/stretched-exponentials/ and focused searches for finite-language DFA asymptotics and compacted k-ary trees, including 2025/2026, did not locate a subsequent full-arity amplitude or higher-order theorem.
- A genuinely later primary paper, Wallner, *The Decompressed Tree Size of k-Ary Chains*, published 25 April 2026, https://doi.org/10.1007/s00026-026-00816-y , studies a different statistic on chains, not enumeration of all minimal acyclic automata. It still cites AofA 2024 for relaxed k-ary enumeration. It does not close the present gap.
- A 2023 presentation search hit gives a misleading (7k-8)/6 exponent without the final factorial-normalization correction. The published theorem was consulted directly, giving (2k-1)/3.

## OEIS

Published tables identify A331120 only for binary minimal DFA counts, A082161/A082162/A102102 for relaxed arities 2/3/4, and A128249 as the relaxed-arity array. A254789 is compacted binary. The ternary and larger DFA rows have no IDs in the 2024 tables.
Fresh OEIS web searches and official oeis/oeisdata GitHub searches for exact strings '14,532,42644', '30,3900,1460700', and '62,26164,43023908' returned no matches. The OEIS JSON search endpoint failed. Hence no larger-arity DFA ID was verified; absence is bounded search evidence, not certainty that no entry exists. Avoid assigning A082162 to minimal ternary DFAs: it is relaxed ternary trees and begins 1,1,7,139 rather than 1,1,14,532.

## ProveIt semantic overlap

Fresh authorized default-branch searches in VladimirReshetnikov/ProveIt checked 'k-ary' with 'relaxed', 'relaxed trees', 'A082162', 'summable' with 'automata', 'minimal deterministic', and 'finite' with 'automata' with 'Airy', plus number strings. Raw connector receipts are in overlap.json. Semantic hits concern insertion-degree spectra, graph visibility, a different Airy fold and numerical substring coincidences, not this enumeration problem. The broad 'minimal'+'acyclic' and raw-number searches were noisy/capped; the narrow exact phrases returned no relevant overlap. Earlier same-day A331120 receipt is available in the approved binary report, but these checks are fresh. No repository changes were made.

The comparison theorem should be described as a locally proved extension with bounded novelty screening, not as a certified globally new discovery.
