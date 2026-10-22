# Attribution and scope

This work reviews and refactors the K215 formal verification in Vladimir
Reshetnikov's ProveIt repository at commit
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

The concrete machine, source program, numerical encodings, completeness
arguments, existing 58-step dominated-implication derivation, and decoder
correctness proofs are inherited work. Their authorship and upstream notices
are retained in the repository and the included component notices.

In particular, the architecture of one shared implication core, the pure
unrestricted adapter, and the unchanged Tarski bridge come from the earlier
`shared-proof-core` proposal. The semantic site-coverage interface comes from
the earlier semantic-coverage proposal. Inclusion in that proposal tree is
distinct from adoption as a maintained endpoint dependency.

The contributions of this collaboration are the two-MP S extension found
during this review, integration of the common proof into both currently
maintained calculus interfaces, synchronized producers, source and typed-client
comparisons, the exact certified decoder-prefix/residual-executor connection,
finite residual checks, and the accompanying report and reproducibility
artifacts. The two-step derivation is a local contraction of an existing lemma
basis, not a claim of globally novel or shortest implicational mathematics.

New ProveIt material follows the included MIT No Attribution license
(`LICENSE.ProveIt`). Inherited third-party portions retain their own license
scope; they are not relicensed by this notice. The Rocq component includes
the pinned K230 reference's full third-party notice and relevant upstream
license texts. Proof-assistant binaries and standard libraries are not
distributed in this packet.

"Independent review" refers to a second review within this research
collaboration. The provided checks are focused component checks. They do not
replace production endpoint replays or assert a reduction in the number of
states of the machine.
