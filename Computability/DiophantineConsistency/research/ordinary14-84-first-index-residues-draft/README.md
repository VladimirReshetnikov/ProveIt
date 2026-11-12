# First Pell index and residues from 84 own-zero — source draft

This unelaborated source proposal strengthens the separate first-index draft by
using `ArithmeticPellFirstNorm.solution_residues`. With positive beta and
J,w,s, the beta port cast, and the 84 graph's own zero, it proposes the same
first Pell index and two natural residue quotients. In particular,
`k=2*n+4*(X*Y²)*s`, with `s` a new existential quotient, is the first-index
relation needed by the later modified-carrier route. The proof explicitly uses
`Q>0` to justify `(Q−1)+1=Q` before rewriting the discriminant.

This does not yet identify `2*n` with the natural rank plus one or derive a
rank window, main-index equality, gamma bound or 84↔85 equivalence. All draft
imports, model tactics, provider ancestry, and the iPRA endpoint remain
uncompiled or separate; no physical-file/PDF correspondence follows. The
checker inventories the interfaces, replays the first-norm receipt and checks
60 finite Pell recurrence/residue cases. No Lean run is performed.

Independent source review is recorded in
`../../reviews/ordinary14-84-first-index-residues-draft-independent/`.
