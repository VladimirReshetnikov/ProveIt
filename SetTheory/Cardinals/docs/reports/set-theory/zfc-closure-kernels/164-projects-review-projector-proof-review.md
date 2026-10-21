# Independent mathematical review of the projection restriction

Reviewer: machine_folds subtask. This review did not author the Source149 certificate or the projection-family proposal. It implements a second forward checker, without importing the supplied checker or audit module.

## Result

The projection restriction and the numerical strengthening are correct as ordinary mathematical statements. They do not establish a smaller binary machine. The inherited calibration from the original numerical calculus to ZFC remains an explicit premise.

Let `P(a,b)=(a+b)(a+b+1)/2+b`, `I(a,b)=4P(a,b)`, and let `L(n),R(n)` be the two components of the unique Cantor unpairing of `floor(n/4)`. These are total functions on natural numbers; no tag or formula-recognition check is required. For every pair of natural numbers, including `a=b=0`,

`L(I(a,b))=a` and `R(I(a,b))=b`.

In particular, `I(0,0)=0` is retained, with `L(0)=R(0)=0`.

The exact 3728-node certificate was independently replayed: 1260 restricted rho8 leaves, 410 substitution nodes, 55 MP-with-substitution nodes, 2002 direct MP nodes, and one truth node. All seven claimed roots, including unrestricted rho8, pass. The 5160 source term references were checked for backward topology and canonical zero normalization.

For a symbolic axiom leaf with `U=p(A)`, every letter of its displayed projection path traverses a literal implication node or the absorbing zero. It never traverses an unspecified schema variable. Induction along that path proves the identity under every assignment of natural numbers to variables. The additional constant-zero family is immediate. Consequently the certificate is a proof using only the proposed computed-fourth-argument rho8 families.

The certificate's substitutions are justified by induction on universally quantified metatheorems: if every numerical assignment makes the parent term derivable, assign each parent variable the evaluated substituted term. MP then applies to two derivable natural codes. Canonical variable renaming at MP-with-substitution nodes is likewise a change of valuation. This reasoning does not assume a uniform-substitution rule for the full native object calculus, and does not require its other axiom families to be substitution closed.

Every proposed projector axiom is an unrestricted rho8 instance, even when its arguments are junk codes. Conversely, the checked universal rho8 root replaces each unrestricted rho8 axiom occurrence by a finite proof in the restricted calculus. Since every other axiom and rule is unchanged, both calculi derive exactly the same natural codes. This transfers syntactic consistency equivalence, not merely semantic soundness in an intended model. Truth code zero must be available as in the inherited calculus.

## A better supported basis

The independent support census finds **six**, rather than only one, optimal nine-family covers of this exact certificate. All have the six families

`ZERO, epsilon, L, R, LL, LLR`,

and choose `LR` or `RR`, include `RRR`, and choose one of `LLLR`, `LLRR`, `LLRLLLL`.

For implementation, the basis

`ZERO, epsilon, L, R, LL, RR, LLR, RRR, LLRR`

is especially convenient: its eight nonconstant projection words are prefix closed. Therefore computing their common traversal tree needs no unselected intermediate projection. The originally proposed basis additionally needs the intermediate prefixes `RR` and `LLL`. This observation is a concrete reduction in the projector traversal representation; no binary state saving has been compiled or claimed.

The minimum of nine is only a certificate-cover minimum for constant-zero and literal-projection families. Five separate leaves force `epsilon`, `R`, `L`, `LLR`, `LL` (nodes 0, 1, 2, 31, 113), and node 5 forces the constant-zero family. Three further leaves have pairwise disjoint remaining support sets:

- Node 115: `{LR, RLLL, RR}`.
- Node 1112: `{RLR, RRR}`.
- Node 2163: `{LLLR, LLRLLLL, LLRR}`.

These sets are disjoint from the six forced families. Thus at least three more families are required. A nine-family upper bound is explicitly checked. The independent enumeration includes all displayed occurrence paths, with no depth cap: there are 55 nonconstant candidate words plus constant zero. Words outside that universe can cover only zero leaves, for which the constant-zero family is already at least as useful. This does not prove that nine families are necessary for some other proof or for equiconsistency in general.

## Numerical strengthening

Cantor unpairing gives `L(n),R(n)<=floor(n/4)`. Hence, for every nonempty projection word of length k,

`4^k p(A)<=A`.

The empty projection gives `U=A`; the constant-zero family satisfies `4U<=A`. Thus every axiom in the supported projector basis obeys

`U=A or 4U<=A`.

The calculus with this numerical restriction lies between the supported projector calculus and the unrestricted calculus and therefore derives exactly the same natural codes. This proof covers raw zero and every other natural code. It establishes no unconditional consistency assertion and no state-count result.

## Review artifacts and limits

`review_projector_certificate.py` is the independent checker; `projector-independent-review.json` records its execution, the source SHA-256, all optimal covers, and the lower-bound witnesses. The exact input SHA-256 is `3cf18a5fe9f187b50b79d97b84535ce9bf776305728b0cdfe17285e94f028452`.

No Lean or Rocq proof was compiled. No new source-to-tape compiler or blank initialization for the projector calculus was supplied. The mathematical result is suitable for the report's proved formalism section, but must not be described as the requested 216-state construction.


## Subsequent finite-matrix review

The author's final `projection_basis.tex` was reviewed, including the prefix-closed basis and all six cover counts. The finite matrix was independently re-evaluated by `review_context_matrix.py`, without importing the author's checker. The reviewed implication-context families account for 64 diagonal assignments, 256 left-child assignments, 256 right-child assignments, and 4096 three-right-child assignments, plus 64 constant-truth cases. Truth alias and MP preservation, I/K/Peirce/cd59, and the explicit failures of B, S and unrestricted rho8 all pass. Its limited propositional scope is accurately stated: no interpretation of the total numerical destructors or the retained set-theoretic rows is established. Receipt: `context-matrix-independent-review.json`.
