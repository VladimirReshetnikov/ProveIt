# Independent audit of the nonstandard merging-branch model

I have checked the core-proof draft subsequently incorporated into report.tex. I find no gap in the claimed model, rule soundness, or finite-parameter bi-interpretability obstruction. The following are the decisive points and the qualifications that should remain explicit.

## Closure must cover internal iteration lengths

For each internal r in the ambient PA model A, define the internally definable region

    B_r = main points union {branch(n,j): r <= n < c, j > 0}.

For every fixed finite term, ambient PA proves that B_r is closed under its operation, uniformly in r and in the other parameters. This is proved by an external induction on the term syntax. In the iterator case use PA's internal induction on the number of steps, with membership in B_r as the invariant. A stronger version tracks a branch's input label and lower bound on its rank; it is also sound.

For finitely many inputs from M, choose a nonstandard r no larger than all their branch ranks, or r=c if every input is a main point. All inputs lie in B_r; all branch outputs have nonstandard rank. This proves M is a substructure. In particular it proves closure for every intermediate state at every internal count, including nonstandard counts. External induction restricted to standard step counts would not suffice, but that is not what the proposed proof uses.

## Constancy transfer is legitimate

Fix an assignment of passive parameters in M satisfying an arbitrary context Gamma. The premise provides f(Sx)=f(x) for every x in M. Every fixed finite term f extends to an arithmetically definable total map on B.

The entire main line belongs to M. Hence A satisfies the internal universal statement f(main(n+1))=f(main(n)) for every n; PA induction gives main-line constancy.

If x=branch(n,j) belongs to M, all internal points of the path from rank n to rank c have ranks at least n, hence remain nonstandard and belong to M until the merge. Therefore A satisfies the bounded universal stationarity statement along the *whole internal interval*. PA induction telescopes it to f(x)=f(main(c)). Combining with the main line yields f(x)=f(0).

Gamma need not be A-definable: it is used only to fix an assignment at which the premise is true. The subsequent internal induction is on equations involving the fixed arithmetically definable term f. This validates contextual Const for arbitrary first-order contexts.

Do not strengthen the conclusion to all externally supplied functions M->M. For example the external distinction between a standard and a nonstandard distance c-rank on a branch can give a nonconstant stationary map. Such a map is not denoted by an internal finite term, and is irrelevant to Const.

## No uniform-evaluator assumption is hidden

For each fixed finite body h, its interpretation is one primitive-recursive map on pair codes, with c and the passive values as parameters. Iterating this fixed map is again primitive recursive. The construction recurses externally over finite syntax and uses internal PA induction for each fixed iterate. It does not postulate a single total primitive-recursive evaluator ranging over all program descriptions, and uses no nonstandard syntax tree.

## Fusion and extensionality survive restriction to M

The rule premises need hold only on M. Internal orbit closure ensures that all states at which those premises are used are still in M, even along a nonstandard internal iteration. Their fixed arithmetic defining formulas therefore hold at every internal step. Ordinary internal induction proves the fusion, fixed-point, seed-shift, and body-extensionality conclusions. No premise about discarded standard branch points is required.

## Automorphisms and bi-interpretability

Swap two complete positive branch labels not used by a prescribed finite parameter tuple. This is an internally primitive-recursive involution on B that preserves rank, S, 0, and epsilon. A structural induction on each term, and internal induction on iterator length, establishes equivariance. Restriction is an automorphism of M.

The automorphism has order two and is nontrivial; its support as a permutation of M is generally infinite. It should not be called a finite-support transposition of two points.

Any ordinary finite-dimensional interpretation with parameters fixed by this automorphism, including a quotient interpretation, induces an automorphism of the interpreted model. A definable return isomorphism in a bi-interpretation makes this action injective. All necessary parameters and representatives of parameters from the reverse interpretation can be included in one finite tuple before the labels are chosen.

Every classical iPRA model has its parameter-free definable strict linear order. A finite-order automorphism of a linear order is the identity: any moved point produces a strict cyclic chain. Thus an order-two source automorphism cannot inject into the automorphism group of an interpreted iPRA model, giving the desired contradiction.

## Scope

The construction refutes successor injectivity and the clock equation while validating the displayed base, coverage, Const, and the listed optional iteration laws. The clock equation has a derivable base and successor step, so equation induction is not admissible. The automorphism proof strengthens this to failure of ordinary finite-parameter bi-interpretability with iPRA; it does not claim failure of one-way interpretations, equiconsistency, or a lower bound on checker length.
