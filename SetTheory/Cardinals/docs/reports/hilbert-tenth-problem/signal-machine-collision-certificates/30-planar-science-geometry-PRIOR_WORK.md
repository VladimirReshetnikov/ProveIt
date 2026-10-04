# Primary literature and claim boundary

Research date: 4 October 2026. These references distinguish established tools from the exact specialization proved in PROOF.md. The search is not exhaustive and does not justify a novelty claim.

## Maximal admissible sets and finite determination

Elmer G. Gilbert and Kok Tin Tan, *Linear Systems with State and Control Constraints: The Theory and Application of Maximal Output Admissible Sets*, IEEE Transactions on Automatic Control 36(9), 1008–1020, 1991. DOI: https://doi.org/10.1109/9.83532

Primary archived paper: https://web.eecs.umich.edu/~grizzle/GilbertFest/Gilbert%2865%29.pdf

The paper defines the maximal output-admissible set by constraints CA^n x in Y at every time. Its Section IV establishes finite determination under asymptotic stability, observability, bounded output constraints, and an interior-origin hypothesis. Section V treats finitely determined inner approximations in a Lyapunov-stable setting. Here C=I, and the contraction-tail argument gives an elementary strict-guard specialization. Neither the invariant-set concept nor stable finite determination is new. The distinction between exact open guards, their closure, and permitted limit-boundary points must be retained.

Access note: the primary archived text was available through indexed search extracts, including the paper's own description of Sections IV–V. Direct PDF opening returned a fetch error. No theorem numbering beyond the verified section references is asserted.

## Point-to-point orbit membership

Ravindran Kannan and Richard J. Lipton, *Polynomial-time algorithm for the orbit problem*, Journal of the ACM 33(4), 808–821, 1986. DOI: https://doi.org/10.1145/6490.6496

Verified primary research discussion: Ventsislav Chonev, Joël Ouaknine, James Worrell, *On the Complexity of the Orbit Problem*, Journal of the ACM 63, Article 23, 2016. Author manuscript: https://people.mpi-sws.org/~joel/publications/orbit_journal_14.pdf

The 2016 introduction explicitly states the rational point-to-point problem A^n x=y and its polynomial-time decidability by Kannan and Lipton. It supplies an independent alternative for each rational ellipse contact. The target is a point, not a guard hyperplane or an unspecified algebraic set. PROOF.md instead gives an elementary companion-denominator specialization. Its polynomial-time conclusion was already implied by the established general orbit algorithm.

## Irrational rotations and semialgebraic obstructions

Nathanaël Fijalkow, Pierre Ohlmann, Joël Ouaknine, Amaury Pouly, James Worrell, *Semialgebraic Invariant Synthesis for the Kannan-Lipton Orbit Problem*, STACS 2017, 29:1–29:13.

Primary publisher page: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2017.29

Primary paper: https://drops.dagstuhl.de/storage/00lipics/lipics-vol066-stacs2017/LIPIcs.STACS.2017.29/LIPIcs.STACS.2017.29.pdf

Example 1 already uses the rational irrational-angle rotation (1/5)[[4,-3],[3,4]] to demonstrate failure of semialgebraic invariant separation for an unreachable target on the orbit closure. The general invariant-synthesis problem is also treated there. Thus the rotational mechanism obstructing semialgebraicity is prior work. The present note specifically computes the entire strict polygon kernel as a critical rational ellipse with finitely many backward contact orbits removed, and proves a rational-input sign obstruction using two tails of one rational contact orbit.

## Two-variable nontermination sets

Liyun Dai and Bican Xia, *Non-Termination Sets of Simple Linear Loops*, 2012.

Primary manuscript: https://arxiv.org/abs/1206.0232

PDF: https://arxiv.org/pdf/1206.0232

Their two-variable algorithm concerns homogeneous guards Bx>0 and updates x:=Ax; see the stated scope in Sections 2–3. Our bounded polygon containing the origin instead has nonzero guard constants. Homogenizing those constants introduces another variable, so their two-variable theorem should not be cited as automatically solving the exact problem here. Their results nevertheless make it inappropriate to suggest that eigenvalue-based planar nontermination analysis is new.

## Broader low-dimensional reachability

Shaull Almagor, Joël Ouaknine, James Worrell, *The Semialgebraic Orbit Problem*, STACS 2019, 6:1–6:15.

Primary publisher page: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2019.6

Primary paper: https://drops.dagstuhl.de/storage/00lipics/lipics-vol126-stacs2019/LIPIcs.STACS.2019.6/LIPIcs.STACS.2019.6.pdf

They prove decidability of semialgebraic source-to-target orbit reachability in dimension at most three. For a rational singleton source and the complement of P as target, nonmembership in K is such a reachability question. Thus uniform decidability of the planar guard problem is already a consequence of broader prior work. The present classification supplies elementary exact geometry in this convex, bounded, origin-interior setting; it is not a new general decidability theorem.

## Uniform complexity caution

Joël Ouaknine and James Worrell, *Positivity Problems for Low-Order Linear Recurrence Sequences*, manuscript arXiv:1307.2779, subsequently SODA 2014.

Primary manuscript: https://arxiv.org/abs/1307.2779

The authors establish decidability and complexity bounds for low-order positivity and ultimate positivity. Each guard sequence b_i-h_i A^n x in the present problem satisfies a rational linear recurrence of order at most three. Exact strict positivity and the encoding of rational recurrences must be matched carefully before transferring a sharper complexity bound. PROOF.md therefore claims only the fully proved fixed-A polynomial-time bound, a uniform polynomial elliptic branch, effective construction, and an explicit linear-form output-size lower bound.

## Positioning

The candidate contribution is a clean, fully explicit strict-boundary classification suited to exact chambers of a separately proved small-signal physical compiler. The rational ellipse contacts, weak-limit unit/stable formula, irrational stable-line distinction, and exponential-facet example are useful components to state and verify. No claim is made that these elementary components or their combined abstract theorem are absent from the existing control, loop-analysis, or linear-dynamics literature.

The next geometric research step proposed in PROOF.md is an exact strict-boundary and arithmetic treatment for two independent rational rotation blocks. It asks for a concrete specialization and transparent proof, rather than rebranding known orbit decidability. A separate explicit elliptic arithmetic certificate is an independent deliverable, not a theorem in this note.
