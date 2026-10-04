# Primary literature audit evidence

Research date: 4 October 2026 UTC. This is a scope and attribution check, not an exhaustive novelty search. No author or upstream code was executed.

## Gilbert and Tan 1991

Elmer G. Gilbert and Kok Tin Tan, *Linear Systems with State and Control Constraints: The Theory and Application of Maximal Output Admissible Sets*, IEEE Transactions on Automatic Control 36(9), 1008–1020. DOI: https://doi.org/10.1109/9.83532

Primary archived paper: https://web.eecs.umich.edu/~grizzle/GilbertFest/Gilbert%2865%29.pdf

Verified locations: §IV, Theorem 4.1; introduction p.1009; §V, Theorem 5.1. The finite-determination theorem's hypotheses include asymptotic stability, observability of (C,A), bounded Y, and 0∈int(Y). C=I and the packet's bounded open P meet these conditions. The indexed theorem statement does not require closed or convex Y. The +1/stable block structure of §V is narrower than arbitrary Lyapunov-stable dynamics.

Access qualification: direct PDF fetch returned HTTP 502. The theorem statements and introductory scope were verified through indexed excerpts of the primary archived PDF. This audit does not claim to have opened the complete PDF successfully.

Verdict: supported; optional narrower wording for §V.

## Kannan and Lipton via the later primary research manuscript

Ravindran Kannan and Richard J. Lipton, *Polynomial-time algorithm for the orbit problem*, Journal of the ACM 33(4), 808–821 (1986). DOI: https://doi.org/10.1145/6490.6496

Ventsislav Chonev, Joël Ouaknine and James Worrell, *On the Complexity of the Orbit Problem*, JACM 63, Article 23 (2016), primary author manuscript: https://people.mpi-sws.org/~joel/publications/orbit_journal_14.pdf

Verified locations: §1, PDF p.1, defines rational point-to-point A^n x=y and explicitly attributes polynomial-time decidability to Kannan–Lipton's 1980 conference and 1986 journal work. PDF p.2 distinguishes the zero-dimensional affine point target from subspace targets.

Verdict: supported. The packet's rational contacts really are point targets, so this is a valid alternative to its elementary denominator test.

## Fijalkow and coauthors STACS 2017

Nathanaël Fijalkow, Pierre Ohlmann, Joël Ouaknine, Amaury Pouly and James Worrell, *Semialgebraic Invariant Synthesis for the Kannan-Lipton Orbit Problem*, STACS 2017, 29:1–29:13.

Primary publisher page: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2017.29

Primary PDF: https://drops.dagstuhl.de/storage/00lipics/lipics-vol066-stacs2017/LIPIcs.STACS.2017.29/LIPIcs.STACS.2017.29.pdf

Verified location: Example 1, p.29:3. It uses precisely (1/5)[[4,−3],[3,4]] and explains failure of semialgebraic invariant separation for an unreachable target on the orbit closure. The primary PDF's angle description appears to contain a typo, arctan(3/5); the matrix angle is arctan(3/4). The reviewed packet does not repeat this typo.

Verdict: supported. Attribution of the obstruction mechanism does not claim that this example already states the packet's complete strict-polygon formula.

## Dai and Xia 2012

Liyun Dai and Bican Xia, *Non-Termination Sets of Simple Linear Loops*.

Primary manuscript: https://arxiv.org/abs/1206.0232

Primary PDF: https://arxiv.org/pdf/1206.0232

Verified locations: §2, PDF pp.3–4, restricts the subsequent treatment to homogeneous while(Bx>0){x:=Ax}; §3, Algorithm 1, PDF p.5, takes A of size 2-by-2 and a 1-by-2 row B; Theorem 1, PDF p.11, proves correctness. Multiple homogeneous rows are handled by intersection in §2, p.4.

Verdict: supported. Homogenizing affine constants introduces an extra state coordinate, so this specific two-variable theorem cannot simply be cited as the exact affine planar classification.

## Almagor and coauthors STACS 2019

Shaull Almagor, Joël Ouaknine and James Worrell, *The Semialgebraic Orbit Problem*, STACS 2019, 6:1–6:15.

Primary publisher page: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2019.6

Primary PDF: https://drops.dagstuhl.de/storage/00lipics/lipics-vol126-stacs2019/LIPIcs.STACS.2019.6/LIPIcs.STACS.2019.6.pdf

Verified locations: abstract p.6:1; §4, Theorem 11, p.6:12. The result covers rational-matrix semialgebraic source-to-target reachability in dimension at most three. Singular matrices are reduced to lower dimension, with fuller details delegated by the paper to its full version.

Verdict: supported. With a singleton rational source and the complement of P as target, nonmembership in K is a special case. No invertibility condition invalidates this application.

## Ouaknine and Worrell low-order positivity

Joël Ouaknine and James Worrell, *Positivity Problems for Low-Order Linear Recurrence Sequences*, arXiv:1307.2779, subsequently SODA 2014.

Primary manuscript: https://arxiv.org/abs/1307.2779

Primary PDF: https://arxiv.org/pdf/1307.2779

Verified locations: §4, Theorems 4.1–4.2, PDF pp.5–6; rational-to-integer conversion immediately after Theorem 4.2; §6, PDF p.12; nondegeneracy handling in §2, PDF p.3 and its footnote 6.

Theorem 4.1 gives a counting-hierarchy upper bound coNP with three nested PP oracle levels for Positivity at order at most five. §6 transfers the stated decidability and complexity results to strict positivity except the order-five Positivity case. Therefore order at most three strict positivity is covered. Rational scaling is v_n=ℓ^(n+1)u_n and preserves sign. Repeated roots and unit roots are not excluded; root-of-unity degeneracy is handled through residue classes. The nonzero-last-coefficient recurrence convention requires removing zero-root finite transients when applying the theorem to singular matrices.

Verdict: the reviewed packet's caution is safe. A stronger uniform counting-hierarchy bound can already be recorded after matching conventions; this is not a uniform polynomial-time result and is not asserted here to be optimal.
