# Source comparison and attribution

## Pinned intake source

The inspected user-repository research manuscript is **Weighted Rank Five and Covers with a Two Vertex Shore**, prepared for Vladimir Reshetnikov with OpenAI, October 1, 2026.

- Pinned archive: https://github.com/VladimirReshetnikov/ProveIt/blob/1512ef8356d10fef99e7caaa2753620f0c900c83/docs/incoming/ProveIt_Weighted_Rank_Five_and_Two_Shore_Covers.zip
- Arrival commit: https://github.com/VladimirReshetnikov/ProveIt/commit/1512ef8356d10fef99e7caaa2753620f0c900c83
- Archive SHA256: 06dd0ae6a88654fb1f409dda35c3346c8cbd443a36d86f32fd1b0120903c6357
- Archive source directory: ProveIt_Weighted_Rank_Five/

The relevant sources were read directly. No source program from the intake was executed.

## Explicit overlap

The intake's article and negative_ranks.tex already contain:

- The all-2+q weighted graph theorem and actual-rank ULC through rank five
- The complete-core/exterior-block support quota formula
- Weighted scalar counterexamples at rank six and every higher rank
- The 72-vertex, 207-edge example with N=33 and core activity 26804
- The statement that the sharp universal weighted rank threshold is five

The scalar sections of the accompanying paper are an independent reconstruction and additional exact verification of those intake results. They are not claimed to be new to the repository. The independently chosen N=40, activity 10000 example and N=33, activity 30000 variant use the same construction.

## The rank-compression construction

The intake's full_lift.tex already builds a rank-(q+2) transversal matroid using two augmented distinguished elements and two extra slots. Its six basis cases prove the graph's homogeneous selected-left marginal is Lorentzian. Retaining separate covered-head dummy variables is also compatible with that construction.

The previously delivered all-finite-matroid theorem extends the scope beyond a represented/transversal seed. A shorter proof of that unrestricted extension can use matroid union with the same two-slot auxiliary matroid. This is an extension of the inspected rank-compression idea and must be credited accordingly; it is not an unrelated newly discovered graph proof. The earlier longer proof and release remain unchanged.

## Separate refinements recorded here

The three-parallel-pair obstruction, its thirteen-vertex graph lift, and the positive-activity three-variable Lorentzian obstruction were independently reconstructed and audited in this research. They concern the specific multivariate homogenizations; their own scalar sequences are ULC. These particular examples were not located in the inspected intake source files. The subsequently inspected nested-exterior and second-Newton papers also contain different full-right-marginal and quintic Lorentzian obstructions. Thus the general phenomenon of a failed stronger Lorentzian approach is already present in the intake. The particular thirteen-vertex examples and sectors in this package are separate exact constructions. This bounded comparison is not a claim about the entire repository or literature.

The all-rank first-layer matrix inequality uses a Gram/partition argument. The intake second-Newton article also uses the same pair-count identity in a neighbor-feature Gram matrix and proves a 3+3-cover bound using the three-vertex marginal input. This is related mathematical context; the present probability/projector decomposition is a different ordinary all-r argument, without a global novelty claim. It is stronger than the scalar first Newton gap, whose separate compatibility-graph proof appears in the intake's first_gap.tex. A later local-source inspection found the same three-tail zero-old-rank cubic statement in **Lorentzian Marginals on Three Vertices**, bundled as `prerequisites/ProveIt_Three_Vertex_Marginals_and_Star_Cores.zip` inside the inspected second-Newton archive. Its proof uses Wagner plus a 5,339-term determinant coefficient certificate. The present all-rank Gram/partition proof removes that finite certificate and gives an ordinary proof of the already-stated cubic theorem. No new-to-intake claim is made for the cubic statement.

That cubic remains distinct from the intake paper **A Rank Six Cubic Sector with a Complete Core**, which treats a forced-right-core sector under one-shore activities and eventual scaling. That intake paper expressly leaves the finite-activity rank-six one-shore problem open.

## Source hashes

- article.tex: 38e53d4ed32fd20ef39d38e57e78f0aab7efb9215adb7f4e7a111c736f8ab137
- negative_ranks.tex: 01d77c2c79f1deacbd0bd2590161370a81b31ce0b0fe9cf05c0642038bc22517
- full_lift.tex: 7236158335047314a874863965e6767248ccdc0852958aadcbc5ce7a9554222c

The intake is a user-repository research manuscript, not a peer-reviewed publication. No global priority claim is made. The preserved historical proof notes predate this source comparison; this comparison and the integrated article provide the current attribution.

Additional nested-source hashes:

- Three-vertex prerequisite archive: 91332da5ae1bf78f03889832ca1a41156bd3d0c83443ea033c11b6a71c6c9b08
- Its article.tex: 635277bf168a1a621a447464d32efe8c514d67ad175307fb8e88887837b5190f
