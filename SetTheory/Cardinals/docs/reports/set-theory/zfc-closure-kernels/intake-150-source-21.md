# Batch 150 / source 02: two-parameter EPSC and compact initializer

Independent intake review, 16 October 2026. Arrival `47e8871089dd8d5b5a912350f3285734041528bb`; manuscript pin `af518abcf8ca2a7c1b795c07973885041aee0d25`. I read all eight report sections, the two-parameter proof notes, checker and initializer review notes, the complete tableau/checker tests, initializer and reproduction code. Runs used an isolated copy. Delivered files were not edited. Bulk provenance/checksum verification was skipped; functional table comparisons were retained. No Lean or Coq build was requested or run for this package.

## Theory: an actual bounded-parameter argument

The report proves an ordinary interpretation/calibration for equality-free EPSC2, whose matrices may have only the free variables x,y,p,q. Arbitrary internal quantifiers remain available. This is an infinite recursive schema, not a finite list of first-order axioms or four-variable logic. I found no substantive defect in the bounded-parameter proof.

The resource bootstrap stays within the stated budget. A false matrix yields an empty object. A globally subset-bounded class theta(y;p,q) has an exact container, with the external bounding object absent from the defining matrix. Power and full two-sided-profile singleton resources each use one parameter. The profile singleton decoder W is parameter-free: it outputs a full-profile singleton when one exists, otherwise subsets. If y belongs to x, it produces y in one or two edges; the required intermediate inputs are nonempty. The one-parameter seeded gate uses the disjoint empty/nonempty cases to obtain a transitive cover before Pairing or Union has been assumed.

Raw Union and the limited cuts also respect their parameter counts. The binary common-bound argument uses parameters a,b and branches on whether a is empty. In the nonempty case the first output is a; recurrence from a then emits b. Taking the union of the resulting hull gives a common subset bound. No choice of an infinite family of arbitrary bounds is used.

The hereditary saturated domain H and incoming-profile equivalence D are fixed first-order definitions. A purity cut of a transitive cover needs only that cover as a parameter. Saturation of A is bounded inside its raw union. The argument establishes pure Pairing with two parameters **before** packing arbitrary parameter tuples. In H/D, membership is congruent and Extensionality holds because every raw member of a hereditary object is hereditary. Finite Kuratowski tuple codes are defined separately for each fixed length, with coordinates unique up to D. This uses finite iterations of Pairing, not an internal set of all tuples, Foundation or an assumed Replacement schema.

Packing is applied to hereditary interpretations of formulas, whose truth is D-invariant. It is not applied to arbitrary raw predicates. An arbitrary target parameter tuple becomes one code t. Adding the seed a uses the second parameter in a matrix R(x,y;t) OR (empty(x) AND y subset a). Binary common bounds establish local boundedness one input at a time. The supported filter of the resulting C0 is defined by y in C0 AND exists x R(x,y;t): its two parameters are C0,t; a has disappeared. Saturation then yields a pure supported hull, recovering the full arbitrary-parameter extensional PSC schema. The support clause and the purity restriction are both essential to this proof.

The inherited extensional PSC/ZF-without-Foundation-or-Choice comparison, internal well-founded core and constructible universe reductions give the ordinary ZFC-formalizable consistency equivalence. The converse uses unique exact fibers and Replacement to collect them, then an omega closure; it does not need a choice function for local bounds. This is not a serialized Lean or PA calibration. Whether one parameter, or none, suffices remains open; packing before obtaining Pairing would not settle that question.

The parameter-packing idea is not claimed as historically new. The primary Schindler–Schlicht note [ZFC without parameters](https://www.math.uni-bonn.de/people/schlicht/ZFC_without_parameters.pdf), printed p.2, uses Pairing to amalgamate finitely many parameters and credits older work. It does not supply the EPSC2 resource bootstrap reviewed here. The report's combinatory and class-theory alternatives remain separate proposals with their explicit calibration and compilation costs.

## Complete tableau and exact four-slot interface

The public parser accepts Bottom, binary relation, implication and universal binding. Matrix scope is checked at depth four, with arbitrary nested binders. Booleans, equality, holes and malformed arities do not enter the public matrix grammar. The three wrapper projections are (2,0,4,3), (1,0,4,3), and (0,1,4,3), in their five-binder contexts; each exposes exactly [x,y,p,q]. Entering a matrix resets the template environment, then its own binders prepend values normally. Virtual exposure and expanded formulas preserve certificate entry numbering.

The public refutation object has exactly the keys matrices and proof. It reconstructs all positive EPSC2 roots itself. Arbitrary signed roots are confined to a generic logical-test helper. Branching implication checks both subtrees. Only positive Bottom or complementary atoms with exactly the same evaluated ordered pair close a branch. Initial parameter 0 ensures nonempty-domain semantics. A positive universal may use an existing parameter or exactly the next unused parameter; a negative universal always uses that fresh parameter. Branch-local counter extensions are independent, which does not identify names or assume distinct denotations.

The numeric codecs terminate mathematically by strictly decreasing recursive children. Formula codes are Bottom0, Rel=1+3P, Imp=2+3P, All=3+3child. The list/proof decoders also decrease. Every finite valid certificate is eventually enumerated. Finite prefix tests establish no consistency theorem. Python recursion or memory failures propagate and cannot become accepted refutations. The report's fair-tableau argument supplies ordinary soundness/completeness, not a verified Python interpreter or compiled binary endpoint.

The wrapper has 49 tree nodes (36 distinct), with three matrix holes: 12 universals, 10 Bottom leaves, 18 implications and 6 relation leaves. Expansion has 46+3m tree nodes for an m-node matrix. These are declared syntax metrics, not machine-state counts.

## Exact initializer argument

For nine nonnegative register values of sum S and positive n,m, the proposed initializer has

    gap G = n(m+2)+2,
    states = S+28+2n+m,
    steps = S+28+6n+(m+2)n(n+2).

Registers are printed in physical order (2,4,3,7,6,8,0,1,5). Relative to the header, iteration j has frontier −(2n+3)−jm and next counter −(2n+1)+2j, separated by 2+j(m+2). The right scan erases that counter, the left scan erases the old frontier, and the stride writes exactly one new frontier. After all counters are consumed, the adjacent auxiliary/header pair distinguishes termination; cleanup erases the auxiliary. This inductively accounts for every written cell and the blank exterior, rather than extrapolating from finite tests.

Setup costs S+22+2n states; the common loop costs 4, stride m, cleanup 2. Iteration costs sum to (m+2)n²+4n, and cleanup costs 2G+2, giving the displayed exact time. For required gap102, 2n+m≤26 implies n(m+2)≤98, which is insufficient. Cost27 has exactly (n,m)=(6,15),(7,13),(8,11); their gaps are104,107,106 and times excluding S are880,1015,1116. Thus (6,15) is the fastest state minimizer in this construction.

All 572 labeled runtime rows are unchanged under numeric relabeling. The clean assembler becomes 286 runtime +55 initializer =341 states for its zero vector and343 for the next-proof value2. The earlier 408-state control used a different 122-state initializer. One cannot subtract this67-state saving from the already optimized public253. These tables do not execute the proposed EPSC2 checker. Affine register-box tests remain conditional on their explicit frame contracts and are not arbitrary-tape runtime proofs.

## Reproduction and current status

The isolated full functional replay passed in14.647 seconds. All reported functional JSON and both binary tables matched the delivered outputs. The suite covered145 matrices,2610 direct schema comparisons,69600 projection cases,145 virtual/expanded certificate comparisons,11 adversarial rejections,10000 formula and10000 proof roundtrips, and a2000-candidate prefix. Its two positive logical certificates are not theory refutations. Initializer checks covered864 whole-frame configurations,300 exact optimizer cases, and8391 affine cases for each table.

Current Lean has advanced beyond the manuscript pin: `Boot253.fullBootstrap253` proves the complete312975-step literal public253 bootstrap and whole tape representation, while excluding the RM330 correspondence, general runtime and consistency endpoint. Conditional full-equality named-calculus completeness is also now present under explicit propositional-basis assumptions. Neither result certifies EPSC2, this numeric codec, its tableau, or its binary implementation. Existing raw PSC semantic resources and extensional calibration are predecessors, not a completed two-slot interpretation.

The manuscript is a complementary addition to the closure-kernel host. No delivered claim requires a mathematical retraction. Preserve its open one-slot question and its artificial-theory alternatives. The practical next comparison is the whole EPSC2 checker against the protected-rule and quantified-NAND frontends with initialization, arithmetic, branching and freshness all charged.
