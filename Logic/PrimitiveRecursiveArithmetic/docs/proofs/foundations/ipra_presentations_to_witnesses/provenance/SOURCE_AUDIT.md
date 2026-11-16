# Targeted audit: what the new framework can add

Repository snapshot: `VladimirReshetnikov/ProveIt` at
`b0f6f535ffc16324683fef2c263260a88ae03755`.
All paths below are relative to
`Logic/PrimitiveRecursiveArithmetic/docs/proofs/` unless explicitly stated.
This is a targeted mathematical source review, not a validation of every
packet or a claim of historical mathematical priority.

## Strongest incremental contribution

The current collection already develops the following ideas: bounded-formula
Booleanization; finite query and demand scheduling; fixed evaluator schemas;
finite contract composition; exact and approximate certificate interfaces;
apartness-controlled arithmetic; analytic simple branches; metastability;
finite Hausdorff root supports; coherent filtered lifting; Hurwitz coefficient
recursions; weighted algebraic norms and proper-subspace zero counts. These
should be credited as prior material, not repackaged as the new contribution.

Two useful output upgrades appear not to be made explicitly in the targeted
sources reviewed:

1. A finite algebra spanning certificate already encodes enough information
   to compute a complete rational-point list. Clearing multiplication-table
   denominators bounds coordinate denominators; an integer eigenvalue
   argument and row/column sum bound locate the points in a finite lattice.
   Independence of the spanning generators is unnecessary. This strengthens
   the deployed certificate's output from cardinality to actual enumeration.
2. A supplied nonzero multiplication norm for a monic plane equation and
   section likewise yields complete rational intersection enumeration.
   Enumerate rational roots of the norm using leading and first nonzero
   coefficients, then enumerate roots in each monic fiber and filter by the
   section equation. The norm's sharper degree/fiber count remains useful
   but is not needed for enumeration completeness.

The second theorem is developed in `research/sections_norm.tex`. The first
is being developed separately by the framework mathematics agent.

## Precise antecedents and difference

### Finite algebra certificates

`foundations/ipra_embedding_framework/paper/05_diophantine.tex`, subsection
“Finite algebra certificates as a general zero-count interface”, defines
polynomials `b_1=1,...,b_D` and coefficient-checked identities
`X_k b_j - sum_i m_kji b_i = sum_l u_kjl F_l`.
Its theorem asserts that every supplied distinct rational-zero list has
length at most `D`; the proof constructs interpolation vectors and performs
finite row reduction. It explicitly permits redundant generators:

> Linear independence of the $b_i$ is not required

The source's final discussion separates certificate verification from
construction and refuses to infer an iPRA complexity bound from an
unspecified Gröbner-basis invocation. The proposed lattice enumeration
theorem uses *the same supplied certificate* and therefore resolves no
unproved general certificate-generation claim. It extracts stronger positive
information from data already present.

`algebra/cayley_hamilton_ipra/sections/applications.tex`, section “Finitely
generated modules and integral elements”, already proves a determinant trick
without a basis and constructs monic annihilators from multiplication tables.
This is an algebraic antecedent. The finite rational lattice and exhaustive
point enumerator are the additional interface. The elementary primitive
integer eigenvector proof avoids importing that determinant theorem.

### Algebraic norms

`foundations/ipra_finite_demand/sections/05_norm_certificates.tex` constructs
the general multiplication norm for an equation monic in `Y`, proves
fiber-sensitive zero counts, and automatically certifies norm nonvanishing
for coprime superelliptic weights. It explicitly separates these results
from a global point list and height cutoff.

`foundations/ipra_coherent_methods_2026-11-15/paper/sections/05_norms.tex`
extends the weighted argument to lower-weight mixed terms. Its discussion
states the endpoint as:

> cardinality bound on arbitrary supplied lists, not a height bound or a complete enumeration of all points.

The proposed norm-to-list theorem does not contradict that statement: a
specific section gives coefficient data from which a rational-root bound can
be calculated; a tuple-local existence assertion supplies no fixed family of
sections covering every unknown point. The difference in quantifiers must be
made explicit.

`foundations/ipra_finite_observation/tex/sections.tex` also gives bounded
annihilator construction and superelliptic section counts. Its annihilator
coefficient majorant depends on the heights of the input spanning matrix.
That is enough to enumerate a supplied section, but supplies no curve-only
bound for all exceptional subspaces.

## Application boundaries and genuine unresolved obligations

| Area | Inspected obligation | What the new work changes | What remains |
|---|---|---|---|
| Explicit finite polynomial systems | The old spanning certificate gives a rational zero count. | An accepted certificate computes a denominator lattice, a coordinate bound, and all rational zeros. | Producing a certificate for an arbitrary zero-dimensional ideal; positive-dimensional systems without an extra equation are outside this interface. |
| Explicit curve sections | The norm packets bound the number of common zeros. | Nonzero norm plus exact rational coefficients computes all rational common zeros, including repeated or singular fibers. | No conclusion from an identically zero norm; no assumption that rejection means infinitely many rational points. |
| Siegel finite-cover route | Every supplied finite tuple should admit a bounded cover; its approximation theorem is unproved. | Once concrete section polynomials are supplied, each section can be exhaustively solved. A single global cover gives all points. A uniform coefficient bound for annihilators also suffices. | The finite-tuple approximation theorem, global cover information or equivalent coefficient-height bounds, local case splits, and covering/lifting arguments in the general case. |
| Faltings | A general complete point list or height bound is not supplied. | Concrete zero-dimensional intersections and globally certified finite covers can be completed. | General curves are not thereby equipped with global covers or effective height bounds. No independence result is inferred. |
| Mordell–Weil | The existing descent theorem assumes an actual finite rational-point list covering `E(Q)/2E(Q)`. | Finite intersections appearing inside a separately justified descent certificate can be solved exactly. | Finding rational points on all relevant covering curves and proving they represent all quotient classes. Those covers are generally positive-dimensional. Solving a finite slice is insufficient. |
| Puiseux / roots | Exact Puiseux coefficient selection from arbitrary Cauchy coefficients is uniformly uncomputable. | None claimed here; prior simple-branch and root-support interfaces remain the applicable repairs. | Multiplicity-sensitive root multiset matching is a possible separate target. Global labels and exact singular coefficients do not follow from support continuity. |
| Metastability | Prior packets give stable finite windows, not a Cauchy rate. | None claimed here; finite data and global completion remain different interfaces. | No general rate extraction from a metastability bound alone. |
| Prime distribution | Effective Chebotarev/Siegel–Walfisz/Bombieri–Vinogradov contracts remain open in these packets. | The algebraic finite-data framework may support later certificates. | Uniform analytic witnesses, exceptional-zero input and complete mean-value estimates are not generated by coding or certificate checking. |

### The exact Siegel source

`diophantine-number-theory/siegel_ipra/paper/05_general_route.tex`, sections
“A finite covering lemma”, “Why finite covers can have finite certificates”
and “Explicit unresolved obligations”, states the tuple-local covering
contract and its finite candidate-space argument. Candidate subspaces are
spans of subsets of the *given tuple*, so their coefficients can inherit the
tuple's unknown heights. The finite candidate count does not provide a
global coefficient-height bound.

An effective coefficient bound would be enough in the following precise
sense. For `r` fixed reduced monomials and a fixed integer `C`, enumerate
every nonzero integral annihilator vector with coordinates in `[-C,C]`.
There are at most `(2C+1)^r-1`. In the weighted coprime family each associated
nonzero section has nonzero norm. If every desired point lies on some one of
these sections, their computed intersection lists exhaust all points. No
preferred global cover need be chosen. This isolates an additional
quantitative theorem which would bridge the remaining gap; it is not
deduced from the present tuple-local cover assertion.

### The exact Mordell–Weil source

`diophantine-number-theory/mordell_weil_ipra/paper/03_elliptic.tex`, section
“The supplied-cover constructive elliptic Mordell–Weil theorem”, starts
with rational representatives satisfying `Cover_E(R)`. Its halving algorithm
then constructs descent witnesses and a finite generator list. Both that
section and `foundations/ipra_coherent_methods_2026-11-15/paper/sections/07_status.tex`
keep production and coverage of the representatives as a separate arithmetic
existence obligation. A Selmer-style finite list of *covering equations* is
not the required list of *rational points*.

### The exact analytic source

`analytic-number-theory/prime_distribution_ipra/paper/sections/07_sw_bv.tex`
contains the witness-preserving reduction from effective BV to uniform
small-modulus power saving and identifies the missing effective Siegel-type
input. It correctly distinguishes one exceptional conductor from all of its
multiples and retains precision error in finite rational sum bounds. A new
general framework should not erase those quantitative hypotheses.

## Formal proof status

The current top-level `Logic/PrimitiveRecursiveArithmetic/README.md` says
the foundational ConciseIPRA library is kernel checked, while the research
packets were placed as delivered. No packet currently supplies a complete
new mathematical derivation in `Prf PRAAx`.

The new report should keep four statuses separate: a complete human
arithmetic argument; checked exact finite examples; host Lean theorems;
and actual object-theory derivations. A supplied object proof of a global
cover can be transformed into a point-list proof, but a verifier must not
silently interpret arbitrary successful proof checking as arithmetic truth.

## Review scope

Read all nine foundations READMEs; read the indicated full source sections;
searched the complete local foundations text for rational-root,
denominator/matrix, norm/enumeration, complete-list and height formulations;
checked relevant Cayley–Hamilton and number-theory source sections. This
supports the narrow claim of an additive connection relative to the
inspected material. It is not a literature search establishing novelty in
mathematics, nor a full correctness audit of all sixty packets.
