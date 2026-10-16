# Mira’s transitive and power-bounding containers

The user supplied [this screenshot](references/mira-containers.png), attributed
to Mira, on 16 October 2026. The screenshot is research input. The arguments
below are an independent mathematical audit, not claims of a new formal proof.

Independent calibration audit, 16 October 2026

## Scope and conclusion

For the formulas in the supplied screenshot, both equiconsistency claims
have mathematical proof routes. They are not new machine theorems, and no
formal proof object is supplied here. The PA claim does not assert that
all sets are finite or that the theory proves negated Infinity. The ZFC
claim does not assert deductive equivalence with ZFC: Foundation and Choice
still require the standard relative-consistency interpretations.

Write T = E# + C_T + GIC and U = E# + C_P + GIC. All schema matrices must
allow arbitrary finite parameter tuples; the displayed domain/witness
variables are fresh for the matrix.

## Equality elimination

Let x~y mean forall z(z in x iff z in y). This is always an equivalence
relation. E# gives congruence in the left membership argument; its definition
gives congruence in the right. Induction on formulas gives invariance under
~. Replacing logical equality by ~ therefore interprets the equality-bearing
extensional versions of T and U in their equality-free versions. The
translated Extensionality axiom is a logical tautology, and each translated
GIC matrix is permitted. Conversely ordinary Extensionality implies E#.
Thus it suffices to work with actual equality and Extensionality below.
This is a syntactic interpretation; it need not choose quotient representatives.

The one-sided EC sentence used by the incoming reports suffices for E#:
symmetry of ~ supplies the missing direction of the conclusion.

## Constructions already available from C_T + GIC

Empty: take the false matrix; the global-image clause forces b empty.

Separation in A: use theta(x,y) = (x in A and psi(x) and y=x), with GIC
domain A. Every desired x must be included, and the image clause excludes
everything else. This yields the exact subset, including the empty case.

Singleton {c}: choose a C_T-container V containing any object t. Use
theta(x,y) = (x=t and y=c), with GIC domain V. The witness contains c,
and image purity makes it exactly {c}.

Pair {a,b}: let e be empty and s={e}, so e differs from s. A transitive
C_T-container V with s in V contains both e and s. Apply GIC over V to
(x=e and y=a) or (x=s and y=b). This gives exactly {a,b}. A two-output
constant relation would not suffice: GIC can select only one output.

Union A: take transitive V with A in V. All y in x in A belong to V;
Separation in V gives the exact union.

Partial functional Replacement on A: use the guarded matrix
theta(x,y)=(x in A and R(x,y)). Functionality forces every output into
the GIC witness; image purity excludes all other outputs. Total functional
Replacement is a special case. The same guarded construction gives full
Collection, but none of the arguments silently identifies Collection with
Replacement in foundation-free set theory.

Consequently T contains the elementary set theory EST (Extensionality,
Empty, Pairing, Union, full Separation and Replacement) plus transitive
containment. It need not prove Foundation, Power Set, or Infinity.

## PA upper bound for T, directly

In PA use Ackermann membership i E n iff bit i of n is 1, on all natural
numbers. Binary extensionality proves E#.

A literal C_T-host of a is v=2^(a+1)-1: a E v, and every x E v satisfies
x<=a; any u E x satisfies u<x<=a, hence u E v. PA proves these facts.

For each fixed translated arithmetic matrix theta(x,y,p), PA proves GIC
by induction over x=0,...,a. Start with empty output code. If x E a and
exists y theta(x,y,p), choose one such y and adjoin it; otherwise retain
the output code. At each stage all accumulated outputs satisfy theta for
some processed input, and all processed nonempty fibers have a selected
output. PA proves the code adjunction operation total using exponentiation.
The final code is the required b. This argument uses ordinary PA induction
for the fixed matrix, not a decision procedure for truth of theta.

Thus PA interprets T. Merely observing externally that HF models T would
not by itself establish this effective relative-consistency direction.

## PA lower bound for T, without assuming global Foundation or Infinity

In EST define Ord(n) to mean that n is transitive and membership well-orders
n. In the absence of Foundation, retain the well-foundedness clause: the
usual abbreviated transitive-and-linear definition is not adequate here.

Define N(n) to mean Ord(n) and every ordinal u<=n is either empty or a
successor ordinal. Here u<=n means u in n or u=n. This class contains
empty, is successor closed, and all its initial segments remain in N.

Full induction holds for this definable class. Given a counterexample n
in N, Separation forms {u in n+1: not phi(u)}. The ordinal well-order
supplies its least element u. Since u<=n, u is empty or a successor; the
base/step hypotheses contradict minimality. Parameters in phi are allowed.

Finite graph recursion on n in N is now proved by this class induction:
extend a graph one ordered pair at a time using Pairing and Union;
uniqueness follows by least disagreement. Successor iteration defines +,
and iteration of addition defines multiplication. Their recursive equations,
successor injectivity/nonzeroness, and full induction give the PA axioms.
This is a standard ordinal interpretation, with an explicit finite cut
because T does not assert that every ordinal is finite.

Both directions are fixed formula interpretations with uniform schema
proofs. Their finite proof transformations are primitive recursive and
can be verified in PA under ordinary fixed proof predicates. Therefore
the screenshot's PA equiconsistency has a paper-level justification.

## ZFC calibration for U: where Infinity enters

C_P includes C_T, so all constructions above apply. For A, choose its
container V. The extra C_P clause gives B in V containing every subset
of A; Separation in B forms the actual P(A).

Fix a C_P-container V with empty e in V. If x in V, every subset z of x
belongs to a bound B in V and therefore belongs to V by transitivity.
Moreover actual P(x) is a subset of that B; subset closure applied at B
puts P(x) itself in V. Thus V is closed both under taking individual
subsets of its members and under the actual power-set operation.

For a well-founded ordinal alpha in V, alpha union {alpha} is a subset
of P(alpha): every beta in alpha is a subset of alpha, and alpha is one
too. Since P(alpha) in V, subset closure places the successor in V.
Separation forms O={alpha in V: Ord(alpha)}. It contains e and is
successor closed, so O is an inductive set. This derives Infinity without
first presupposing a set of natural numbers or global Foundation.

Hence U proves ZF with Foundation and Choice omitted (and in fact has
additional Collection consequences). The standard well-founded-hierarchy
and constructibility interpretations supply the ZFC consistency lower
bound. This last bridge is established mathematics, not a new formal
implementation in the repository.

Conversely ZFC proves U. For a seed a, V=V_(rank(a)+omega) is a transitive
container with the required power bounds. Ordinary ZFC Collection proves
GIC after guarding its matrix by the domain a; Separation removes junk.
No Choice is needed just to select the collection witness. This gives the
upper bound and the claimed ZFC equiconsistency.

## Relation to sources and formal status

Kaye and Wong, 'On interpretations of arithmetic and set theory' (expanded
2006 manuscript; NDJFL 48(4), 2007, 497-510), is a primary source for the
Ackermann and ordinal interpretation architecture. Its EST is defined
on p.3; Theorems 3 and 8 give the two familiar finite-set directions;
Sections 5-6 explain why transitive containment matters for stronger
inverse/bi-interpretability claims. Its published finite theory includes
Foundation and negated Infinity, so it must not simply be cited as an
identity with T. Sections 2-4 above give the necessary bridge for T.
Primary manuscript:
[Kaye–Wong primary manuscript](https://cpb-us-w2.wpmucdn.com/blog.nus.edu.sg/dist/4/10956/files/2019/01/finitesettheory-1i2tx5t.pdf)
[Published paper](https://doi.org/10.1305/ndjfl/1193667707).

Repository PAHF uses a different theory. In
Logic/Interpretability/PAHF/Lean/PAHF/AckermannHFCore.lean:1502-1522,
HFAx_s includes foundation-style set induction and HFFinAx_s adds
finite-generation induction. These are useful machinery, not a checked
theorem about screenshot T or U. No repository proof assistant has been
run for the claims in this note. No new TM or state estimate follows.


## Exact formulas from the screenshot

Write `x⊆y` for `∀u(u∈x→u∈y)` and `D(x,y)` for equal predecessor profiles.

- `E#`: `∀x∀y(D(x,y) → ∀z(x∈z ↔ y∈z))`.
- `C_T`: `∀a∃V(a∈V ∧ ∀x∈V x⊆V)`.
- `C_P`: `∀a∃V(a∈V ∧ ∀x∈V(x⊆V ∧ ∃y∈V∀z(z⊆x→z∈y)))`.
- `GIC(θ)`: `∀a∃b[∀y∈b∃x θ(x,y;p̄) ∧ ∀x∈a(∃y θ(x,y;p̄)→∃y∈b θ(x,y;p̄))]`.

All matrices are equality-free in the screenshot theory. Parameters are
arbitrary finite tuples and `b` is fresh for θ. The order of the two GIC
conjuncts changes no deductive content. Its existence gate is equivalent
in classical logic to the benchmark's universal-output gate.

The one-sided alternative `D(x,y)→(x∈z→y∈z)` is enough, with universal
x,y,z or theorem-only open instances: swap x,y and use symmetry of D for
the other direction. This is a provable formula simplification, whose
machine cost depends on the logical engine and how instances are emitted.

The imported machine searches a different presentation: CP+GIC with logical
equality and irreflexivity, using a bisimulation interpretation instead of
E#. No screenshot equivalence justifies deleting those machine rules or
its freshness gates without rebuilding the associated proof.

## The MathOverflow predecessor and seed convention

The corrected [question](https://mathoverflow.net/questions/380000/is-this-set-theory-equivalent-to-zfc)
uses a set seed `s⊆w`. Glazer's answer uses a rooted seed `s∈T`, and its
edit explicitly says that the rooted version follows using singletons
from Separation and Power Set. The answer also records an earlier reversal
of the relation arguments. Keep input/output order explicit when reusing it.

The repository already formalizes that predecessor in
`SetTheory/ClosureAxiomatization`; see the intake reconciliation for exact
paths and declarations. The new [subset-only kernel](subset_only.md)
produces singletons directly, derives Power Set from a constant all-subsets
fiber, and uses a positive singleton-decoding hull for Separation and Union.
The latter hull contains the members of the initial root, even though it
need not contain the root. These are separate parts of the bootstrap.
