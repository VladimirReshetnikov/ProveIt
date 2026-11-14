# Independent theory and compiler audit

## Scope and conclusion

I independently read the unary theory's complete lower interpretation and the
upper proof-transport argument, then followed the exact mathematical dependency
chain retained by the 209-state proposals. I found no substantive mathematical
defect in the portions reviewed. The appropriate proof status remains:

* ordinary mathematical proofs whose syntactic and simulation arguments are
  formalizable in PA;
* executable finite reconstruction, literal local equivalence, and symbolic
  induction checks for specific machine tables;
* no newly exported end-to-end Lean, Rocq, or MM0 certificate for a U209 table.

The fixed K215 formal endpoint does not certify a modified U table. It is the
unchanged generic logic, arithmetic-macro, and proof-search interfaces that are
transferred, with a separately proved new nonlogical emitter and separately
verified physical table.

Source snapshot: ProveIt commit
`343da82d7384d10ec9fd1c17361fc923b2d1d117`. All paths below are relative to the
current workspace. The exact retained lineage was obtained from:

`sources/extracted/U209_ConPA_2026-10-29/U209_ConPA_2026-10-29/reference/U211_ConPA_Contextual_2026-10-28.zip`

then, successively, its `baseline/selected_U212.zip`,
`inputs/parent_U213_ConPA_2026-10-28_1.zip`,
`inputs/U214_ConPA_Reduction_2026-10-28.zip`,
`inputs/U218_ConPA_2026-10-28.zip`, and
`inputs/U222_ConU_2026-10-28.zip` (each relative to that archive's top directory).
Selected texts were materialized under `research/theory_lineage/` for review.

## 1. What unary U asserts

In equality-free classical first-order logic over a nonempty domain, with one
binary relation E, put Sub(x,a) := forall t (E(t,x) -> E(t,a)). For every matrix
phi with at most x free, U has:

    forall a exists b [forall x (E(x,b) -> phi(x))
                      and forall x (Sub(x,a) -> (phi(x) -> E(x,b)))].

No source parameter or arbitrary ambient parameter is permitted in phi. This
restriction applies to free variables, not the number of bound variables or
quantifier complexity. The cover may include additional phi-objects that are
not subsets of a. Therefore the ordinary exactification shortcut replacing phi
by Sub(x,a) and phi is illegal for U.

Primary text:
`sources/extracted/pa_unary_power_cover/pa_unary_power_cover/sections/overview.tex`.

## 2. Review of the lower interpretation

The construction uses coextensionality x~y (same member profile), saturated
objects, and numerical representatives that are transitive and linearly ordered
by membership on coextensionality classes. An endpoint condition says that each
nonempty intersection of an existing object's profile with a numerical initial
segment has least and greatest member classes. This is an internal first-order
property, not external well-foundedness or external finiteness.

The main logical difficulty is handled in the correct order:

1. False filtering supplies an empty object. Numerical classes are hereditary;
   every nonempty number has a greatest predecessor. Existing successors are
   numerical and unique modulo coextensionality, without assuming totality.
2. A legal unary filter of failures proves induction using only existing
   successors. If failures occur below a counterexample n, their least class
   gives a contradiction via its predecessor. If none occurs below n, n itself
   has a predecessor satisfying the induction predicate. No successor of n is
   needed.
3. Parameters in theta(v,p) are internalized by the unary formula
   forall p (BaseAndStep(theta,p) -> theta(v,p)). This gives induction even for
   predicates not invariant under coextensionality. The proof does not assume
   saturation of the failure cover.
4. Induction gives global comparison of numerical classes and least numerical
   witnesses; fixed finite tuples are minimized lexicographically. Tuple
   notation is a finite list of variables, not an assumed coded tuple object.
5. For an invariant numerically parameterized target chi(z,n), failure of exact
   comprehension has a least failing tuple r. The unary matrix
   exists n (LeastFailure(n) and chi(z,n)) is extensionally chi(z,r).
   A separately supplied support source a contains every selected z as a subset;
   filtering at a therefore gives the forbidden exact object. All parameters
   are bound inside the matrix. This is a syntactic classical argument, not a
   computation of a least failure or a truth predicate.
6. This conditional comprehension gives total successors and exact powers of
   numerical sources. Their support condition is explicitly proved; no power
   axiom for arbitrary ambient objects is inferred.

Singleton, pair, and Kuratowski ordered-pair objects contain all representatives
of their selected classes. The decoding argument still distinguishes ordered
coordinates when they coincide. Pair codes with coordinates in n are subsets of
an exact power W of n, providing the support needed for graph comprehension.

Canonical histories bind the previous graph under an existential quantifier,
leaving only numerical free parameters. History uniqueness is proved before
history extension. The numerical value bound is separate from the terminal
value, so the iteration argument does not silently assume monotonicity. These
histories supply total functional addition and multiplication modulo
coextensionality, their recursion equations, and every translated PA induction
instance.

Primary texts: `sections/unary_core.tex` and `sections/unary_arithmetic.tex`
within the unary theory package. The review found the obvious circularity,
freshness, arbitrary-parameter, and graph-restriction pitfalls addressed rather
than assumed away.

## 3. Upper interpretation and the internal PA statement

Interpret E(x,a) by bit x of a. PA proves Sub(x,a) -> x<=a and global
irreflexivity. For each fixed arithmetic formula theta, induction forms a
binary characteristic code for the theta-selected integers through a. This
gives exact filtering, including for arbitrary matrix parameters. Because the
argument uses PA's own induction schema, it applies in nonstandard PA models;
it does not rely on an external finite-domain model or a uniform truth predicate.

The source describes primitive-recursive proof transformations in both
directions. Their ingredients are fresh-name selection, substitution,
relativization, operation-graph translation, insertion into fixed proof
templates, and induction through a finite derivation. Only finitely many lower
comprehension targets establish the fixed arithmetic interpretation; translated
PA induction instances use the uniform parameter-internalization template.
Thus the advertised endpoint is the internal syntactic assertion

    PA proves Con(U) iff Con(PA).

This is stronger than standard-model equiconsistency. The packet supplies the
ordinary uniformity argument, not an executable arbitrary-proof translator or a
kernel-checked proof of that internal assertion.

Primary text: `sections/upper_transport.tex` in the unary theory package.

## 4. The actual machine-facing theory

The U209 machines do not implement the unary packet's positive dyadic
nine-multiplication emitter. They preserve the native Cantor-coded calculus,
with truth alias 0, target 1, seven logical rows, a dominated propositional row,
modus ponens, generalization, and a gated cover/vacuity bundle.

Its ordinary calibration uses W+IR: the weak-cover schema permits arbitrary
matrix parameters, and IR is global irreflexivity. The internal consistency
reductions are

    Con(PA) -> Con(W+IR) -> Con(U) -> Con(PA).

The first arrow is the bit interpretation, the second uses U's inclusion in W,
and the third is U's lower interpretation. Equality-containing matrices are
harmless in the upper bit interpretation.

For the U214 role-reassigned emitter, matrix code and output label are a,
source label b, tested label c, with c unequal to a,b. Code a is self-fresh:
every effective variable label in its decoded matrix is below a (with a=0 the
closed truth alias). If a differs from b the guard expresses subset. If a=b,
the binder captures the source within the guard, yielding emptiness under IR.
A cover at an empty source proves this exceptional instance. This includes
small codes zero and one. The bundled atomic membership vacuity remains valid
under the gate.

Completeness pads a desired matrix to code n>1 and uses (a,b,c)=(n,0,1), then
undoes the logical padding and naming normalization. The retained logical
templates recover unrestricted dominated rows and implement equality via
two-sided membership indiscernibility; they do not incorrectly infer all
primitive-equality vacuity from membership vacuity alone.

Primary texts: `research/theory_lineage/U222/paper/report.tex`,
`research/theory_lineage/U222/references/logic/README.md`, and
`research/theory_lineage/U214/proofs/role_emitter.tex`.

## 5. Exact source and proof-search transfer

The U213 source replaces the old 1,597-primitive Theory K emitter region with
the calibrated 774-primitive U214 subtree. A finite source comparison binds all
copied emitter instructions and all retained exterior successor edges. The
result has 3,909 primitive occurrences. The surrounding source keeps the AX
interface, gate, and ten-entry stack effect used by the proof compiler.

The three-command compiler uses a strong completeness invariant: a compiled
theorem X either halts early or returns top X with the *arbitrary* original
stack restored after counter/cache reset. This avoids needing incoming data to
be theorem-valued for completeness. Raw zero aliases are separately handled
(J(0) is empty because MP(0) would succeed). For cache-return modus ponens a
disposable zero is reserved before evaluating the premises, so the final
transfer does not pop an arbitrary original stack head.

Successful command words have cofinal numerical candidate codes, and residual
continuations descend. Hence any finite candidate cutoff and persistent
arbitrary underlying stack preserve completeness.

Primary texts: `research/theory_lineage/U213/proofs/source_transport.tex` and
`research/theory_lineage/U213/proofs/compiler.tex`.

## 6. Startup: an important genuine dependency

The shortened initializer starts inside AX. Its incoming cache 1 is an
arithmetic parameter, not a theorem. The retained physical bridge identifies
the observed source ordinal 136/store with 141 source steps from ordinal 106
and logical store (N,T,W,A,D,H,X,Y,L)=(1,0,4,0,0,1,0,0,1).

The interior suffix constructs nine explicit theorem heads above opaque tail 4,
then reaches scheduler candidate 1 with counter/cache zero. A ghost explicit
stack length is maintained because P(0,0)=0 prevents unique recovery of list
length from the numerical code.

The all-natural scheduler proof assigns conservative stack weights S=-1,
MP=0, AX=10, resolves the first candidates explicitly, and uses Cantor diagonal
blocks for later candidates. Starting at candidate 1 the maximal prefix debt is
2. Therefore nine initial theorem heads leave a permanent conservative margin
of seven; the unsafe tail 4 is never exposed. This is the soundness reason, not
a finite blank-tape trace or an assumption that 4 is a theorem stack.

Primary text: `research/theory_lineage/U213/proofs/startup_suffix.tex`.

## 7. Consequences for a further state reduction

For a new candidate, state a new literal reduction theorem first, with its exact
scope (local arbitrary-exterior finite stuttering, source-control conjugacy,
universal primitive simulation, and blank-start bridge as appropriate). Then
compose with the preceding retained calibration to obtain

    PA proves not Halt(M,blank) iff Con(U) iff Con(PA).

No consistency hypothesis is needed for this biconditional. Claiming the
machine actually never halts additionally uses Con(PA).

The unproved-in-a-kernel portion is the complete end-to-end formal artifact,
not an identified missing mathematical lemma in the reviewed proof. Universal
symbolic induction certificates are stronger than bounded register tests, but
remain dependent on the soundness of their checker and mathematical induction
rules. A proof assistant's endpoint and a Python replay receipt must not be
described as equivalent verification products.

No new theory-level modification reviewed in this audit yields a proved
literal state saving. In particular, the smaller positive emitter in the unary
packet is not already implemented by these native tables. Treating it as a
state reduction without its compiler and startup proofs would overstate the
result.
