# Independent audit of the U/PA calibration

Prepared for the sub-208-state comparison, 29 October 2026.

## Scope and conclusion

I read the complete mathematical sections of the supplied
`pa_unary_power_cover/pa_unary_power_cover/` package, the calibration in
`U208_ConPA_Conditional_Context_2026-10-29/u208_conpa_2026-10-29/paper/calibration.tex`,
and the retained U214 role-emitter and U213 source/compiler/startup proofs.
The latter four texts were extracted without modifying upstream into
`analysis/theory_lineage/`; its manifest records each exact nested archive
path and SHA-256.

I found no fatal mathematical error in these arguments. The strongest
justified description is an ordinary mathematical proof with explicit
uniform syntax and induction arguments sufficient for PA formalizability.
There is no newly compiled end-to-end Lean, Rocq, or MM0 proof for U208.
The existence of the separate formal K215/Con(ZFC) result does not supply
such a proof for a changed theory or table.

No theory modification examined here yields a proved literal state saving.
The local-machine reductions can therefore keep the existing calibration
and give a cleaner result than changing both the theory and interpreter.

## 1. Three different theories/interfaces must not be conflated

The underlying unary theory U is equality-free classical first-order logic
over nonempty domains, with one binary relation E. Its axiom schema is

    for all a, exists b,
      [for all x, E(x,b) -> phi(x)] and
      [for all x, Sub(x,a) -> (phi(x) -> E(x,b))],

where `Sub(x,a) := for all t, E(t,x) -> E(t,a)` and the only possible
free variable of phi is x. Arbitrary bound variables are allowed. The
source a is forbidden as a free matrix parameter. The cover need not
be an exact subset filter.

The **current native U208 machine** retains the Cantor-coded calculus
with truth alias 0 and refutation target 1. Its ordinary theory is W+IR,
where W permits arbitrary matrix parameters and IR is global
irreflexivity. The consistency calibration is the PA-provable cycle

    Con(PA) -> Con(W+IR) -> Con(U) -> Con(PA).

The dyadic **positive theorem stream** in the unary-theory archive is a
different implementation proposal, not the source compiled by U208. That
stream targets code 0, the atom E(v0,v0), and uses positive P together with
a metatheoretic seed `not D`, where `D := for all v, E(v,v)`. P alone has
a one-object total-relation model. Its ordinary consistency must never be
identified with Con(PA). The calibrated assertion is nonderivability of
the atomic target, equivalently consistency of P+not D.

## 2. Audit of the lower interpretation: PA in U

### Coextensionality and numerical objects

Coextensionality means equality of member profiles. It is always a
congruence in the second membership argument, and is a congruence in the
first argument only for saturated containers. The proof observes this
distinction and does not silently assume global extensionality.

Numerical representatives are saturated transitive objects, with saturated
members linearly ordered by membership modulo coextensionality, and an
endpoint condition on nonempty intersections with existing objects. The
endpoint condition ranges over the object and all its represented initial
segments. These are first-order conditions, not assertions of external
finiteness or well-foundedness.

The local lemmas correctly establish heredity, irreflexivity, greatest
predecessors, and uniqueness of existing successors before claiming that
successor is total. In the successor lemma the extra class is the entire
coextensionality class of the predecessor. Saturation is what makes this
an actual new maximal class and makes arbitrary representatives behave
correctly.

### Induction before successor totality

The proof filters the failures of a unary predicate at a numerical
counterexample n. Every member x of n is a subset of n by transitivity,
so the weak upper and lower clauses give the correct failure predicate
on the member profile of n.

If failures occur inside n, choose their least class and apply the
successor step to its predecessor. If no failures occur inside n, apply
the successor step from the greatest predecessor of n directly to n.
Neither branch requires a successor of n to have been constructed.
The argument also works when a predicate distinguishes coextensional
representatives: the base premise covers all empty representatives, and
the step premise covers all representatives of any existing successor.

For arbitrary ambient parameters p, the legal unary predicate is

    Q(v) := for all p, (BaseAndStep_theta(p) -> theta(v,p)).

The base and successor step of Q follow uniformly from their respective
components. This is a valid parameter-elimination argument, not an
illicit use of parameters in the nonlogical schema.

### Comparison, least failures, and bounded numerical comprehension

Induction first gives comparison of numerical classes using only existing
successors. An invariant predicate with a witness then has a least
numerical class. Each fixed finite tuple is minimized lexicographically
by finitely many uses of that theorem; no tuple-coding object is assumed.

For a target chi(z,n), bounded numerical comprehension has two real
hypotheses: invariance in its numerical parameter positions, and a source
a such that every selected z is a subset of a. If comprehension fails,
let r be the least failing tuple. The unary formula

    exists n, LeastFailure(n) and chi(z,n)

is extensionally chi(z,r). Its source is chosen separately by the support
premise. All n are bound, so there is no forbidden free source or graph
parameter. Filtering gives the supposedly missing exact output. This is
a fixed classical formula and proof template, with no semantic truth
predicate or syntactic self-reference.

Successor, powers of numerical sources, and a common numerical bound for
each fixed finite tuple follow in that order. The proof does not infer
powers of arbitrary ambient objects.

### Arithmetic graphs and histories

Singletons, pairs, and ordered-pair codes collect every representative of
the required coextensionality classes. Their exact profiles give valid
decoding, including equal-coordinate pairs. Ordered-pair codes with
coordinates in n are subsets of an exact power of n, which provides the
needed support for graph comprehension.

The history construction first proves pointwise uniqueness with existing
graphs as parameters of the already established induction theorem. Its
extension and restriction matrices bind the old graph existentially and
have only numerical free parameters. This correctly avoids filtering by
an arbitrary free graph parameter. A separate bound on all values makes
the argument valid for nonmonotone transition functions. Successor
iteration gives addition, addition iteration gives multiplication, and
representative induction supplies every translated PA induction instance.

## 3. Reverse interpretation and internal, not merely external, strength

Interpret E(x,a) as bit x of a. PA proves that translated Sub(x,a) implies
x <= a. For each fixed arithmetic formula chi, induction constructs its
binary characteristic code through a. This gives an exact filter and
hence U's weak cover. It even validates W with additional parameters.
PA also proves this relation irreflexive, since 2^a > a.

This is a formula-by-formula use of PA induction and works in nonstandard
PA models. It does not assert a uniform arithmetical satisfaction
predicate or decide an arbitrary formula.

Mutual interpretability by itself is not sufficient wording for the
requested internal equivalence. What matters is that the fixed lower and
upper derivations are uniform proof templates. Freshening, substitution,
term-to-graph translation, relativization, and finite proof concatenation
are primitive recursive. Formula induction and proof-length induction in
PA verify those templates. Thus the archive's intended statement is

    PA proves Con(U) iff Con(PA),

not just equivalence of consistency in the standard metatheory. The
archive does not implement all arbitrary-proof translations or deliver
their proof-assistant certificate. This is a verification-status
limitation, rather than an identified logical counterexample.

## 4. Native role-emitter calibration

The current emitter assigns matrix code and output label a, source label
b, and tested label c, with gate c != a,b. Effective labels in a positive
code are below that code, while code zero is a closed truth alias. This
makes the output fresh without scanning its matrix.

For a != b the guard is Sub(vc,vb). For a=b the guard's local binder
captures the source, yielding `for all va, E(va,vc) -> E(va,va)`, which
under IR is emptiness of vc. W supplies an empty source, so a weak cover
at that source verifies the exceptional shell. The cases a=0 and a=1
are explicitly covered: the first is closed truth, the second is false
under IR. No unchecked freshness assumption remains there.

The gate preserves atomic membership vacuity, and the other logical rows
are unchanged. Full equality reasoning is obtained through the inherited
two-sided membership-indiscernibility translation, not by silently
assuming full primitive equality vacuity. The dominated propositional
row must be retained; earlier packages already supply a Boolean
counterinterpretation for the calculus with that row simply deleted.

Completeness double-negates a desired matrix to a code n>1 and chooses
(a,b,c)=(n,0,1), then uses logical proof transformations to remove padding
and restore names. The matrix code/output label is fresh by the native
coding bound. These are finite syntactic operations and are suitable for
PA-internal proof transport.

## 5. Source and startup dependencies

The U213 source transport replaces the old closed emitter by the calibrated
774-primitive U214 emitter and checks all retained operations and resolved
successors. It preserves the scheduler return and the direct-transfer
contract. It does not infer a new theorem from the old literal K215 table.

The strong compiler works above arbitrary underlying numerical stacks
after an AX reset. It handles the zero alias P(0,0)=0 explicitly, notably
the zero exception when setting the additive counter. Successful
candidate codes are cofinal, so a finite initial cutoff preserves
completeness.

The shortened initialization enters an interior AX suffix. Its incoming
cache 1 is an arithmetic parameter, not a proved false sentence, and its
tail 4 is not theorem-valued. A finite source bridge and a uniform suffix
contract show that execution creates nine explicit theorem heads above
that opaque tail. A ghost explicit stack length is essential because
numeric pairing aliases do not recover list length. The all-natural
scheduler credit argument bounds prefix debt at two from candidate 1,
leaving margin seven. This protects the tail for arbitrary future runs.
The finite startup trace alone would not establish that fact; the
retained proof does provide the needed unbounded invariant.

## 6. Simple theory edits ruled out

These small countermodels explain why obvious source shortening is not
a justified PA-strength saving:

* Remove the lower covering clause: a one-object empty relation satisfies
  every remaining upper-filter instance, even with IR.
* Remove the upper filtering clause: a two-object directed 2-cycle
  satisfies IR and every remaining lower-cover instance. Each member
  profile is a different singleton, so Sub(x,a) is just x=a, and the
  other object can always be used as output to contain a.
* Replace Sub(x,a) by E(x,a): the one-object empty relation satisfies all
  resulting instances, even with IR.
* Remove the subset guard entirely while retaining both clauses: the
  unrestricted matrix not E(x,x) gives Russell's contradiction.

PA can verify the finite models uniformly, so these finite-model
weakenings cannot have the requested PA-provable Con(PA) calibration if
PA is consistent. These observations concern these exact edits; they are
not a lower bound on theory size or machine states.

Merging the two universal tests into a single conjunctive body is not a
proved implementation saving either: in the native implication/falsity
basis, its naive translation costs extra constructors. The separate
positive dyadic emitter has only nine nonlinear multiplications, but that
fact does not bound the states needed for a new parser, proof engine,
initialization, and literal binary-tape compiler.

## 7. Recommended theorem statement for a new reduction

First state exactly the newly established literal-machine equivalence:

    PA proves Halt(M_new, blank) iff Halt(M_selected_208, blank).

Identify its proof mechanism and the precise literal tables it relates.
Then compose with the retained ordinary mathematical calibration:

    PA proves not Halt(M_new, blank) iff Con(U) iff Con(PA).

The biconditional needs no consistency premise. A claim of actual
nonhalting does use Con(PA). An exhaustive finite local-context identity
with arbitrary tape exterior is stronger than testing a finite set of
runs, but an executable Python certificate checker is not automatically
a proof-assistant kernel. These distinctions should remain explicit in
the report and final response.
