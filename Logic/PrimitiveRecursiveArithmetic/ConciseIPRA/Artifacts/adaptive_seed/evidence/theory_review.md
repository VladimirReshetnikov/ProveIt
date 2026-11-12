# Independent mathematical review

## Scope and status

This review concerns the native theory and the inherited arithmetic bridge in `ipra_constructed_computation_2026-11-10.zip`, inspected in the current local ProveIt snapshot. It is a written mathematical review. It is not a proof-assistant verification, an independent external peer review, or a proof of the Python codec's complete soundness.

The reviewed mathematical presentation is an established ingredient of the supplied drafts. Restating it, combining its existing implementations, or remeasuring its sources must not be presented as a newly discovered axiomatization.

## 1. Exact native theory

Numerical terms are variables, `0`, `S t`, and `I(n,a;v.h)`. Only the update body `h` binds `v`. Its other parameters stay fixed. The staged first-order reading introduces one symbol for each fixed earlier body; there is no object-level universal evaluator or function quantifier.

The only arithmetic computation schemas are

\[
I(0,a;v.h)=a,\qquad I(Sn,a;v.h)=h[I(n,a;v.h)/v].
\]

Native formulas have grammar `Eq / Q / D`, with

\[
Q_y B \quad\rightsquigarrow\quad B(0)\to\forall yB(y),
\]

\[
D_{x,y}B \quad\rightsquigarrow\quad
\exists x\bigl(B(x,0)\to\forall yB(x,y)\bigr).
\]

The primitive logical rules are hypothesis use, equality transport through a fixed arbitrary formula template, Q elimination using its zero premise, D elimination to a fresh witness and its retained Q clause, and the two D introductions:

- Case introduction: from `Gamma, B(t,0) |- B(t,Sz)`.
- Progress introduction: from `Gamma, E(t,z) |- E(t,Sz)`, with `E` literally an equation.

Both conclude `Gamma |- D_(x,y) B(x,y)` with their respective matrix. In introduction, `z` is fresh for the retained context, witness, and passive parameters. In elimination, the opened witness is fresh for the old context and final conclusion. These conditions must remain explicit.

Computation may be given as theorem leaves or supplied as a temporary computation assumption and discharged after the continuation. These are equivalent by ordinary cut. The more general implementation principle supplies `H(w)` for a fresh parameter `w` when the generator guarantees a theorem `H(0)`: replace `w` by zero in the continuation and cut with `H(0)`. It does **not** assert that `H(w)` is a theorem uniformly in `w`.

## 2. Q introduction and the Q/D distinction

There is no primitive Q introduction, but its absence causes no deficiency in the full Eq/Q/D presentation because

\[
Q_y B(y)\dashv\vdash D_{u,y}B(y)
\]

for an unused witness coordinate `u`.

From Q, assume its zero instance, use Q elimination at `Sz`, and apply case D introduction with any witness. In the converse direction, eliminate D; because the witness coordinate is unused, the retained clause is exactly the required Q formula, which hypothesis use returns. This gives an explicit finite derivation in each direction.

In particular, from a fresh-parameter derivation `Gamma, B(0) |- B(Sz)` one obtains Q by case D introduction followed by D elimination and hypothesis use. For a literal equation, progress D introduction gives the corresponding progress-closure Q theorem. Combining it with a supplied zero proof yields equation induction.

Q can therefore be eliminated from *object formula syntax* if it remains an internal reusable closure resource. The existing elimination-assumptions and atomic-transport presentations already use this distinction. A failed raw edit deleting unary formula nodes in a particular checker does not establish that Q is an essential object connective. Conversely, retaining raw Q goals while removing the only way to return a retained Q clause would be an incomplete edit.

The equivalence extends through nested formulas by the corresponding binder-congruence constructions, with all local names freshened. It is not numerical equality transport that replaces a subformula by an interderivable formula.

## 3. Logical reconstruction is independent of arithmetic induction

Equation reflexivity follows from the base computation `r=I(0,t;v.0)=t`: use the same computation as both transport premises with motive `w=t`. Symmetry, transitivity, and numerical congruence then follow by explicit transport motives.

With an unused D witness coordinate, case introduction, D elimination, and Q elimination derive numerical cases for arbitrary native matrices. With progress introduction they derive induction only for literal equations. Allowing progress at a Q or D root would instead derive induction for arbitrary native formulas; because the logical interface is expressive enough for full first-order logic, this would not be an innocuous implementation change.

The scalar selector

\[
C(n,a,b)=I(n,a;v.b)
\]

has the endpoint equations `C(0,a,b)=a` and `C(Sn,a,b)=b`. Gates and the formula selector are constructed by external recursion on fixed finite formula syntax. Padding handles different binder depths. The six derived logical operations are implication, conjunction, disjunction, universal and existential quantification, and falsity designated by `0=S0`.

The important dependency check is that these logical macros use case introduction, equality transport, and fixed computations, not induction on compound formulas. Native numerical coverage is then obtained using the derived disjunction and existential rules. Explosion from `0=S0` follows first for every equation by the selector and then for every native formula by external structural induction.

The ordinary comparison theory must nevertheless include the explicit falsity bridge `(0=S0) -> bottom`. Positive arithmetic equations alone have singleton models. The native convention for absurdity is not a license to omit this ordinary-theory axiom.

## 4. Arithmetic bridge and the circularity boundary

The inherited scalar arithmetic argument has a valid dependency order:

1. Use equation induction, the selector, and numerical cases to construct scalar predecessor and prove `P(0)=0`, `P(Sn)=n` internally.
2. Construct monus and an actual-equality characteristic, proving its reflection on the entire numerical domain.
3. Translate each fixed quantifier-free formula to a Boolean-valued characteristic equation and recover contextual quantifier-free induction.
4. Use that induction for bounded square-root search, a pairing injection with projections, and a compiler for general primitive recursion.

I inspected the predecessor construction through its finite cycles, ramp, factor map, comparator, and saturated iteration. The delicate parameter discipline is respected: the shift identity for the saturated iterator is proved with the saturation parameter fixed; only afterward is its diagonal specialization used. The argument does not assume that the successor is already injective, that parity exhausts numerical residues, or that arbitrary primitive recursion has already been compiled.

The equality bridge uses a single-equation residual invariant. Its consequence `d(Sa,b)=1 iff a=b` concerns actual equality, not an assumed equality-test predicate. Applying sign and the countdown test produces a Boolean characteristic of actual equality. This establishes decidable equality as a theorem. The Boolean compilation of implication uses this proved decidability only for the relevant quantifier-free antecedent, so it does not introduce excluded middle for quantified formulas.

The arithmetic-reflection appendix contains a general statement in the full PR language, but its scalar application must be read using its opening specialization: all operations actually used before the compiler are already scalar terms. It would be circular to assume the whole PR signature in order to prove that scalar iteration can represent that signature.

Pairing is a state-coding device; its range need not be the whole original domain. The compiler carries a counter and the current recursive value in a paired state. Equation induction on the first projection gives the current counter; the projection equations then establish the general recursion equations. The original numerical domain is not replaced by the pairing range.

## 5. What makes the bi-interpretability claim substantive

The ordinary scalar theory `T_I` has full intuitionistic first-order equality logic, the staged scalar equations, literal-equation induction, numerical coverage, and the falsity bridge. It is the precise ordinary theory to which the native calculus is a faithful proof presentation.

The interpretation in iPRA replaces every fixed scalar iterator by primitive recursion with a step ignoring the old counter. The interpretation back compiles every fixed PR description into scalar terms. Both domain formulas are `x=x`, and numerical equality is actual equality.

Agreement on standard natural-number computations is insufficient. For each fixed finite description, its two translations must be identified internally at every counter. The required argument is available: after earlier subdescriptions agree, equation induction compares two functions having the same initial value and update. This also supplies coherence when substitution changes the staged description of an update.

The formula composites require separate proofs. The native returns are

\[
Q_yB\dashv\vdash B(0)\Rightarrow_*\forall_*yB(y),
\]

\[
D_{x,y}B\dashv\vdash
\exists_*x\bigl(B(x,0)\Rightarrow_*\forall_*yB(x,y)\bigr).
\]

The forward D direction opens its witness, temporarily assumes the base, specializes the closure at a fresh parameter, and introduces the universal, implication, and existential macros. The converse opens the existential and supplies case D introduction from its implication and universal. Q follows directly or through the unused-witness representation. External induction on each finite formula supplies both full formula round trips.

Thus the identity relation is an internal isomorphism for the numerical composites, and the formula translations are mutually inverse up to provable equivalence. Effective proof translations preserve contradiction in both directions and establish equiconsistency. No assertion that either theory proves its own consistency is involved.

These are written mathematical proofs with inherited substantial subproofs. They are not established merely by finite tests of the checker or of numerical functions. The separate code claim still needs its sorted raw syntax, opening, freshness, error handling, soundness, and canonical-completeness arguments.

## 6. Independent audit of the generalized tied-initializer obstruction

The proposed extension of the existing one-coordinate bound is valid with an exact oracle restriction. Let the only external numerical primitives be fixed unary PR functions and constants. A new recursor has update `h(u,v,p)` and base determined by at most a fixed finite number `q` of adaptive oracle queries to `h`. Each query argument is a fixed PR function of previous replies and constants. The final seed is another fixed PR function of those replies. The initializer has no direct access to passive parameters, their codes, a caller's counter, or oracle evaluation time.

By structural induction, each update term is bounded by a unary PR function of one selected free coordinate, or by a constant. There are three cases.

- If the selected coordinate is a passive parameter `p_j`, every oracle reply is bounded by `F(p_j)`, irrespective of its query arguments. A bounded maximum of the fixed final PR combiner over the reply box gives a unary PR bound for the seed. All later update values are again bounded by `F(p_j)`.
- If it is the update counter, the finite query circuit has a numerical constant bound independent of all passive parameters. Bound each next query and reply from the finite bounds on preceding replies. Subsequent recursive outputs are bounded by a nondecreasing unary PR function of the recursion counter.
- If it is the previous state, the same finite-circuit argument bounds the seed by a constant. Iterating a nondecreasing unary PR envelope for the state update gives a unary PR bound in the recursion counter.

Composing with the counter term's own one-coordinate majorant finishes the structural induction. Arbitrary fixed PR combiners may occur *inside the initializer circuit*; allowing them as unrestricted outer term primitives would of course admit addition immediately and invalidate the conclusion.

The finite-query condition belongs in the theorem statement, not only in its proof. For unrestricted black-box oracles, bounded replies can encode unbounded information through the first query index at which the reply is one. The oracle `h(u,v,p)=1_[u=p]` illustrates that failure of the unrestricted oracle lemma; this example does not assert that such an oracle is term-definable in the restricted language.

The resulting term obstruction rules out ordinary addition, a total selector with two arbitrary payloads, and a binary pairing injection. It also rules out a term compiler for initialized iteration, because iterating successor from an arbitrary seed gives addition. It does not rule out a relational interpretation or an interpretation with nontrivial quotient equality.

## 7. Stronger consequence: finite tuple domains do not suffice

The majorant property has a useful consequence beyond the currently inspected scalar term obstructions.

**Proposition.** Suppose every numerical term in a language has a unary majorant in one input coordinate, or a constant majorant. Let `D` be any subset of `N^d`, for fixed finite `d`, and let `e` belong to `D`. Suppose a binary operation on `D` is given by a tuple of terms

\[
\mu_i(\vec x,\vec y),\qquad 1\leq i\leq d,
\]

and has `e` as a two-sided identity with respect to actual coordinatewise equality. Then `D` is finite.

**Proof.** Fix an output coordinate `i`. If its majorant depends on a coordinate `x_j` of the first input, substitute `x=e`. The identity law `mu(e,y)=y` gives `y_i <= F_i(e_j)` for every `y` in `D`. If its majorant depends on a coordinate `y_j` of the second input, substitute `y=e` and use `mu(x,e)=x` to obtain `x_i <= F_i(e_j)` for every `x` in `D`. A constant majorant already has the required form. Thus every coordinate of every element of `D` has a fixed finite bound. The product of those finite intervals is finite. No associativity, commutativity, cancellation, or definability of `D` was used.

Consequently such a language cannot term-interpret an infinite unital magma on any finite tuple domain with actual equality. In particular, changing the numerical domain to a definable subset of a fixed finite product does not rescue a term interpretation of iPRA addition. An iPRA interpretation has infinitely many distinct numerals, whereas its addition supplies exactly the forbidden two-sided identity operation.

The direct proof just given uses actual equality. Root subsequently strengthened it to arbitrary quotient equality; the independent formal proof is in `finite_quotient_theorem.tex`. The key construction composes the two unit maps `L(z)=f(e,z)` and `R(z)=f(z,e)`. For each output coordinate, at least one map gives a uniform constant bound and the other follows only one dependency coordinate. A greedy choice of the letter removing the greater number of current dependencies halves their number, so at most `ceil(log2(d+1))` letters yield a uniformly bounded representative of every equivalence class. Unit laws and transitivity preserve the class throughout. Every class therefore meets one fixed finite box, so the quotient is finite. No congruence, associativity, commutativity, cancellation, or definability assumption is needed beyond those explicitly used.

The logarithmic composition bound is sharp at dimensions `d=2^k-1`, using projection functions organized as the complete binary tree, a zero root, and universal quotient equality. The detailed fragment makes clear that this is sharpness of the number of unit-map compositions, not of checker size or arbitrary representative definitions.

The quotient extension removes the earlier equality qualification. The restriction to term-defined operation tuples remains essential to the argument. If arithmetic function graphs are defined by quantified relations, the proof does not apply. Thus this is a stronger obstruction to a family of simplifications, not an impossibility theorem for the user's full allowed class of bi-interpretations.

The underlying one-coordinate domination property is already known as the almost-unary property on a countable set; composition closure is established in Michael Pinsker's *Clones containing all almost unary functions*, arXiv:math/0401102. The report should attribute this concept, keep the primitive-recursive-majorant strengthening explicit, and avoid a global priority claim for the finite quotient theorem.

## 8. Final assessment

The inherited complete native theory can safely be presented with full-domain bi-interpretability and equiconsistency, accompanied by its explicit hypotheses and written proofs. It is not a new theory. No new verified axiomatization below the current whole-program frontier was obtained in this independent search.

The generalized finite-oracle initializer theorem and its finite-quotient unital-magma corollary are useful mathematical results beyond the specific term obstructions inspected in the drafts. They narrow a concrete family of attempted reductions, including finite-dimensional domains with quotient equality. They neither supply a smaller complete checker nor settle absolute minimality or the remaining relational constructions.
