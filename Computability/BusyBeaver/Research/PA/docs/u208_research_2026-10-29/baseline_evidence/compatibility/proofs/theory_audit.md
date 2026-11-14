# Independent audit of Theory U and its machine-facing calibration

Audit date: 2026-10-29. Inputs are the four archives downloaded at ProveIt commit
`da4ab9dd68ccfc47ac852118601eaf1fdae53795`. This is an ordinary mathematical review,
not a proof-assistant verification.

## Executive result

I found no concrete mathematical defect in the unary theory's interpretation of
PA, its reverse interpretation in PA, or the principal dependency chain that
avoids a circular use of successor existence. The manuscript supplies a substantial
ordinary proof, including uniform proof-translation templates. Accordingly the
appropriate inherited conclusion is the mathematical claim

    PA proves Con(U) iff Con(PA).

It is not appropriate to describe the manuscript as only proposing an unsupported
least-failure hypothesis. It is equally inappropriate to describe the supplied U
machines as already having a checked PA/Lean/Rocq/MM0 endpoint: no such endpoint is
provided. A new literal-table reduction should first state precisely its own
halting-preservation theorem, then compose it with the retained numerical/source
and theory calibration.

There is an essential distinction between the two interfaces in the theory ZIP.
The U211 source uses the older native numerical calculus calibrated to unrestricted
weak cover plus irreflexivity. It does **not** run the positive dyadic emitter
described separately in `sections/emitter.tex`. Code-count or arithmetic-complexity
claims about that positive emitter cannot be used to certify the U211 tables.

## Exact theory

The language is classical first-order logic on nonempty domains, with one binary
relation E and no primitive equality, functions, or constants. Define

    Sub(x,a) := forall z (E(z,x) -> E(z,a)).

For every formula phi with FV(phi) contained in {x}, U has

    forall a exists b [forall x (E(x,b) -> phi(x)) and
                        forall x (Sub(x,a) -> (phi(x) -> E(x,b)))].

The source a may not occur freely in phi. This is a one-free-role restriction,
not one-variable logic. The output may include extra objects satisfying phi.
Consequently exactifying the matrix with `Sub(x,a) and phi(x)` is illegal for U.
The distinction matters in the lower interpretation, and the supplied proof
respects it.

## Checked lower interpretation

The main files are `sections/unary_core.tex` and
`sections/unary_arithmetic.tex` in `pa_unary_power_cover/pa_unary_power_cover`.

### 1. Equality and numerical representatives

Coextensionality x ~ y means equality of their E-member profiles. It is an
equivalence relation by logic and a congruence in membership's second coordinate.
Saturation of a containing object is needed whenever it is used in the first
coordinate. The numerical predicate N explicitly includes saturation,
transitivity, a strict linear order of its member classes, saturation of its
members, and endpoints for every nonempty represented intersection at every
initial cutoff. These are first-order clauses about existing objects, not an
assumption of external finiteness or well-foundedness.

The local lemma is sound on inspection: false filtering gives empty objects;
members of a number are numbers; existing successors preserve numericality;
every nonempty number has a greatest member d, with Succ(d,a); and least members
of a number are empty. In the hereditary step, saturation is explicitly needed
to pass a cutoff t ~ i from i in a to t in a. In the successor step, profile
equalities and saturation exclude edges from or within the new greatest class.

### 2. Induction before total successors

For a unary counterexample predicate not Q, filter at a numerical source n.
Each x in n is a subset of n, so within n the weak cover selects exactly the
failures. If there is a selected member, its least class i has a predecessor d;
failure at d contradicts minimality, and success at d contradicts failure at i.
If there are no selected members, n itself is the first failure, and its existing
predecessor gives the contradiction. This second case is essential: no successor
of n is needed.

Parameter internalization is legal. With A_theta(p) the base-and-step premise,

    Q(v) := forall p (A_theta(p) -> theta(v,p))

is unary. Its base and step follow directly from the corresponding components of
A_theta. This yields representative induction with arbitrary ambient parameters,
even for predicates not invariant under coextensionality. Endpoint selection in
the proof is still sufficient for such predicates, because a predecessor is
strictly smaller in the class order; saturation of the failure cover is not
silently assumed.

### 3. Global comparison and least failures

The no-gap property is proved by induction using only already-existing
successors. A second induction establishes trichotomy of numerical classes.
Induction on initial numerical segments then gives least classes for invariant
predicates. Fixed-length lexicographic tuples are minimized one coordinate at a
time. The defining formula contains a fixed finite tuple of variables, not an
assumed tuple-coding object.

### 4. Bounded numerical comprehension

For a target chi(z,n_1,...,n_k), the derived theorem has two genuine hypotheses:
invariance in the numerical parameter positions, and the existence of a support
source a containing every selected z as a subset. If exact comprehension fails,
choose its least failing tuple r. The unary matrix

    exists n_1 ... n_k (LeastFail(n_1,...,n_k) and chi(z,n_1,...,n_k))

is extensionally the target at r. All numerical parameters have been bound, so
there is no forbidden free source or ambient graph parameter. Filtering at the
separately obtained support gives an exact output, a contradiction. The proof is
classical syntax, not an algorithm evaluating LeastFail, and contains no truth
predicate or syntactic self-reference.

Applications establish total successors and exact powers of numerical sources.
The successor target is supported by its predecessor number itself; selected
objects are subsets of that predecessor. The power target is directly supported
by its numerical source. No powers of arbitrary ambient objects are inferred.

### 5. Arithmetic graphs and histories

Singleton, unordered-pair, and Kuratowski-style ordered-pair profiles collect all
coextensional representatives of the desired components. Numerical parameter
invariance and the required support sources are proved. Both coordinate decoding
and saturation are valid on inspection, including equal-coordinate pairs.

For graph comprehension, pair codes with coordinates in n are subsets of an
exact power W of n. W need not be numerical: the bounded-comprehension theorem
allows any supporting source. Its matrix still has only numerical free
parameters.

History uniqueness precedes extension. The old graph is bound inside the canonical
extension or restriction formula; every free parameter is numerical. This prevents
the invalid shortcut of filtering a graph while leaving that graph free in a unary
matrix. A separate numerical bound d handles nonmonotone transition functions.
Induction constructs finite histories, proves their functional recursion equations,
and then supplies addition and multiplication. Representative induction supplies
all translated PA induction instances.

## Reverse interpretation and PA internality

In any PA model, interpret E(x,a) as `Bit(a,x)`. PA proves that Sub(x,a) implies
x <= a. For each fixed arithmetic predicate, induction constructs its finite
binary characteristic code on the interval through a. The resulting object
satisfies an exact filter, hence the weaker U clauses. The same argument even
allows arbitrary additional matrix parameters, and PA proves irreflexivity of
this membership interpretation.

This is a formula-by-formula proof, not a uniform satisfaction predicate.
Nonstandard PA models are included because finite comprehension is obtained by
PA's own induction scheme.

The report describes primitive recursive syntax operations for translating finite
proofs: freshening variables, substituting a formula into fixed derivation
templates, relativizing quantifiers, replacing terms by total functional graphs,
and concatenating proof fragments. The fixed arithmetic axioms have fixed lower
derivations; variable induction instances use the unary parameter-internalization
template. Structural induction and induction on coded proofs are the advertised
PA correctness proofs. This is the conventional route to an internal consistency
biconditional. Neither a complete implementation of these arbitrary-proof
translators nor a proof-assistant certificate is delivered in the theory archive.

## Positive-interface cross-check

The positive theory uses D := forall v E(v,v), a local target q(a)=E(a,a), and
an additional seed not D. To translate an arbitrary unary matrix into positive
syntax, replace falsity by **closed D**, not by q(a): the latter would introduce
a forbidden free source. This point is handled correctly.

Under the seed, weak filtering is initially available only at irreflexive
sources. Every source actually used in the arithmetic construction is numerical
or an exact power W of a number n. Such W is irreflexive: n belongs to W; if W
belonged to W then W would be a subset of n, yielding n in n. Thus the localized
lower proof remains legal.

The positive theory alone has a one-element total-relation model. Its ordinary
consistency is therefore not the calibrated assertion. The target is
nonderivability of E(v_0,v_0), equivalently consistency after adding not D.
The raw positive emitter's two low-code collisions, padding, and naming
normalization are additional proof obligations, supplied in its separate section.
They do not certify the older native calculus used by U211.

## Actual numerical/source bridge retained by U211

For additional inspection I extracted the relevant text from the retained
`u212_combined_2026-10-29.zip` into `work/theory_lineage`.

The native calculus has truth alias 0, falsity target 1, native Cantor-coded
constructors, seven logical rows, a dominated propositional row, modus ponens,
theorem generalization, and a gated cover/vacuity bundle. Its calibrated ordinary
theory is W + IR, where W allows arbitrary matrix parameters and IR is global
irreflexivity. The calibration is

    Con(PA) -> Con(W+IR) -> Con(U) -> Con(PA),

with PA-verifiable finite-refutation conversions claimed for each arrow.

`baseline/u214/proofs/role_emitter.tex` handles the nontrivial role collision:
the output label equals the matrix code a, the source label is b, and the tested
label is c, with gate c != a,b. When a != b, the generated guard is subset. When
a=b, the local binder captures the source and the guard becomes emptiness under
IR; an empty source gives the needed weak-cover instance. The truth 0 and falsity
1 aliases are accounted for. Completeness pads an arbitrary desired matrix to a
code n>1 and selects (a,b,c)=(n,0,1), so the gate is satisfied and output freshness
follows from the variable-label bound. The bundled atomic vacuity is preserved.

`baseline/primary_u213/proofs/source_transport.tex` explicitly compares the copied
774-primitive emitter and every retained control successor. It does not pretend
that K215's fixed ZFC theorem changes its conclusion merely by replacement of an
emitter.

`baseline/primary_u213/proofs/startup_suffix.tex` addresses the dangerous interior
startup. At the inherited physical entry, the incoming cache 1 is an arithmetic
parameter, not a theorem. The interior suffix constructs nine theorem-valued
heads above opaque tail 4. A scheduler-credit proof shows debt at most 2 from
candidate 1, preserving margin 7. Ghost explicit stack length is needed because
P(0,0)=0; this issue is handled. Thus the opaque tail is never exposed in the
soundness proof.

`baseline/primary_u213/proofs/compiler.tex` gives a strong proof compiler above
arbitrary underlying stacks after an AX reset, and cofinal successful candidate
codes. This is the completeness argument that allows the finite startup and
candidate cutoff to be retained. These source/compiler obligations are genuine
mathematical dependencies, not replaced by a finite blank-tape trace.

## Suggested endpoint language for the new result

State the locally established result first, for example:

    PA proves Halt(M_new, blank) iff Halt(M_selected_parent, blank).

Describe whether this is supported by arbitrary-exterior local tape identities,
universal symbolic primitive contracts, a source-control-flow equivalence, or
their combination. Then state the inherited composition:

    PA proves not Halt(M_new, blank) iff Con(U) iff Con(PA).

Label the second as an ordinary mathematical result using the exact retained
calibration lineage. Describe executable symbolic certificates as such; they are
stronger than bounded numerical tests but are not automatically small-kernel
proof-assistant theorems. No consistency assumption is needed for the
biconditional, while asserting actual nonhalting uses Con(PA).

## Theory-level research attempted

No immediate theory modification reviewed here yields a proved literal state
saving. Pulling the two test quantifiers together looks superficially shorter at
a high-level connective basis but blocks the cancellation used in the current
{E,forall,implication,false} encoding. Its straightforward primitive translation
adds two implications and two falsities while saving one quantifier, so it is a
net loss of three constructor nodes. The positive dyadic emitter may be a useful
future compiler target, but its nine nonlinear multiplications do not imply any
binary single-tape state bound.

Dropping the gate or bundled atomic vacuity would require new soundness or
completeness proofs, respectively; unary U's single-schema description does not
by itself license either deletion. The literal-table and source-association
reductions pursued by the main investigation preserve more of the established
calibration and therefore offer a cleaner path to a sub-211 candidate.
