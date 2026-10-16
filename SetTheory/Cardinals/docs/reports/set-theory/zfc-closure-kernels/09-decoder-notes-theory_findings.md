# Logical and foundational audit for a smaller ZFC machine

These are intermediate research notes prepared for the parent report. No
new transition table is claimed here. The work includes tail universality
for the existing enumerator, two rigorous rejection tests, and a positive
solution of the retained article's subset-only point-BIC question. The
latter is developed fully in `point_subset_bic_proof.md`; its key idea is
a gated subset-generation/singleton-decoding relation that supplies
transitive containers before Union or Separation is available.

## 1. A countermodel to deleting equality vacuity

The current eight logical rows use a primitive equality atom, membership,
implication, and universal quantification. Let the space of valuations be
all functions s:N -> {0,1}. Give implication its ordinary Boolean meaning
and interpret All_i as quantification over changes to the i-th coordinate.
Interpret every membership atom as false, and interpret equality by

    Eq(i,j)[s]  iff  s(0)=0 or s(i)=s(j).

This is a deliberately nonstandard interpretation of the equality atoms.
It is an algebraic model of the proposed remaining axiom system, not a
first-order structure with genuine equality. That is the correct kind of
model for proving that the omitted axiom is not derivable.

At each valuation, Eq is either universal equality (when s(0)=0) or the
equivalence relation determined by the coordinate values. Therefore the
Euclidean equality row

    Eq(c,a) -> (Eq(c,b) -> Eq(a,b))

is true. The equality existence row Exists_i Eq(i,j) is also true. For
i != 0, change coordinate i to s(j); for i=0, change coordinate 0 to 0.
Left and right membership congruence are vacuous because membership is
always false. Every membership-vacuity row holds for the same reason.

The Lukasiewicz row holds pointwise by propositional logic. Quantifier
distribution, quantifier commutation, and Exists_i All_i A -> A hold for
ordinary coordinate quantifiers and arbitrary truth sets A. Modus ponens
and generalization preserve formulas true at every valuation.

Nevertheless, the equality-vacuity instance

    Eq(1,2) -> All_0 Eq(1,2)

fails when s(0)=0, s(1)=0, and s(2)=1: its antecedent is true but changing
s(0) to 1 makes its consequent false.

Consequently no derivation of all equality-vacuity instances from the
eight logical rows plus membership vacuity exists. Adding the nonlogical
CP/GIC bundle might alter this conclusion, but using that possibility
would require an additional nonlogical proof. The countermodel does not
assert that CP or GIC is valid, and does not claim independence over the
whole set theory.

### A second consequence: merely choosing larger binder labels is unsafe

The same infinite-coordinate model validates every restricted
equality-vacuity instance with c > max(a,b). Such a c is neither 0 nor a
nor b, so changing coordinate c cannot change Eq(a,b). Yet the omitted
instance displayed above still fails. Thus replacing the freshness
condition c != a,b by numerical ordering c > max(a,b) is insufficient to
recover full pure logic. One cannot appeal to an unproved admissibility
of arbitrary renaming: the numerically restricted axiom set itself is
not closed under arbitrary renaming.

### Finite regression

`check_vacuity_countermodel.py` checks the four-coordinate restriction.
It exhausts all 65,536 predicate truth tables, checking 1,048,576
commutation instances and 262,144 Exists-All instances. Distribution K
is checked by exhausting its 16 possible pairs of truth tables on a
two-point coordinate fiber; validity on each fiber establishes its
arbitrary-global-table case. The analytic infinite-coordinate argument
above, rather than the finite regression, proves non-derivability for a
language with arbitrarily many variables.

The relevant literature distinguishes object-level completeness from
scheme completeness. See Benoit Jubin, *Independence questions in a
finite axiom-schematization of first-order logic*, arXiv:2202.10383,
https://arxiv.org/abs/2202.10383 (version 3, 2026-03-06); and the exact
Metamath S2 table at https://us.metamath.org/mpeuni/mmset.html. The
particular countermodel above is proved directly here; no attribution of
its historical novelty is made.

## 2. Dropping the CP transitivity arm gives a theory whose consistency
##    is provable in ZFC

Write CP' for

    Forall p Exists V [ p in V and
        Forall x in V Exists W in V Forall z (z subset x -> z in W) ].

It omits the conjunct x subset V from the current CP axiom. Let GIC be
the full global-image collection schema, with genuine equality allowed
in its matrices, and let IR be Forall x not(x in x).

**Theorem.** ZFC constructs a set model of CP' + GIC + IR. In particular,
ZFC proves Con(CP' + GIC + IR). Assuming ZFC is consistent, this theory
cannot have a ZFC-provable consistency equivalence with ZFC.

**Proof.** Work in ZFC. Put kappa = beth_omega and define P_kappa to be
the pseudo-hereditary universe

    { x : |x| < kappa and every y in TC(x) has |y| < kappa }.

This is a transitive set. For completeness, each finite membership level
of x has cardinal at most kappa, so TC(x) has cardinal at most kappa.
The objects therefore belong to H_(kappa^+), a set, and separation
defines P_kappa inside it. Transitivity is immediate from the definition.
This is the universe denoted H_kappa by Greg Oman, *On the axiom of
union*, Archive for Mathematical Logic 49 (2010), 283-289, Theorem 1:
https://faculty.uccs.edu/goman/wp-content/uploads/sites/15/2021/02/On_the_axiom_of_union.pdf.

Two closure facts are enough here. (1) If x is in P_kappa then its full
ambient powerset P(x) is in P_kappa. Its cardinality is 2^|x| < kappa
because kappa is a strong limit; subsets of x and their descendants
satisfy the same cardinality restriction. (2) If C is an ambient set of
fewer than kappa elements of P_kappa, then C is in P_kappa. Its immediate
cardinality is small and every descendant belongs below one of its
members, where the defining restriction is already known. This second
fact does not require regularity of kappa.

Given p in P_kappa, let V={P^n(p):n<omega}, where P^0(p)=p. Every element
of V lies in P_kappa, and |V| <= aleph_0 < kappa, so V lies in P_kappa.
It contains p. If x=P^n(p) is a member of V, choose W=P^(n+1)(p), also a
member of V. Every z subset x in the transitive structure P_kappa is an
actual subset, and hence belongs to W. This proves CP'.

For an arbitrary formula phi and parameters in P_kappa, fix B in
P_kappa. Let A={x in B : some y in P_kappa satisfies phi(x,y)}. Ambient
ZFC Choice selects one such witness f(x) for each x in A. Its image C
has cardinal at most |B| < kappa and consists of elements of P_kappa.
Closure fact (2) puts C in P_kappa. Every nonempty fiber over B has a
witness in C, and every member of C comes from a phi-fiber over B.
This proves GIC, including its no-junk clause (indeed with the stronger
condition that the source x is in B). A single satisfaction predicate
for the set structure proves this uniformly for all formula codes.
Finally IR follows from ambient Foundation. This proves the theorem.

**Why the missing arm matters.** The model contains the countable set of
stages {P^n(omega):n<omega}, although the union of those stages has
cardinality at least beth_omega and is excluded. A transitive CP
container V for omega would force, by finite induction, members with
cardinalities at least beth_n for every n; transitivity would make all
their elements members of V. Thus |V| >= beth_omega, contradicting
membership in P_kappa. CP' supplies a set of stages; CP supplies the
substantially stronger bound containing their elements.

This is a direct obstruction to the specific proposed optimization. It
does not merely point out that an existing proof happened to use
transitivity.

## 3. Equality elimination is rigorous but does not establish a machine
##    saving

Let S0 be CP + GIC in membership logic with equality. Define a theory
E0 in equality-free membership logic by the same CP and all equality-free
GIC instances. No member-profile congruence sentence is needed to
calibrate E0 with the already nonextensional S0.

Define two-sided observational equality by

    D(x,y) := Forall z [ (z in x <-> z in y) and
                         (x in z <-> y in z) ].

Pure equality-free first-order logic proves that D is reflexive,
symmetric, and transitive. It also proves

    D(x,x') and D(y,y') -> (x in y <-> x' in y').

Translate an equality-bearing formula by replacing each equality atom
with a fresh-variable copy of D. The translation commutes with the
logical operations and capture-avoiding variable substitution. By
structural induction all equality axioms translate to pure logical
theorems. CP is unchanged. Every translated GIC instance is an E0
instance because its translated matrix is equality-free. Thus every S0
refutation translates effectively to an E0 refutation. Conversely the
E0 axioms and equality-free logical calculus embed directly into S0.
These finite proof translations can be formalized in elementary
arithmetical metatheories, in particular in PA and ZFC. Adding IR on
both sides does not affect the argument.

This observation does **not** remove the member-profile congruence axiom
from an extensional closure theory. D uses both incoming and outgoing
profiles, so equality of incoming profiles alone need not imply D. It
therefore does not prove the translated Extensionality axiom. The
nonextensional S0 interpretation still uses its set-coded bisimulation
construction to obtain an extensional completion.

It also does **not** justify deleting equality rows from the current
Tarski compiler. Those rows are the efficient substitute for recursive
variable substitution. An equality-free foundational presentation must
still be paired with an adequate equality-free proof calculus and a
measured implementation. The equality-vacuity countermodel above gives
a concrete reason not to equate semantic equality elimination with
deletion of the runtime equality constructor.

## 4. Safe specialization of the nonlogical variables

The existing `Comp_Bundle254.v` proof of every GIC instance (`TB_gic`)
already uses only input label 1 and output label 3. The translated
matrix uses parameters 5,7,..., and an extra vacuous quantifier ensures
that its code c is greater than 3 and absent from the matrix. The CP
derivation uses other fixed labels only for convenience and can be
alpha-renamed to this layout.

Thus a compiler may specialize the CP/GIC generators to two fixed
distinct labels, provided it separately retains the general gated
membership/equality vacuity rows needed for logical completeness.
Freezing the whole bundled root, including those vacuity rows, does not
inherit the old logical completeness proof. The specialization should
be measured after code generation; no state estimate follows solely
from choosing labels 0,1 or 1,3.

## 5. Positive theoremhood versus inconsistency

For an equality-free bottom-bearing theory T that proves not H, where
H=Forall x Forall y (x in y), translate falsity to the **closed** H.
Pure positive implication/universal logic proves H->A for every formula
in that positive language. Thus the translation gives

    T^+ proves H  iff  T is inconsistent.

With sentence axioms, an open atom x0 in x1 with distinct variables is
an equivalent theoremhood target by generalization and instantiation.
It is not a valid open replacement for bottom inside arbitrary formulas.
If equality is retained, H no longer implies all atomic formulas; the
target or proof calculus must additionally handle equality.

The positive theory T^+ has a singleton full-relation model, so it is
consistent regardless of Con(T). The theoremhood equivalence is the
calibration. A consistency equivalence for T^+ would be the wrong claim.
For CP+GIC, the empty-set instance of GIC proves not H without IR.
Nevertheless, expanding a closed H throughout the existing encoded
formulas and preserving all alias/collision invariants can increase
the program. The current diagonal alias is not a separately encoded
IR axiom whose removal automatically saves states.

## 6. Tail universality of the existing enumerator

**Reviewed claim: sound.** The exact definitions and existing lemmas in
`Enum254.v`, `L1_Comp254.v`, and `L1_Sound254.v` support the following
stronger statement. Write `halts_from(s)` for eventual halting of the
abstract six-register enumerator from state

    s = (pl, np, tw, ws, d, h).

Let

    Inv(s) := thm254(tw) and thm254(h) and goodstack(ws),

where `goodstack(ws)` means that every entry of the iterated P-decoded
stack stream is a `thm254` theorem. Then

    for every s, Inv(s) implies
        (halts_from(s) iff thm254(1)).

There is no restriction on the natural numbers `pl`, `np`, or `d`.
In fact, the completeness direction does not require `Inv`:

    thm254(1) implies (for every s, halts_from(s)).

This is a theorem about the existing enumerator with its existing
command semantics, not a change to the proof system.

### 6.1 Soundness from a good retained state

The existing `Inv_step`, `Inv_run`, and `halt_step` already quantify
over an arbitrary initial state. If a run from `s` reaches `s'` and
halts on the next step, `Inv_run` gives `Inv(s')`, and `halt_step`
gives `thm254(1)`. Neither proof assumes anything about `pl`, `np`,
or `d`. Thus this half needs no new invariant argument.

### 6.2 Every sufficiently late candidate is reached

The existing `step_pl` says that a nonhalting step from positive `pl`
strictly decreases it and preserves `np`. Hence the already generic
`drain` lemma says that every state either eventually halts or reaches
a state with `pl=0` and the same `np`.

At a state with `pl=0` and `np=K`, a nonhalting step starts candidate K,
sets `np=K+1`, and leaves a finite residual `pl`. Draining that residual
either halts or reaches `pl=0,np=K+1`. By induction, from any initial
state `s` and every `N >= np(s)`, the machine either halts or reaches a
state with `pl=0,np=N`. This is the direct relative version of the
existing `reach` lemma; it uses the same `step_pl`, `drain`, and
`run_add` proof steps. No decrease of `tw`, `ws`, `d`, or `h` is needed.

### 6.3 A halting compiled program exists arbitrarily far out

Suppose `thm254(1)`. The existing `compile` lemma supplies a command
list L with the contract

    for all T,w, exec(L,(T,w,0,0)) is None
                or Some(1,w,0,0).

The quantification over *every* T,w is crucial: there are no goodness,
size, or stack-shape premises in `blk`. Define

    START_U := CAX 0 1 1 U,
    SUFFIX  := [CDROP; CNIP; CNIP],
    Q_U     := START_U :: (L ++ SUFFIX).

For every incoming tuple `(t,w,dd,hh)`, executing START_U yields

    (gate(dd+1,hh+1,0),
     ax_stack(dd+1,hh,hh+1,0,U,t,w), 0,0).

The two final coordinates are zero for every U. Apply the block
contract at precisely the displayed new T and w. If L halts, Q_U
halts. Otherwise L yields `(1,w',0,0)`; DROP gives
`(0,P(1,w'),0,0)`, the first NIP gives `(0,w',0,1)`, and the second NIP
halts. Therefore

    for every U and every q, exec(Q_U,q) = None.

This is exactly the existing `program_halts` proof with the last
parameter of START changed from 0 to U. U only changes the rho8
formula placed in the temporary axiom stack. Neither the block
contract nor the suffix proof inspects that formula. START_U also
preserves `Inv` whenever its input satisfies `Inv`, by the existing
general AX case of `Inv_step`.

The **first** command is encoded without the `+1` that is used for
commands in a residual tail. Consequently the correct candidate
number is

    N_U = enc_fields(fields(START_U), enc_tail(L ++ SUFFIX))
        = P(3, P(1, P(1, P(U, enc_tail(L ++ SUFFIX))))).

The existing `P_ge_l` and `P_ge_r` imply `N_U >= U`. For an arbitrary
starting state choose `U = np(s)+1`. Then `N_U > np(s)`, so the
relative reach lemma either already gives a halt or reaches a state
with `pl=0,np=N_U`. The existing `run_first` lemma applies there to
Q_U, and its premise `exec(Q_U,q)=None` holds for every retained q.
Composing the finite runs proves `halts_from(s)`.

### 6.4 Consequence for a shortened bootstrap

One need not reproduce the published bootstrap's particular value
`np=2`, zero `pl`, or zero `d`. It is sufficient to reach a correctly
represented enumerator boundary with `Inv`. This can enlarge the
search space for a shorter startup program without changing the
logical core.

The qualification "correctly represented enumerator boundary" is
essential. The theorem concerns the six-field abstract state. Applying
it to a Turing-machine entry point still requires the concrete tape
encoding and control-location conditions of the simulation theorem,
including any required zero temporary registers. It does not claim
that every physical tape or every interior DAG node simulates an
arbitrary Enum254 state.

**Verification status.** This section is a direct mathematical review
of the imported definitions and proved lemmas. No new proof-assistant
formalization is claimed, and the imported development is unchanged.
The argument is a small extension of the existing proofs. A future
formalization should follow the repository's stated preference for Lean.
