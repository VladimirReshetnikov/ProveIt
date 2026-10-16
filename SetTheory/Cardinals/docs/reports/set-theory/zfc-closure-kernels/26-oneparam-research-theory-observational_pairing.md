# One arbitrary parameter plus a short fixed adjunction axiom

Research contribution, 16 October 2026. The theorem below strengthens the
inspected repository's two-slot consistency result to a direct deductive
equivalence in the original equality-free language. It makes no priority
claim beyond this comparison, and it supplies no new Turing-machine state
bound. The familiar idea of packing finite tuples is standard; the additional
points requiring proof here are extracting a suitable pairing axiom from a
single EPSC instance, using full profiles rather than incoming profiles, and
recovering ordered-pair coordinates without Extensionality.

## 1. Definitions and main result

The language is classical equality-free first-order logic with genuine
falsity, a nonempty domain and one binary relation `in`. Put

    E(x)     := forall z not(z in x),
    Sub(x,b) := forall z(z in x -> z in b),
    D(x,y)   := forall z(z in x iff z in y),
    O(x,y)   := forall z((z in x iff z in y) and (x in z iff y in z)),
    U(x,y)   := forall z(x in z -> y in z).

The relation O compares both incoming and outgoing profiles. It is a fixed
first-order formula. It is not a new predicate in the object language.

For R(x,y;p), write

    SB_R := forall x exists b forall y(R(x,y;p) -> Sub(y,b)),
    Hull_R(c) :=
       [forall x forall y(((E(x) or x in c) and R(x,y;p)) -> y in c)]
       and [forall y(y in c -> exists x R(x,y;p))].

EPSC_k consists of all universal closures of

    SB_R -> exists c Hull_R(c)

for matrices whose ordinary free parameters occupy at most k slots. The
input x and output y are additional variables. EPSC_infty allows arbitrary
finite parameter tuples. All binders inserted by a template are fresh.

Define

    PairO(a,b,c) := forall y(y in c iff O(y,a) or O(y,b)),
    OPair := forall a forall b exists c PairO(a,b,c),
    Gamma := EPSC_1 + OPair,
    AU := forall a forall b exists c forall y(
              y in c iff (y in a or U(y,b))),
    Gamma_AU := EPSC_1 + AU.

**Main theorem.** In their common equality-free membership language,

    Gamma_AU, Gamma, EPSC_2 and EPSC_infty

are deductively equivalent. There are uniform syntax-directed reductions of
axiom instances and refutations in both directions. The preferred candidate
Gamma_AU is one arbitrary one-parameter schema plus one short fixed
first-order sentence. Under EPSC_1, even the one-sided outgoing implication
U(x,y) is equivalent to full observational equivalence O(x,y); Section 6.1
proves this and reduces the fixed surcharge from pairing to adjunction.

Equivalently, OPair may be replaced in Gamma by the single two-parameter
EPSC instance displayed in Section 3. No assertion here eliminates that
finite surcharge or identifies EPSC_1 alone with ZFC.

Combining the theorem with the existing ordinary ZFC calibration of EPSC_2
gives

    ZFC proves Con(Gamma_AU) iff Con(Gamma) iff Con(EPSC_2)
                   iff Con(EPSC_infty) iff Con(ZFC).

The new part of this note is the direct raw-language equivalence. It does
not require passing to the hereditarily saturated interpretation before
packing raw parameters.

## 2. Why full profile equivalence is sufficient

**Lemma 1.** Pure equality-free first-order logic proves that O is an
equivalence relation and a congruence for `in` in both coordinates. Every
equality-free formula is invariant under replacing any of its free arguments
by O-equivalent objects.

**Proof.** Reflexivity, symmetry and transitivity follow separately for the
two profile conjuncts by propositional logic. If O(a,a'), outgoing agreement
gives `a in b iff a' in b`. If O(b,b'), incoming agreement gives
`a' in b iff a' in b'`. Combining them proves invariance of the atomic
membership formula. Falsity is constant. Implication and other Boolean
connectives preserve equivalence; universal and existential quantifiers
preserve it after bound variables have been freshly renamed. Structural
induction gives the formula assertion. ∎

Incoming profile equivalence D alone would not suffice: D(a,a') does not
generally imply `a in z iff a' in z`. This is precisely why the existing
hereditary interpretation was needed for D-based packing. O carries the
missing congruence already in pure logic, so arbitrary raw formulas can
be packed once OPair is available.

## 3. A single fixed EPSC_2 instance gives OPair

Use the matrix

    B(x,y;a,b) :=
       (E(x) and O(y,a))
       or ((not E(x) or E(a)) and O(y,b)).

It has exactly the two ordinary parameters a,b and no others.

**Lemma 2.** Pure logic proves SB_B. EPSC_1 together with this one fixed
two-parameter instance proves OPair. Thus EPSC_2 proves OPair.

**Proof of boundedness.** For a fixed input x, use the following explicit
local witnesses:

| Input condition | Subset bound |
|---|---|
| not E(x) | b |
| E(x) and not E(a) | a |
| E(x) and E(a) | b |

In the first case only O(y,b) outputs occur. In the second only O(y,a)
outputs occur. In the third both kinds may occur, but O(y,a) makes y empty
because a is empty; hence these outputs are subsets of b as well. O(y,b)
also makes y a subset of b. No common bound for a and b, Pairing, Union or
Choice is presupposed.

**Proof of pairing.** The false-matrix EPSC_1 instance supplies an empty
object e. Apply the fixed B instance to obtain its supported closed hull c.
The input e emits every O-copy of a, so all such copies belong to c. If a is
nonempty, a itself is now a recurrent active input and emits every O-copy
of b. If a is empty, the initial input e already emits every O-copy of b
through the E(a) arm. Conversely, the support clause says that every member
of c is a B output, hence an O-copy of a or b. Therefore PairO(a,b,c). Since
a,b were arbitrary, OPair follows. ∎

The special empty-a arm is necessary: without it an empty first parameter
need not activate the second branch. The formula is uniformly bounded even
in that collision case.

## 4. Kuratowski coordinates without Extensionality

Put

    OP(a,b,t) := exists s exists u(
        PairO(a,a,s) and PairO(a,b,u) and PairO(s,u,t)).

OPair supplies such a code for every a,b by three applications. The inner
pair objects themselves need not be unique, even up to O.

For a code t define two formulas that use no other parameter:

    Intersection(z,t) := forall w(w in t -> z in w),
    UnionProfile(z,t) := exists w(w in t and z in w).

These are profile predicates; their names do not assert the existence of
actual intersection or union objects.

**Lemma 3 (coordinate recovery).** If OP(a,b,t), then for every z,

    Intersection(z,t) iff O(z,a),
    UnionProfile(z,t) iff O(z,a) or O(z,b).

**Proof.** Choose witnesses s,u. Reflexivity of O implies s in t and u in t.
If Intersection(z,t), then z in s and hence O(z,a), because s is an exact
O-singleton of a. Conversely, if O(z,a), then z belongs to s and u. Any
w in t is O-equivalent to s or u, so incoming O-congruence gives z in w.

For the union profile, if w in t and z in w, then O(w,s) or O(w,u). Incoming
congruence reduces membership in w to membership in s or u, which gives
O(z,a) or O(z,b). Conversely, either disjunct gives z in u, and u in t. ∎

**Lemma 4 (endpoint injectivity).** If D(t,t'), OP(a,b,t), and OP(a',b',t'),
then O(a,a') and O(b,b'). In particular the conclusion holds for O-equivalent
codes or for two decompositions of the very same code.

**Proof.** Incoming equality D(t,t') makes the two displayed profile
predicates identical. Lemma 3 therefore yields

    forall z(O(z,a) iff O(z,a')),
    forall z((O(z,a) or O(z,b)) iff (O(z,a') or O(z,b'))).

Set z=a in the first line; O(a,a) gives O(a,a'). If not O(b,a), take z=b
in the second line. The first alternative O(b,a') would contradict
O(a,a'), so O(b,b'). If O(b,a), take z=b' in the second line and use
symmetry and transitivity to conclude O(b',a), hence O(b,b'). Classical
case distinction completes the proof. ∎

The proof uses only exact local pairing witnesses and full-profile
congruence. It never invokes Extensionality, Foundation, uniqueness of the
inner pair objects, or an already existing union/intersection operation.

## 5. Uniform finite tuples and matrix packing

For k >= 1 define a finite formula Tuple_k(t,z1,...,zk) recursively:

    Tuple_1(t,z1) := O(t,z1),
    Tuple_(k+1)(t,z1,...,z_(k+1)) := exists s(
        OP(z1,s,t) and Tuple_k(s,z2,...,z_(k+1))).

This recursion is in the metatheory. For each fixed k it produces an
ordinary finite formula, not an internal infinite list object.

**Lemma 5.** Under OPair, every finite tuple has a code, and O-equivalent
codes determine componentwise O-equivalent tuples.

**Proof.** For k=1 choose t=z1; Lemma 1 gives existence and uniqueness up to
O. For the next stage, code the tail by induction and apply OP existence
to the head and tail. If two outer codes are O-equivalent, Lemma 4 identifies
their heads and makes their tail codes O-equivalent, so induction applies.
Only finitely many OPair uses are needed for each fixed tuple length. ∎

Fix an arbitrary raw equality-free matrix R(x,y;p1,...,pk). Replace its
parameter tuple by the one-parameter matrix

    Rhat(x,y;t) := exists z1 ... exists zk(
        Tuple_k(t,z1,...,zk) and R(x,y;z1,...,zk)).

The formula has no free variables except x,y,t. Fresh renaming avoids any
collision with the bound variables of R. If k=0 no packing is necessary.

**Lemma 6.** Under OPair and Tuple_k(t,p1,...,pk),

    forall x forall y(Rhat(x,y;t) iff R(x,y;p1,...,pk)).

**Proof.** The reverse implication uses the original parameter tuple as
the witnesses. In the forward direction, the witnessed tuple has the same
code t; Lemma 5 identifies corresponding entries up to O, and the raw
formula invariance of Lemma 1 transfers R to the original parameters. ∎

No hereditary restriction or incoming-profile saturation is needed. The
reason is exactly the stronger observational congruence O.

## 6. Proof of the main theorem

Work in Gamma. For any target EPSC_infty instance R(x,y;p1,...,pk), fix
its parameters and suppose SB_R. OPair supplies a tuple code t. Lemma 6
shows that SB_Rhat and SB_R are equivalent at that code, and that their
hull formulas are equivalent for every prospective c. Apply the permitted
EPSC_1 instance for Rhat and obtain an Rhat hull, hence an R hull. The
conclusion does not mention t, so existential elimination discharges the
chosen tuple witness. Universal closure of the original parameters gives
the required target axiom.

Thus Gamma proves EPSC_infty. Conversely EPSC_infty contains EPSC_1 and
proves OPair by Lemma 2, so it proves Gamma. EPSC_2 contains EPSC_1 and the
fixed B instance, hence proves Gamma; EPSC_infty trivially contains every
EPSC_2 instance. These three theories therefore have the same consequences.

The equivalence also proves that Gamma can replace OPair by just the fixed
B instance: that instance derives OPair using EPSC_1; OPair, together with
EPSC_1, derives every EPSC instance including B.

### 6.1 Collapsing a one-sided outgoing implication to full equivalence

**Lemma 7.** EPSC_1 proves

    forall x forall y(U(x,y) iff O(x,y)).

**Proof.** The implication O(x,y) -> U(x,y) is pure logic. Conversely,
fix x and form its exact O-singleton s by the one-parameter constant matrix
O(z,x), whose outputs are subsets of x. The exact-class construction uses
an empty input supplied by the false-matrix instance. Since O(x,x), we
have x in s. If U(x,y), then y in s, hence O(y,x), and symmetry gives
O(x,y). No Extensionality or purity assumption is involved. ∎

This lemma is stronger than observing that U defines equality in extensional
set-theoretic models. It holds in every raw EPSC_1 model, where different
objects may still have the same incoming profile without being O-equivalent.

Define the intermediate fixed observational adjunction axiom

    OAdj := forall a forall b exists c forall y(
                 y in c iff (y in a or O(y,b))).

**Corollary 8 (short surcharge).** EPSC_1 + OAdj and EPSC_1 + AU are
deductively equivalent to EPSC_infty.

To derive OPair from OAdj, first use the exact-class lemma on O(y,a),
bounded by a, to form an exact O-singleton s of a. OAdj applied to s,b
forms their exact O-pair. The main theorem for Gamma gives unrestricted
EPSC. Lemma 7 makes OAdj and AU equivalent over EPSC_1.

Conversely unrestricted EPSC gives OAdj by exact-class formation. For a
given a use a one-parameter transitive container v, so every member of a
is a subset of v. Obtain an exact O-pair P of v,b by Lemma 2. Raw Union of
P, which the one-parameter bootstrap supplies, gives a common subset bound
u for v and b: both v and b belong to P. Thus every y satisfying
`y in a or O(y,b)` is a subset of u. The exact-class lemma for that
two-parameter predicate produces the OAdj witness. The bound u is used
only in the premise and does not enter its matrix. Lemma 7 then gives AU.

For completeness, the needed raw Union of P has a direct one-parameter
proof: obtain a transitive container V of P. If y in z in P, then y in V
and hence y is a subset of V. Exact formation of
`exists z(z in P and y in z)` therefore produces Union(P) using P alone.

This proves the full four-theory equivalence asserted at the start.

## 7. Effectiveness and formalization scope

This argument gives direct axiom-instance derivations, rather than relying
only on the existence of a quotient model or a semantic completeness theorem.
Its transformations are:

1. list a matrix's free parameter variables and rename its binders;
2. construct the corresponding finite Tuple_k formula;
3. build the raw-formula O-invariance derivation by structural recursion;
4. insert the fixed local pairing and coordinate-recovery derivations;
5. replace the arbitrary EPSC axiom by its one-parameter packed derivation.

Under standard Gödel codings these are primitive-recursive constructions on
finite syntax. Replacing axiom leaves in a finite proof supplies uniform
refutation transformers. This is an ordinary metamathematical proof; no
serialized proof-code file or proof-assistant theorem for this transformer
is included in this note. The pre-existing EPSC_2-to-ZFC calibration remains
an ordinary ZFC-level result at the inspected pin, not an automatically
obtained checked PA endpoint.

## 8. Consequences for a small-machine program

The result separates arbitrary-parameter machinery from a single fixed
logical sentence. A complete equality-free search engine for Gamma_AU needs an
arbitrary matrix environment with slots x,y,t rather than x,y,p,q, together
with a fixed closed AU row. OPair, OAdj and the fixed B-instance version are
controls to compare under the same backend. The calibration proof does not
put tuple construction or decoding on the Turing-machine tape.

Whether this saves states is unresolved. The AU row is much shorter than the
O-expanded controls, but a generic dynamic environment may already handle a
fourth slot at negligible additional state cost. All logical inference,
binding, enumeration and initialization costs must be charged. Removing the
finite surcharge would require an additional proof; EPSC_1 alone remains
open in the inspected research.

The separate least-hull theorem in `least_hull.md` proves EPSC_k equivalent
to its exact active-support fixed-point version XFP_k for k >= 1 without
increasing parameter counts. Hence one further calibrated candidate is

    XFP_1 + AU.

This supplies a concrete alternate wrapper for future compilation. The same
least-hull argument removes existential hull names from later definitions
that use those hulls only through incoming membership.

`formula_metrics.py` gives a reproducible expanded-tree comparison under
explicit implication/falsity/universal-quantifier macros. It counts 33 nodes
for AU, 39 for U-based pairing, 81 for OAdj, and 135 for OPair. Variable
payloads, DAG sharing, codecs, inference and all compiler costs are excluded.
These are formula counts, not Turing-machine state estimates.

## 9. Verification and sources

The independent finite diagnostic `research/packing/observational_packing.py`
checks local bounds and all represented supported hulls of the B instance,
full-profile congruence, and all local Kuratowski witnesses in finite
relational structures. Constructed cloned hereditarily finite controls make
the tuple tests nonvacuous in nonextensional structures. These tests are
diagnostics, not proofs of the infinite schema or a machine compilation.

The source-21 parameter proof and the current raw interpretation scope are:

* https://github.com/VladimirReshetnikov/ProveIt/blob/6ec2e80dbbe45a99b7812fb5757977307959a51e/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/21-two-notes-two_parameter_proof.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/6ec2e80dbbe45a99b7812fb5757977307959a51e/Computability/BusyBeaver/Research/ZFC/raw_psc.md

For the older general parameter-packing context, see Ralf Schindler and
Philipp Schlicht, *ZFC without parameters (A note on a question of Kai
Wehmeier)*, which explicitly uses Pairing and credits Azriel Levy (1974):

* https://www.math.uni-bonn.de/people/schlicht/ZFC_without_parameters.pdf

The present result does not invoke that note as a black-box theorem about
EPSC: its required pairing and raw congruence are established above.

