# Independent review of the bounded-arity SS+RED proposal

Review date: 16 October 2026. Reviewed artifact:
`logic_work/subworld_arity_notes.md`, through its direct derivation of ZF
without Foundation or Choice and its consistency calibration.

## Conclusion

**The mathematical argument passes this independent review.** I found no
counterexample, circular dependency, hidden use of Extensionality in the raw
part, or use of Foundation, Replacement, Power Set, or a choice of a family
of witnesses in the bisimulation construction. The conclusion is an ordinary
mathematical assessment, not a Lean/Coq check and not a proof of any new
Turing-machine state count.

The source theory must have actual logical equality, a shared constant `W`,
unrestricted bound-variable resources, and all matrix instances allowed by
the stated free-variable restriction. In particular, one cannot transport
this conclusion to a finite-sort or equality-free proof engine merely by
deleting some of that engine's quantifier or equality rules.

Subject to these hypotheses, the proposal supplies a credible new source
theory for a consistency-search compiler. Its full source theory is
equiconsistent with ZFC, with the equivalence provable in ZFC. The syntax
measurements are useful compiler inputs, but do not establish a machine
smaller than the current 253-state public candidate.

## 1. The finite-arity reduction has a noncircular dependency order

The relevant chain is:

1. The inhabited separation clause gives both nonemptiness of `W` and
   ordinary restricted separation.
2. `RED2` uses the actual object `W` as an ambient container witness to
   obtain a container in `W` for two elements of `W`. Restricted separation
   then forms exact literal pairs in `W`.
3. Exact Kuratowski pair codes have unique endpoints in pure equality
   logic. Iterating them gives fixed-length tuple codes with unique
   coordinates.
4. Nonemptiness pads `RED2` down to `RED1` and `RED0`. A tuple code in `W`
   packages all parameters of an arbitrary `RED_n` instance into one
   parameter, yielding full reducibility.
5. Full reducibility reflects a counterexample tuple coordinate by
   coordinate. Therefore any `W`-free assertion true absolutely at all
   tuples from `W` is true at all tuples in the raw universe. This yields
   global Pairing.
6. Global Pairing codes arbitrary separation parameters, including the
   actual object denoted by `W`, into an external tuple. Restricted
   separation at that code recovers full separation.

The final tuple need not belong to `W`. That is permissible because the
two matrix-parameter slots in the separation half are **unguarded**; only
the source object is required to belong to `W`. This is a material feature
of the exact stencil, not an incidental convenience.

The joined formula has the same matrix in two clauses, but universal
closure permits projection of each clause for every allowed matrix. There
is no unwanted logical coupling between their uses. The free witness
variable in the antecedent of `RED2` is intentionally rebound in its
consequent. Capture-avoiding renaming of other bound variables is sufficient.

## 2. Endpoint uniqueness really survives failure of Extensionality

For a fixed exact code `t` of `(a,b)`, the intersection of the literal
extensions of members of `t` is `{a}`, and their union is `{a,b}`. The first
identifies the first endpoint. With that endpoint fixed, the second
identifies the second endpoint, including the repeated-coordinate case.

This proof never concludes that two raw objects with the same incoming
membership profile are identical. The singleton and pair used inside a
code may have distinct coextensional representatives; two different codes
may represent the same endpoints. What is impossible is one fixed code
representing different endpoints. That is exactly the direction required
by the tuple and relation constructions.

Actual logical equality is essential to this proof. Replacing it by an
arbitrary binary predicate requires a separate congruence or interpretation
argument. The original raw finite-sort countermodels are therefore not
countermodels to the equality-bearing theory reviewed here.

## 3. The weak-product argument does not assume Choice

After full separation and reducibility are available, global separation
follows by upward transfer. Restricted separation of `x in W` by membership
in `W`, followed by reducibility of a distinguishing witness, proves
transitivity of `W` without identifying coextensional objects.

For `x,y in W`, every endpoint in `x times y` is in `W`, and there is at
least one ordered-pair code in `W` for those endpoints. Separating suitable
codes from the single raw object `W` produces a weak product. The existence
assertion for such a product is `W`-free, so upward transfer makes it global.

Given a weak product and a definable endpoint relation, separation retains
all qualifying codes already in that product. Endpoint uniqueness ensures
that the resulting code represents exactly the intended relation. It is
unnecessary to choose one representative per pair, or to have a set of all
possible raw representatives.

Rooted transitive covers must contain the root as an element, rather than
merely include its members. The proposed formula has this stronger
condition. Transitivity then keeps all children encountered in the
bisimulation conditions inside the chosen covers.

## 4. The all-bisimulations fixed point is legitimate

The definition of `B(a,b)` is an explicit first-order existential formula:
there exist rooted transitive covers and a set-coded relation satisfying
the displayed bisimulation conditions and linking `a` to `b`. Its syntax
contains no `W`. It is defined before using separation with `B` as the
separating predicate.

Reflexivity uses the diagonal relation on a transitive cover. Symmetry
reverses a represented relation. Transitivity represents the composition
of two witnessing relations in a weak product of the first and last
covers. The two middle covers may differ: a middle endpoint linked by both
relations belongs to both covers, and each of its children belongs to
both by transitivity. Hence the forth/back argument for the composition
is valid.

The forward fixed-point implication reuses a witnessing bisimulation for
each matched pair of children. For the reverse implication, fix covers
`U,V` containing the proposed roots. Separate

    B(s,t) OR (s=a AND t=b)

inside a weak product of `U,V`. A pair already satisfying `B` has the
required child matches by the forward implication. The added root pair
has them by the hypothesis. The matching children remain in `U,V`, so the
separated relation is itself a set-coded bisimulation.

There is no recursion through the definition of `B`, no appeal to a
universe-sized relation object, and no collection of one witness for each
child pair. Ordinary first-order separation with the already defined
predicate `B` is the only comprehension step here. This repairs the
well-founded-cover domain problem in the preliminary sketch by changing
the relation's definition, not by assuming every raw object is well-founded.

## 5. The quotient satisfies the correct schemes

For

    E*(a,b) := EXISTS c in b B(a,c),

the equivalence and forth/back properties of `B` give congruence of `E*`
in both arguments. Equality of the `E*` incoming profiles of two roots
gives child matching by reflexivity, and the reverse fixed-point
implication identifies the roots modulo `B`. Thus target Extensionality
holds when target equality is interpreted by `B`.

For target separation, an object in target `W` has a `B`-equivalent literal
representative `x' in W`. Raw separation at `x'` gives `y in W` whose
literal members satisfy the translated matrix. Invariance of the matrix
under `B` shows, in both directions,

    E*(z,y) IFF (E*(z,x) AND translated_matrix(z)).

The raw output is a target member of `W` by reflexivity. Raw full separation
permits arbitrary parameters and literal `W`, so the translated matrix is
an admissible instance.

For target reducibility, there are finitely many target parameters; choose
literal representatives of those parameters in raw `W`, apply invariance,
and use raw reducibility. This is ordinary finite existential reasoning,
not a choice principle. Since both `B` and `E*` are defined without `W`, a
`W`-free target matrix remains `W`-free after translation. This last fact
is crucial and is satisfied by the proposed definitions.

The interpretation uses all raw objects, including the raw object `W`.
Global rooted covers establish reflexivity there too. In a set-coded model
the ambient metatheory can take an actual quotient of the domain, while
the formal interpretation can work directly with the equality congruence.

## 6. Calibration and its limits

The direct derivation of ZF without Foundation or Choice after adding
Extensionality is sound. Subset closure inside `W` uses Extensionality
precisely where needed. Global separation on `W` gives Union and Power Set
for inputs in `W`; upward transfer gives the global axioms. Nonemptiness,
an empty object in `W`, and reducibility of successor existence make `W`
an inductive set. Functional Replacement reflects each output into `W`;
functionality identifies it with every other output, so separation of `W`
gives the image. Upward transfer then removes the restriction on the domain
and parameters. No Collection axiom was smuggled into this reasoning.

The usual cumulative-hierarchy interpretation restores Foundation, and
the constructible-universe interpretation restores Choice. For the upper
consistency direction, finite reflection supplies a suitable rank for the
finitely many reducibility instances in a fragment; separation with
arbitrary parameters outside that rank still works because a subset of
an element of the rank belongs to the rank. Compactness is needed for the
whole scheme. This does not assert the existence of a rank satisfying all
of ZFC, an externally well-founded model, or an inaccessible cardinal.

Friedman's 5 October 1997 seminar notes explicitly present the subworld
schemes and their calibration, but their printed `EXT` is an equality-free
incoming/outgoing congruence condition. The proposal avoids treating that
condition as literal identity: it states its own source equality assumption
and directly proves the required post-quotient set-theoretic axioms.

Primary reference:
<https://cpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/2014/01/TalkAxiomSetThy-ts05xn.pdf>,
especially pp. 3–5. The notes also explicitly describe cumulative-hierarchy
and constructibility interpretations on pp. 2–3.

The 10 October 1997 presentation also states the calibration and the
interpretability claim for raw subworld separation and reducibility:
<https://cpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/2014/01/FromRusselltoSetThy-1rnmfbg.pdf>.

The report should preserve the distinction between: (i) this ordinary
mathematical interpretation and ZFC-provable consistency equivalence;
(ii) a serialized proof translation; and (iii) a verified blank-tape machine
with an exact state count. Only the first is supplied by the new argument.
