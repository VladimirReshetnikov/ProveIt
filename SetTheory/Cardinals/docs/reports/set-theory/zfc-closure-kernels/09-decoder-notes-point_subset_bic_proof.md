# Point-seeded BIC needs only subset bounds

## Claim and scope

In classical first-order membership logic with ordinary equality, the
point-seeded bounded-image-closure schema with local bound

    y subseteq b

is deductively equivalent to the original point-seeded schema with bound

    y in b or y subseteq b.

The schemas have exactly the same closure and global-image conclusions.
The reduction is uniform in the arbitrary relation formula. In particular,
adding Extensionality to both presentations preserves deductive equivalence.
The argument below does not itself need Extensionality.

This resolves the specific open question in the source-02 retained article,
"Can the membership arm be deleted from point-seeded BIC?" It does not by
itself compile the smaller schema into a Turing machine or validate the
entire pre-existing ZFC calibration of the retained article.

## 1. Notation

Let

    B_sub(rho) := forall x exists b forall y (rho(x,y) -> y subseteq b).

The subset-only point-seeded axiom for rho is

    B_sub(rho) -> forall a exists C [
        forall x,y (((x=a or x in C) and rho(x,y)) -> y in C)
        and forall y (y in C -> exists x rho(x,y)) ].

The seed variable a and witness C are fresh for rho. Any intended seed
may occur in rho as an ordinary parameter and then be instantiated equal
to a. All bound variables in the formulas below are renamed apart.

Write

    Empty(e) := forall u not(u in e),
    Sing(x,z) := forall u (u in x iff u=z),
    IsSing(x) := exists z Sing(x,z),
    Trans(C) := forall x (x in C -> x subseteq C).

`Sing(x,z)` identifies the member of a singleton by ordinary logical
equality; it does not require a previously available singleton term.

## 2. Empty sets and singletons require no bootstrap assumptions

For rho(x,y) identically false, B_sub is immediate (choose b=x). The
global-image clause forces every member of the output C to satisfy false.
Thus an empty set e exists. The nonempty-domain convention of ordinary
first-order logic supplies a seed for this application.

For a parameter z, use the constant relation rho(x,y) iff y=z. Its fiber
is subset-bounded by z itself, since z subseteq z. Seed at the already
available e. Closure puts z in the output C, and the global-image clause
implies every member of C equals z. Thus forall z exists x Sing(x,z).

The singleton's member is unique: if Sing(x,z) and Sing(x,z'), then
z in x and hence z=z'. A singleton is not empty. Neither assertion uses
Extensionality, Separation, Union, Power Set, Pairing, or Choice.

## 3. A single gated relation supplies a transitive container

Fix an arbitrary A and an empty e. Define rho_{A,e}(x,y) by the following
three disjoint cases:

    (x=e and y subseteq A)
    or (x!=e and Sing(x,y))
    or (x!=e and not IsSing(x) and y subseteq x).

This is an ordinary first-order formula in the permitted schema language.
The explicit gates avoid combining a nondeterministic subset fiber with
an unrelated singleton-decoding fiber at the same input.

### The fibers are subset-bounded

For each x use classical case analysis:

* If x=e, choose b=A. All outputs are subsets of A.
* If x!=e and IsSing(x), choose its unique member z as b. Every output
  equals z, hence is a subset of b=z.
* If x!=e and not IsSing(x), choose b=x. Every output is a subset of x.

This proves B_sub(rho_{A,e}). No common union, selection function, set of
bounds, or Choice principle is involved: the conclusion is only the
pointwise first-order statement forall x exists b.

Apply point-seeded BIC with seed a=e. Let C be its output.
Every subset of A belongs to C by the root case. In particular, A in C
and e in C. We now prove Trans(C).

Take x in C and z in x.

* If x=e, this is impossible because e is empty.
* If IsSing(x), its unique member is z; the second case gives
  rho_{A,e}(x,z), so z in C.
* Otherwise, choose s with Sing(s,z), using the already proved singleton
  existence. Since z in x, we have s subseteq x. The third case gives
  rho_{A,e}(x,s), hence s in C. The singleton s is not e, and the second
  case gives rho_{A,e}(s,z), hence z in C.

Thus every member of every x in C is in C, proving

    forall A exists C (A in C and Trans(C)).

Only the forward closure half of BIC was used in this step. The no-junk
clause causes no obstacle: by singleton existence, every object y is in
the global range of the second case, with input any singleton of y.
Consequently the no-junk clause for this particular rho is automatically
true for any C.

## 4. Recover the original mixed-bound schema directly

Suppose a relation rho has the original local mixed bound:

    forall x exists b forall y (rho(x,y) -> (y in b or y subseteq b)).

Fix x and such a b. By Section 3 obtain a transitive V with b in V.
If rho(x,y), then:

* If y in b, transitivity gives y in V and then y subseteq V.
* If y subseteq b, transitivity gives b subseteq V, so y subseteq V.

Therefore V is a subset bound for the entire rho-fiber at x. Generalizing
proves B_sub(rho). The subset-only BIC axiom for rho now gives exactly the
conclusion of the original mixed-bound axiom for rho.

Conversely, a subset bound is a mixed bound by disjunction introduction;
the original mixed-bound schema therefore gives every subset-only instance.
This proves deductive equivalence. The new implication uses fixed BIC
instances for Empty Set, Singletons, and the gated relation, followed by
the instance for rho. It is uniform in rho and its parameters, and gives
effective finite-proof transformations in both directions.

## 5. Direct Union and Separation checks

Although Section 4 is the shortest calibration reduction, the originally
suspected bootstrap gap can also be closed directly.

Given A, take transitive V with A in V. For Separation use the constant
relation rho(x,y) iff y in A and phi(y). Its outputs belong to V and
therefore are subsets of V. Subset-only BIC applies, and its point seed
and no-junk clause give exactly the desired separated set.

For Union use the constant relation

    rho(x,y) iff exists z (z in A and y in z).

Every output y belongs to V, hence is a subset of V. BIC again produces
the exact union of A. No invocation of Union occurred in the transitive
container proof or in its fiber bounds.

## 6. Syntactic size under the retained article's exact convention

The unmodified source-02 `02-seeded-formulas.py` already contains both
templates: `PIBI` for the mixed case and `PISI_open` for the subset-only
case. Its metric expands connectives into implication, universal
quantification, and falsity, counts a relation-schema hole once at each
occurrence, and excludes variable payloads and parameter closure.

* Mixed point-BIC: 53 nodes; subset-only point-BIC: 49 nodes.
* Ext plus mixed point-BIC: 69 nodes; Ext plus subset-only point-BIC: 65.
* Both schemas contain three relation-hole occurrences.
* The four removed nodes are one membership atom, two implication nodes,
  and one falsity node, exactly the expansion of the removed disjunction
  arm. Universal quantifiers, equality atoms, and hole counts are unchanged.

These are formula-template tree counts only. They are not register-program
nodes, compiled formula-builder costs, or Turing-machine states. The
companion measurement script loads the unchanged source module, records
its hash, and regenerates the comparison.

## 7. The same deletion works for the subset seed

The proof of the bound replacement uses the point seed only through the
fact that the root is an admitted seed: sigma(e,e). Consequently it works
unchanged for any fixed seed predicate with a pure logical proof of
forall a sigma(a,a). This is a bound-equivalence statement, not a claim
that every reflexive seed produces a consistent or calibrated theory.

In particular, take sigma(x,a) to be x subseteq a. The constant-fiber
bootstrap still works, and the same empty root e activates the first
case of rho_{A,e}. Any additional seed inputs are harmless, since BIC
still gives its stated closure and range conditions. The transitive
container argument and mixed-to-subset conversion are unchanged.

Thus the equality-bearing subset-seeded mixed-bound and subset-bound-only
theories are deductively equivalent. The existing equality-elimination
translation using incoming-profile equality D together with EC applies
to the latter exactly as it does to the former: both bound/seed wrappers
are equality-free, Extensionality translates to a tautology, and EC
supplies the missing first-coordinate congruence. This retains EC; it
does not resolve the separate proposal to delete EC.

The measurement script constructs the new subset-seeded template as

    Imp(templates['PISI_open'].args[0], templates['SIBI'].args[1]).

That is the unchanged SIBI conclusion with the already defined subset-only
local-bound premise. The exact source-02 count is 52 nodes, versus 56 for
SIBI. The full equality-bearing presentation is 68 nodes including Ext,
versus 72; the equality-free control is 79 including EC, versus 83.
These have the same four-node reduction and three relation holes.

## Verification status

The argument is a complete mathematical derivation using ordinary
first-order logic and explicit instances of the stated schema. No proof
assistant formalization is claimed. All variable-freshness conditions can
be met by fixed renaming; the intended empty root is an ordinary parameter
before the schema's fresh seed is instantiated with it.
