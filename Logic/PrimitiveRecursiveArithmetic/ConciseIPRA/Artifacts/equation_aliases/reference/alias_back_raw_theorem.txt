# Raw aliases centralize equality and specialization

## Exact result

There is a raw, normalization-free presentation of the repository's full
first-order iPRA consequence relation in which:

* equality replacement is backward substitution for the **newest free
  numerical parameter only**;
* a retained clause can be specialized at the **newest parameter only**
  (at zero if the numerical scope is empty);
* a fresh alias `b=t`, with ordinary substitution of `t` for `b` when its
  scope closes, supplies all arbitrary equality transport and all arbitrary
  clause specialization;
* no reflexivity axiom, root joining case, equality template, or arithmetic
  normalizer is primitive.

This replaces the previous equality interface and restricts specialization,
at the cost of adding the Alias rule. It does not delete an arithmetic
principle or show a globally smallest presentation. In particular it is
not the raw variable-substitution proposal ruled out by the repository's
obstruction: the additional Alias rule proves reflexivity outright.

## Syntax

Use the unchanged raw scalar terms

    t ::= x | 0 | S(t) | I(n,a;u.h).

Only u is bound, in h. Formulas are literal equations and the paired binder

    A ::= s=t | D_{x,y}B,
    D_{x,y}B := exists x (B(x,0) -> forall y B(x,y)).

A context is a finite list of clauses `[A; y.B]`, read `A -> forall y B`,
or clauses `[; y.B]` without an antecedent. Ordinary assumptions A are
`[; v.A]`, with v unused. There is no fixed reflexivity clause. The root
context and numerical scope are empty. Contradiction is `0=S(0)`.
All terms and substitutions are raw: no computation or definitional
conversion is hidden in formula equality.

Let `last(Pi)` be the newest parameter in the ordered numerical scope Pi,
or zero in the empty scope. All binder substitution is capture avoiding.

## Complete rules

**Compute-zero:** infer `I(0,a;u.h)=a`.

**Compute-successor:** infer
`I(S(n),a;u.h)=h[I(n,a;u.h)/u]`.

**Use-newest:** from A infer `B(last(Pi))` if `[A;y.B]` occurs in the
context; omit the premise when that clause has no antecedent. Its clause
position is supplied, but no numerical target is supplied.

**Back-newest:** from `b=t` and `F[t/b]` infer F, where b is the newest
free numerical parameter of the current scope. The formula F is the
claimed conclusion; there is no independently supplied template. The
term t may contain b; substitution is simultaneous once. Both premises
are established in the same context as F.

**Alias:** from a derivation of F under `Gamma,b=t`, with b a new
parameter and t a term in the outer scope, infer `F[t/b]` under Gamma.
The fresh b is absent from Gamma and t. The discharged assumption is
an ordinary assumption, stored as the antecedent-free clause
`[;v.b=t]`. There is no additional equality premise.

**Open:** from `D_{x,y}B` and a derivation of A under the additional clause
`[B(b,0); y.B(b,y)]`, infer A, where b is fresh and absent from A.

**Close:** from `B(t,eta)` as an ordinary additional assumption derive
`B(t,S(z))`, with z fresh, and infer `D_{x,y}B`. Here eta=z exactly when
B is a literal equation and t is literally zero, and eta=0 otherwise.
The witness t is an arbitrary term in the outer scope. This is the
inherited witness-selected introduction; no claim is made that its
witness has also been removed.

The first two computations may be grouped as one implementation family,
but remain two equations. Alias and Open are two distinct scope rules;
grouping them does not erase their different logical content.

## Step 1: unrestricted backward substitution and Alias give all equality

First let Back allow any free numerical parameter v. This temporary
calculus is stable under injective parameter renaming and context
extension, by a structural induction on proofs: being a free parameter,
being zero, and being a literal equation are preserved. This is not an
assumption about the later newest-only calculus.

Reflexivity requires only a hypothesis and Alias. Under a fresh b=t,
use that hypothesis and close its alias scope. The result is t=t.

Given s=t, obtain symmetry as follows. Open the alias b=s. Back with
major b=s and minor s=t yields b=t. Reflexivity gives t=t. Back with
major b=t and minor t=t yields t=b. Closing b=s yields t=s.

Given s=t and F(s), where F is any formula template with its distinguished
variable fresh for the new aliases, first derive t=s. Open b=t. Back
with major b=t and minor t=s yields b=s. Back with major b=s and minor
F(s) yields F(b). Closing b=t yields F(t). Thus arbitrary formula
transport is admissible, without arithmetic, induction, normalization,
an equality reflection function, or a primitive root-joining operation.

For the repository's one-term crossed transport, apply this to
F(v) = (h(v)=r), and then symmetry: from s=t and h(s)=r infer r=h(t).
This gives the unchanged raw scalar core's equality rule.

All these displayed constructions can be confined to literal equations:
if both Back and Alias are restricted to equation conclusions, they
still derive reflexivity, symmetry and the one-term crossed transport.
The existing logical construction then recovers transport in compound
formulas when arbitrary clause specialization is retained. This observation
concerns the equality subsystem: the later removal of specialization
targets uses Alias with a compound exported formula. The supplied final
implementation allows arbitrary formulas in Alias and Back, and does not
implement an equation-only Alias restriction.

## Step 2: the newest parameter suffices

The key is a generalized compiler theorem, not weakening of already
completed newest-only derivations.

Take a finite derivation in the temporary calculus with Back at any free
parameter and Use at any numerical term. Let theta injectively embed its
ordered free parameters in an arbitrary target scope, and let a position
map identify its context clauses with their exact theta-images among an
arbitrary larger target context. The claim is that the derivation has a
target derivation of its theta-translated conclusion. Additional target
parameters and clauses are allowed. Prove this simultaneously for every
source derivation, by induction on that derivation.

Computations translate literally. At Close and Open, map the source fresh
parameter to the new target parameter, append the corresponding clause to
the position map, and recurse on the source branch. The Close mode is
preserved by the injective renaming: equations stay equations and a
nonzero variable or constructor does not become literal zero. At Alias,
translate its defining term, open the corresponding target alias, extend
both maps, and recurse on its branch. Capture-free substitution commutes
with the injection.

For an old Back step, write its premises as v=t and F[t/v], and its
conclusion as F. Open a new target alias b=theta(v). Reinvoke the induction
hypothesis on **both proper source-premise derivations** directly into
this extended target context. They produce theta(v)=theta(t) and
theta(F[t/v]). Since b is newest, Back using b=theta(v) converts the
first to b=theta(t). Another newest Back, with the claimed goal obtained
by replacing theta(v) by b in theta(F), converts the second to that goal.
Closing b=theta(v) returns exactly theta(F). Both recursive calls are on
strictly smaller source derivations. No target proof was weakened.

For an old Use at a term t, open a target alias b=theta(t). Reinvoke the
induction hypothesis on its antecedent proof directly in this extended
context, if the clause has an antecedent. Use the mapped clause at the
newest parameter b, obtaining theta(B)(b). Close the alias to obtain
theta(B)(theta(t)), exactly the old conclusion. An antecedent-free clause
requires no recursive premise. Thus arbitrary specialization is removed
without a predecessor construction or a naming formula.

At the identity embeddings and empty target extension this gives a
consequence-preserving translation to the displayed calculus. The reverse
direction is immediate: newest Back and newest Use are allowed in the
temporary calculus. Weakening and the usual persistent-premise facts can
be transferred *after* this equivalence has been established.

## Full first-order equivalence and both interpretations

The temporary calculus contains the old raw scalar calculus: recover its
transport as in Step 1, and retain its computations, arbitrary Use, Open
and Close. Conversely its additional rules are valid in the old ordinary
realization. Back is equality substitution in the reverse direction.
For Alias, interpret its premise after setting the fresh b equal to t;
the additional assumption becomes the reflexive t=t and is discharged.
Equivalently, introduce and eliminate the unique name of the value of t
using the old theory's derived ordinary first-order logic. This uses the
established native/ordinary equivalence, and no normalization.

Step 2 therefore establishes the exact same native Eq/D consequences as
the inherited raw scalar calculus. The old translation eliminating Q by
an unused D witness gives the full native Eq/Q/D consequence relation as
well. The numerical terms, their ordinary values, and the formula reading
have not changed. Compose this consequence equivalence with the pinned
repository's established iPRA interpretations. Both numerical domains
remain whole, equality remains actual, and both numerical composite
graphs are x=y. The formula round trips are unchanged. Thus the new
presentation is equiconsistent and bi-interpretable with full first-order
intuitionistic PRA.

## Why this is different from the previous unsuccessful raw proposal

The article, chapter 9, "Not achieved", records that backward-only
parameter replacement with an ordinary fresh-name *elimination* can get
stuck: once the goal omits the alias, it may require itself as premise.
The present Alias rule substitutes into the *exported conclusion*. It
does not merely drop an assumption from an already alias-free goal.
For example its single hypothesis b=t exports t=t. This is precisely
the step unavailable to a backward-only replacement rule with no
substitutive alias discharge.

The parameter_substitution package retains a nonvariable root-joining
case to bootstrap reflexivity and aliases. Here Alias is primitive and
root joining is derived, so the construction does not refute that
package's raw no-reflexivity obstruction. On full normal forms,
witness_discharge and conditional_copy already use substitutive discharge
of existential witnesses. The new point here is a raw definitional alias
with no existential major, combined with goal-directed backward equality
and a compiler that removes all non-newest equality sources and all
specialization targets. No literature-wide originality claim is made.

## Implementation and validation

`code/raw_alias.py` is the readable complete checker for the final
newest-Back/newest-Use system. `raw_alias_unrestricted.py` checks the
temporary unrestricted-source/unrestricted-target system.
`raw_template_matched.py` checks the original raw template calculus with
the same antecedent-free ordinary assumptions.

`code/translate.py` first compiles template equality using the explicit
raw Alias/Back equality proofs, then applies the generalized-context
compiler of Step 2. Each completed compiler call is replayed by its
standalone target kernel, including calls under nontrivial context
embeddings. Neither compiler is trusted by any acceptance module.

Thirty-two inherited closed raw template certificates have been compiled
and replayed successfully, including nested compound binders, computation,
closure specialization, nontrivial induction hypotheses, capture avoidance,
passive source occurrences and zero sources. The tests support the
implementation; the general equivalence is the written induction above.

The completed standalone validation suite has 58 candidate cases (32
compiled certificates, four additional positives and 22 negatives), run
through both target programs in normal Python and with -O. Both matched
controls are replayed on the 32 source proofs. All 360 process executions
have the expected result. A separate open-sequent example checks a
non-order-preserving injective parameter map and a non-contiguous clause
position map into a larger target context.

Complete-program measurements under CPython 3.12.14, stripping real
docstrings and using ast.unparse plus one final newline:

| Program | Tokens | AST nodes | Normalized bytes |
| --- | ---: | ---: | ---: |
| Readable matched template control | 764 | 883 | 2918 |
| Readable newest Back/Use with Alias | 825 | 966 | 3149 |
| Same control with scope inferred from context and shorter CLI | 716 | 838 | 2683 |
| Same target simplifications | 773 | 916 | 2903 |

Thus the mathematical restriction has not yet produced a smaller matched
complete checker. It does not meet the compact repository envelope. The
small variants make the same changes to scope bookkeeping and the CLI on
both sides; they do not add a new mathematical rule.

Pinned repository commit: 36d37fc1071fe289371f6bcd7dcfa0eac593a5a6.
Primary comparison: Artifacts/parameter_substitution/code/raw_template_control.py.
Relevant previous mathematics: article chapters 5, 6 and 9 and the
retained_premises incoming raw-variable obstruction. The existing MIT-0
license applies to attributed inherited code.
