# Independent review: deterministic raw export removes arbitrary specialization

## Verdict

The proposed raw combination is mathematically valid, subject to the scope
and translation conventions below. It is a genuine combination beyond the
source's isolated restricted-specialization and inferred-export results:
the numeral `1` is not an admissible target of the restricted Use rule,
and no term argument is supplied to Use. Ordinary term substitution is used;
no computational normalizer is required.

It does **not by itself** establish a new global proof-checker size minimum.
The selector's implementation cost must be measured against a matched raw
checker, as well as against the repository's compact and validated frontiers.

## Source calculus and explicit scopes

Use the raw clause calculus with Refl, Eval, Use, Elim and Intro from
Chapter 5 of the pinned article. Context entries are conditional clauses
`[A; y.B(y)]`, with exactly one antecedent. An ordinary formula assumption
`F` is `[0=0; y.F]`, where `y` is unused. Refl is an arbitrary atomic
reflexivity rule, so `0=0` is always available.

A judgment has an explicit finite ordered list of distinct numerical
parameters `Pi`. Every term and free variable of its clauses and goal is
in this scope. The distinguished term `nu(Pi)` is its newest parameter;
set `nu(empty)=0` for definiteness. A fresh eigenparameter is appended to
Pi. All object-language substitutions are capture avoiding; binder names
can always be chosen fresh.

The target retains Refl, Eval and Intro unchanged. It has

    Gamma |- A
    ---------------- Use_nu      [A;y.B(y)] in Gamma
    Gamma |- B(nu(Pi))

and the deterministic Export rule below in place of Elim. This still has
five rule families (Eval has its inherited two computational cases).

## A raw selector with no body-freshness test

Let the eliminated formula be `D_{x,y} B(x,y)` and append a fresh parameter b.
If B is literally of the syntactic form

    I(y,0;u.x) = I(y,0;u.h(x,y,u)),

put `r_B(b) = h[b/x, S(0)/y, 0/u]` using simultaneous capture-avoiding
substitution. Otherwise put `r_B(b)=b`. The two iterator binders can have
different variable names; the pattern is stated up to alpha conversion,
or literally in a nameless encoding. The outer x and y binders and each
iterator binder are distinct. No condition that h omit x,y,u is needed.

Export is

    Pi;Gamma |- D_{x,y}B(x,y)
    Pi,b;Gamma,[B(b,0);y.B(b,y)] |- F
    ------------------------------------------------------ Export
    Pi;Gamma |- F[r_B(b)/b]

where b is fresh for Gamma and the major formula and the **exported
formula** has no free b. The intermediate F may contain b. The selected
term may also contain b; the freshness condition is on the exported formula,
not on r itself. This is the same logically sound treatment of cyclic names
as in the source's normalized Export rule.

The more restrictive selector suggested by the parent--recognize only
`C(y,0,x)=C(y,0,t)` with t independent of the displayed binders, choose t,
otherwise choose b--is valid too. The generalized selector trades an occurs
test for a fixed simultaneous substitution and may be easier to implement
with an existing substitution routine.

## Soundness of raw Export

The fallback has r=b and is ordinary D elimination: the exported goal then
equals F and its freshness side condition ensures b is absent.

In the recognized case, under the opened clause the two iterator zero
equations prove B(b,0). Clause Use at the numeral1, **in the unrestricted
source calculus or in the ordinary iPRA interpretation**, proves B(b,1).
The successor and zero equations give

    I(1,0;u.b) = b,
    I(1,0;u.h(b,1,u)) = h(b,1,0) = r_B(b).

Equality reasoning therefore gives b=r_B(b). Transport the branch's
F along that equation to obtain F[r_B(b)/b], and discharge b by ordinary
D elimination. This is a proof of target soundness in the source; it does
not assume that the restricted target itself has Use at1. This distinction
is essential: importing Use at1 into the target's completeness proof would
be circular, but using it to establish admissibility in the source is valid.

## Derived arbitrary specialization

For a term t in the current scope let

    N_t := D_{x,z}( I(z,0;u.x) = I(z,0;u.t) ).

The term t contains none of x,z,u by fresh binder choice. Intro at witness t
has the raw conclusion in its premise

    I(Sw,0;u.t) = I(Sw,0;u.t),

which is Refl. It ignores Intro's assumption. This works in either selected
mode, including t literally0, which selects progressive Intro. Thus N_t is
available in every scope and every context with no equality substitution,
no clause Use and no weakening of a prior target derivation.

To simulate an unrestricted Use of `[A;y.B(y)]` at t, prove N_t and Export
it at a fresh newest parameter b. Reconstruct the proof of A in the enlarged
scope/context, apply Use_nu to the original clause to get B(b), and Export.
The selector reads r=t from N_t, so its conclusion is B(t). The original
clause may occur anywhere in Gamma; it need not be newest. The antecedent A
may be compound or arbitrary rank. Only the numerical parameter b is newest.

The term t may be0,1, an old parameter, or an arbitrarily nested raw iterator.
It is not normalized, and its raw syntax is unchanged by the selector.

## Why the reconstruction is legitimate

It is unsafe to say simply 'weaken the proof of A': adding b changes the
meaning of Use_nu. The complete proof instead establishes the following
stronger invariant by induction on an **unrestricted source derivation**:

For any injective renaming of its free parameters into any larger ordered
target scope, and any target context containing renamed copies of all its
source clause occurrences, the renamed conclusion has a target derivation.

Extra clauses may have arbitrary origins. The induction is on the source
derivation, not on the target's regenerated proof. It supplies the antecedent
proof of A in the context opened at b as needed above. It needs no target
weakening theorem, no target substitution theorem and no target cut theorem.

The remaining cases are direct:

* Refl remains Refl after renaming.
* Eval remains an instance of the same raw equation scheme.
* Intro uses a new eigenparameter z at the end of the target scope. Its
  atomic/compound test and literal-zero witness test are invariant under an
  injective renaming; the source premise is translated by the induction
  hypothesis under the additional assumption clause.
* Elim is Export with F equal to the translated original conclusion. It does
  not contain the new b, so `F[r/b]` is literally F regardless of which
  selector branch is taken. Translate the source branch under b and the
  added opened clause using the induction hypothesis.
* Use is the name-and-export construction above.

All scope conditions hold by choosing the new names outside the finite free
supports of the current terms, clauses and goal. Occurrence embeddings of
contexts preserve repeated clauses; set membership would suffice if the
proof format does not distinguish occurrences.

Thus the target and the unrestricted raw source have precisely the same
derivable open clause sequents. By the pinned source's established raw
native-calculus equivalence and iPRA bridge, the target's ordinary
realization is bi-interpretable with iPRA, with both number domains whole,
actual equality and identity numerical composites. These are inherited
bridge theorems applied after the new exact-consequence result, not newly
mechanically verified Lean theorems in this package.

## The reflexivity boundary

Keep arbitrary Refl primitive. If it is instead represented only by the fixed
clause `[;y.y=y]` and **every** use of that clause is restricted to the newest
parameter, the construction is circular: proving N_t by Intro requires the
arbitrary reflexivity at the raw term `I(Sw,0;u.t)`, while naming t was supposed
to be the way to recover that specialization. No proof that this stronger
restriction is complete has been established here.

One may alternatively retain unrestricted specialization for unconditional
clauses and restrict conditional clauses only, but that is a different,
weaker reduction with a different checker dispatch. Do not conflate the two.
