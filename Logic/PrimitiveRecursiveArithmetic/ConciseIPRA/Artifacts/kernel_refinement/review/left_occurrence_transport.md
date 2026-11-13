# One-occurrence transport in the scalar native core

This is an auxiliary observation, not a checker-size record or a claimed
literature-new equality principle. It concerns the unmodified scalar term
language of the current `ConciseIPRA` core.

## Replacement rule

Let a *linear term context* `C[-]` be a finite term with exactly one hole.
Plugging is capture-avoiding. In particular, iterator-bound variables are
renamed away from all free variables in the plugged terms before plugging.
The identity context `[-]` is allowed. Replace the native equational
transport rule by the single schema

    Γ ⊢ s=t       Γ ⊢ C[s]=r
    ----------------------  LOR
           Γ ⊢ C[t]=r.

No occurrence of the hole is allowed in `r`. All other primitive rules,
terms, formulas and freshness conditions are exactly those of `NPrf`.

## Equality algebra without circular use of native transport

For any term `a`, put `j_a = I(0,a;u.0)`. Computation supplies `j_a=a`.
Use that same theorem as both premises of LOR, with identity context and
right endpoint `a`, to derive `a=a`. This uses no congruence principle.

Given `s=t`, apply LOR with the second premise `s=s`, identity context and
right endpoint `s`; this gives `t=s`. This proves symmetry.

Given `s=t` and `t=r`, first obtain `t=s` by symmetry. Then LOR with
identity context and second premise `t=r` gives `s=r`. This proves
transitivity, though it is not needed for the occurrence-by-occurrence
simulation below.

## Simulation of arbitrary equational transport

Suppose the inherited rule is applied to a fixed equation template
`A(v)=B(v)`, an equation `s=t`, and a proof of `A(s)=B(s)`.

1. Alpha-rename every iterator binder in the template away from the free
   variables of `s,t` and all its fixed parameters.
2. Traverse the free occurrences of the distinguished variable `v` in
   `A(v)`. At each occurrence, the current left term has the form `C[s]`
   for one linear, capture-avoiding term context. Apply LOR with `s=t`.
   After finitely many applications the equation is `A(t)=B(s)`.
3. Apply the derived symmetry rule, obtaining `B(s)=A(t)`.
4. Traverse the free occurrences of `v` in `B(v)` and use LOR at each one.
   The resulting equation is `B(t)=A(t)`.
5. Apply symmetry again. The result is `A(t)=B(t)`.

Occurrences are tracked in the original template, not found by replacing
every subterm syntactically equal to `s`: passive parameters can contain
such subterms and must remain unchanged. At each step every occurrence
outside the selected hole is a fixed part of `C`. A formerly bound
occurrence of a variable named `v` is not a free template occurrence and
is never selected.

This is an explicit finite proof transformation. It does not rely on
cut admissibility, numerical induction, ordinary first-order logic or a
general substitution theorem for derivations. The existing proof of the
native core's equivalence with iPRA can therefore be reused after this
kernel-equivalence theorem.

## Converse simulation and identity composites

An LOR step is a native equational transport step with equation template
`C[v]=r`. Thus inclusion of LOR derivations into native derivations is
immediate. The transformation in the preceding section supplies the
reverse inclusion by induction on a finite native derivation, replacing
only its transport nodes.

Consequently, for every well-scoped context and formula,

    LPrf Γ A  iff  NPrf Γ A.

The translations on numerical terms and native formulas are literally the
identity. Composing this identity comparison with the repository's
`NativeBiInterpretation` yields the same whole-domain, actual-equality
bi-interpretation and equiconsistency with iPRA. No new arithmetic bridge
or changed interpretation is needed.

## What this does and does not simplify

One primitive use now rewrites one occurrence in one numerical term. The
primitive interface does not take a pair of arbitrary term templates and
does not perform simultaneous replacement on both sides of an equation.
A proof certificate can supply a position in the left side of the minor
equation instead of a term template.

This is a local simplification of the inference interface. It is not known
to reduce the complete Python checker: the current checker shares its
generic substitution routine between transport and closure elimination,
whereas position-based rewriting needs a scope-aware traversal of its own.
Its implementation cost must be measured before making any quantitative
claim. The older `counter_congruence` package already proves a stronger
fixed-position sufficiency result for a different, counter-aware recursor.
The elementary LOR reduction is therefore not a significant mathematical
breakthrough, and it should not be presented as one.
