# Bounded quantifiers and the strict Π₂ side invariant

Foundation's `Hierarchy` used in `ParsonsSide` is not a strict prenex grammar.
In particular, its bounded-universal constructor can keep a formula in Σ₁
when its matrix is already Σ₁. Thus the Lean theorem that the three induction
premises lie in `Hierarchy 𝚷 2` does not by itself produce formulas of the
shape `∀u ∃v D(u,v)` with bounded D, nor a rule-calculus proof relating those
forms. The missing proof is relevant to the cut-free recursion: before the
principal induction case applies its guarded Σ₁ rule, the outer universal
variables of the Π₂ side context have to be fixed and the remaining side
formula must be Σ₁.

A concrete obstruction already appears at Σ₁. Let D(i, y, a) be a bounded
formula with arbitrary further parameters a, and let n be a term independent
of i and y. The syntactically Σ₁ formula

    H(n,a) := ∀ i < n, ∃ y, D(i,y,a)

has the candidate strict Σ₁ form

    C(n,a) := ∃ B, ∀ i < n, ∃ y < B, D(i,y,a).

The matrix of C has only bounded quantifiers, so a concrete adapter must
construct, for each D, rule-calculus proofs of both implications between H
and C, uniformly with all parameters retained. The direction C → H is a
logical weakening of the witness bound. The direction H → C is a finite
collection or bounding principle: a separate bound is available for each
of finitely many i, and a common B is required. This formulation uses one
numeric bound and avoids assuming a pairing function or coding a tuple of
witnesses. It does not establish that the required implication is derivable
in the currently implemented rule calculus.

One possible mathematical construction studies C(k,a) by Σ₁ induction on k:
C(0,a) is immediate, and from C(k,a) and an instance of D(k,y,a), a bound
larger than both the old B and y gives C(k+1,a). This is only a proof plan:
it must be formalized using actual ordered-ring axioms, exact substitutions,
and the calculus's Σ₁ induction rule. In particular, the assumption H is an
open side hypothesis. It cannot simply be discharged through the induction
rule without a proved admissibility theorem: adding ¬H as a guard need not
preserve Σ₁ complexity. Nor does the existing `ParsonsRuleEmbedding` solve
this issue, because it preserves its base theory and does not eliminate the
induction axioms. Whether this particular bounding proof can be carried out
in the current rule calculus, or whether another invariant avoids it, remains
to be established.

For a complete strict Π₂ adapter, the concrete deliverable is a Lean function
which, for each relevant Π₂ side formula with all its free parameters,
returns a finite tuple of universally quantified variables, a finite tuple of
existential witnesses, a bounded matrix, and actual rule-calculus derivations
of both implications. A proof must handle every constructor of the relevant
hierarchy, including bounded quantifiers and capture-avoiding substitutions;
tuple variables avoid silently assuming that one arithmetic variable codes an
arbitrary tuple. The cut-free translation then has to show that the resulting
side form is stable under each LK rule and under opening parameter blocks.
Neither this adapter nor the complete cut-free translation has been proved.
