# Research log and discarded claims

## Starting point

The reviewed `fastunknot.simplify` implementation searches RIII traces of depth
at most four.  After the first RIII move, recursion is confined to the
neighbourhood of the *last* move.  The repository records strong empirical gains
but no asymptotic completeness theorem for that locality restriction.

## First attempted theorem - rejected

An initial conjecture said that every shortest first-unlocking trace could be
commuted into a form in which each new move meets the accumulated footprint of
all previous moves.  This is false for general local systems.  Two independent
moves can prepare disjoint regions, after which a third move meeting both regions
unlocks the reduction.  Neither preparatory move can be deleted, and no legal
chronological ordering has connected prefixes.

The hand fixture `two_birth_branch` in `results/validation.json` is the minimal
three-move obstruction.  This invalidated the first proof sketch before it was
placed in the article.

## Corrected invariant

The right parameter is the **birth number**: the number of neutral actions whose
footprints are disjoint from the union of all earlier footprints.  Birth actions
are pairwise disjoint and commute left across every predecessor, so all births
can be front-loaded.  Thereafter every move meets the accumulated footprint.
This gives a complete normal form and the bound

    N^{b+O(1)} (C k)^k.

The full dependency graph of a *shortest* trace remains connected; this is a
separate theorem and explains why births are causal branches rather than
irrelevant work.

## Why the theorem is useful but not a full solution

- `b=1` strictly generalizes the existing last-neighbour chain search.
- Constant `b` and logarithmic `k` give `N^{O(log log N)}` time.
- Logarithmic `b` and logarithmic `k` give a conventional
  `N^{O(log N)}` quasi-polynomial bound.
- No proof is known that arbitrary unknot diagrams satisfy either hypothesis.
- A failed bounded search remains inconclusive and must fall through to the
  exact recognizer.

## Computational checks

The generic code was compared with unrestricted BFS on 5,000 deterministic
random finite local systems.  Of these, 3,209 were initially reducible, 131 had
no witness within depth six, and 1,660 had a witness.  There were zero failures
of front-loading, normal-form completeness, or dependency connectedness on the
witnessed cases.  These checks validate the implementation on finite fixtures;
they do not replace the proof and do not test knot diagrams.

## Implementation audit corrections

Two additional completeness issues were removed before packaging.  First, the
generic search no longer prunes a branch merely because the physical state
repeats: accumulated support is part of the parameterized state, and a cycle can
change which later actions count as births even if it restores the bits.  Second,
the ProveIt adapter suppresses only the exact inverse triangle, matching the
reviewed helper, rather than suppressing every immediately repeated crossing
triple.  The patch also imports the optional adapter lazily so the maintained
default path pays no new import cost.

The restricted recognition theorem is stated for an explicit deterministic
trace-selection and RI/RII policy.  Existence of some globally successful
sequence of bounded episodes does not imply that an arbitrary greedy episode
choice succeeds; recognizing that existential class would require outer
backtracking or a separate confluence theorem.
