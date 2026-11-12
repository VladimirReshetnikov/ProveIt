# Final mathematical manuscript review

Reviewed `output/ipra_checked_presentation_2026-11-12/ipra_checked_presentation.tex`
through the attributed-appendix boundary, and native delivery AUDIT sections
4--6 against the actual 849-byte source.

## Verdict

No blocking mathematical error found. The main text states its limitation
clearly: implementation improvement of the inherited theory, not a new
arithmetic basis and not a proof of a global minimum. Its fully typed native
comparison and compact-byte comparison are kept separate.

## Points checked

- The displayed native case and progress rules agree with the inherited
  Choice-DI calculus, and progress is restricted to literal equations.
- The selector/gate logical macros agree with the foundational source. The
  universal macro includes A(0) separately, and the conjunction uses parity
  instances 1 and 2; neither silently assumes full induction.
- Case distinction and equation induction follow by an unused witness,
  paired elimination and closure use.
- The ordinary realization includes an explicit separation/falsity bridge.
- The primitive-recursion compiler carries both its numerical index and
  accumulated value in a verified pair. Its index identity follows by
  literal-equation induction. No universal evaluator is smuggled into the
  object language.
- Numerical round trips are proved operation by operation using recurrence
  uniqueness, with identity numerical domain and actual equality.
- The paired formula composite is proved in both directions using native
  logical macros; the stated formula-composite induction is appropriate.
- The rejected-Q-progress proposition is valid for adding that rule to the
  native calculus. Gating makes every native formula equivalent to a Q-rooted
  formula, so that extra rule yields contextual induction on all formulas.
- The implementation argument preserves the distinct zero and empty-list
  flags for native atomic progress and cases.
- The compact modulo refinement is properly described semantically rather
  than as all-certificate trace inclusion.
- The known-zero-instance supply lemma is used instead of incorrectly
  claiming every fresh-parameter computation supply is a uniform theorem.

## Small precision edits recommended

1. Explicitly state that the two variables bound by D are distinct.
2. In the rejected-rule proposition, spell out the structural extension
   G_v(Q_y B) = Q_y G_v(B), with bound variables fresh for the gate control.

These clarify existing conventions; they do not change a result.

## Native AUDIT sections 4--6

The delayed-dispatch proof is valid: a truthy m makes the generated hypothesis
m*3 and prevents the branch that mutates a; a falsy m cannot match a nonempty
expected elimination major. The caller's k is local and opener calls consume
no proof instructions. Consequently reordering goal selection past major
verification and hypothesis construction preserves successful executions.
The eager tuple selection has the previously audited successful-trace
inclusion and canonical completeness. No further mathematical edits needed.

This is a written independent review, not proof-assistant verification of the
new Python source or a rerun of the entire inherited Lean development.
