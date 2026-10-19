# Exact guarded comparator quotients: 28 and 24 states

The tables in this note inherit the complete prepared-frame contracts proved
in compare_biased_counter_PROOF.md and compare_biased_counter27_PROOF.md.
No interface, tape action, head movement, runtime or gap premise is changed.

## Gap at least two: 29 becomes 28

After the original two initialization folds, `init/0` and
`restore_counter/0` are both `1 R return_neq`. The initialization contract
proves that `init` reads only zero. Identify init with restore_counter,
retaining both restore_counter rows. The latter's one row still performs
its distinct, valid initialization role.

## Gap at least three: 27 becomes 24

Make the same identification, and also identify:

1. `failed_restore_left` with `restore_left`. Both read only zero and have
   the same zero row, `1 L done_ones`.
2. `restore_right` with `failed_find_first`. The former reads only zero.
   Their zero rows become identical after identification 1: both write one,
   move left, and enter the common restore_left state. Retain the latter's
   one row for its ordinary rightward source-search role.

The zero-only guards were established by the original marker induction.
Each retained state's rows on all of its own valid reads are unchanged up to
projection. Each removed state's rows agree with the retained state's rows
on every valid read after target projection. Thus these simultaneous
identifications satisfy the exact guarded quotient condition.

Induction on literal execution length proves that the new state is the
projection of the old state, and the tape and head are identical at each
step. In particular valid executions never acquire an unproved read, the
ports remain distinct, and termination and outputs are preserved.

The generator fold_comparator_entries.py asserts every required row equality
before emitting the tables. Its JSON results contain the removed/retained
states, valid-read domains, entry, ports and the complete quotient guard map.
The 28-state version has 27 operational states and one sink. The 24-state
version has 23 operational states and one sink. Neither count includes the
separate EQ/NEQ ports, which remain enclosing-machine obligations.

An additional 1,864 whole-tape fixtures check both functional outputs and
5,534,670 individual literal transition projections. The respective table
hashes are recorded in compare_biased_counter28_results.json and
compare_biased_counter24_results.json. These checks supplement the guard and
row-equality proof rather than substitute for its universal premise.
