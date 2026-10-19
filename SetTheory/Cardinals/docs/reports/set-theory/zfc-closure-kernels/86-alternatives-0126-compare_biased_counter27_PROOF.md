# 27-state comparator with a three-cell minimum gap

This variant has exactly the interface and output of the 29-state comparator,
except that the blank gap between the loaded counter and the header must have
length at least THREE, rather than two. It has 26 operational states and one
invariant-failure sink, with separate EQ and NEQ ports. The stronger gap
premise is an enclosing caller's obligation and is not free initialization.

Use the complete proof in compare_biased_counter_PROOF.md for initialization,
the main invariant, productive cycles, source completion, scans and the two
forced-symbol folds. Only the counter-exhaustion terminal path changes.

If a<b, the attempted (a+1)st source advance detects counter exhaustion at
c-1. `restore_exhausted` restores the sentinel at c and `dummy_counter_one`
writes one at c+1. This dummy counter has length two. Its remaining gap has
length original_gap+a-1, which is at least two because original_gap>=3.
The new writer reads zero: c+1 has either just been cleared by an earlier
successful decrement or belonged to the original gap when a=0.

The failure-mode right shuttle therefore remains valid. It locates the
shifted two-zero source marker, restores both marked source cells, and now
enters the existing `done_ones` left shuttle. The dummy counter's length two
makes `done_check` read one. It consequently clears the dummy counter,
restores its single sentinel, and returns NEQ on c. This is correct because
a<b was already established before the dummy was written. All temporarily
written gap cells are cleared, and the source/header/arena are unchanged.

No failure-mode left shuttle is needed. Remove its three states and add the
one `dummy_counter_one` state: 29-3+1=27. All other steps and valid-read guards
are inherited unchanged. `dummy_counter_one` has the universal guard zero.
The result JSON includes the complete conservative valid-read guard map.

The separate generator and table do not alter the 29-state gap>=2 component.
A gap2 input with a=0 may leave only one zero between the dummy counter and
header, violating the shuttle lemma, so this stronger premise must never be
silently dropped. Loading a with the copier requires original allocation
at least a+3 if this 27-state comparator will follow it.

The generator checks 5,072 exhaustive-small and seeded-random whole-tape
fixtures with gaps at least three, all four seven-cell header modes, all
comparison outcomes and arbitrary exterior bits. Maximum observed runtime
is 80,480 steps. These tests supplement the unbounded argument; no complete
verifier, free dispatcher, blank bootstrap or proof-assistant theorem is
claimed.
