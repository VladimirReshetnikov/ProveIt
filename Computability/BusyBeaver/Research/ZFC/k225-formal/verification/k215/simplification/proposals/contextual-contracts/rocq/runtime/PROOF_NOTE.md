# Why the guarded left-frame rule is sufficient

The symbolic left list records the finite portion of tape on that side of the
head. Appending a frame preserves all nearer cells. A symbolic step can inspect
that frame only when it reaches the end of the original left list. In the
current runtime, the only conflicting case is a left-oriented configuration
whose left list is empty: the unframed semantics may manufacture a blank,
whereas the framed semantics can inspect a real frame cell.

The Boolean guard excludes exactly that case. Case analysis on orientation,
head segment, transition lookup, direction, and oracle outcome proves the
single-step equation. The helper operations `peel_left` and `peel_right` commute
with append without additional hypotheses. The successful-step corollary
preserves the symbolic output and the step's progress flag.

The local runner checks the guard before every symbolic step. An induction on
the requested step count applies the single-step equation, proves the guard
also holds for the framed input, and transports the rest of the local replay.
Consequently each concrete successful unframed replay becomes a theorem for
all symbolic frames. This quantification is logical, not testing over a finite
collection of sampled prefixes.

For the machine-level reachability corollary, the same induction invokes the
existing `sstep_sound` at each framed state and composes its reflexive
transitive reachability conclusion. This deliberately does not turn a zero-step
or stuttering computation into a positive transition. A full control-node
simulation must still establish a positive progress contribution and compose
the uniform Home contract, then identify the concrete template associated with
each production node. The accompanying Lean work performs further parts of
that composition; they are not silently included in this Rocq theorem.

For each of the 35 entries, `checked` compares the actual guarded replay result
with its literal pre-Home endpoint. `all_checked` is proved by `vm_compute`
and `reflexivity`. `checked_ok` converts the Boolean equality to an exact
symbolic replay equation. The universal `template_replay` then follows from
`run_local_frame`. The supplied Python generator controls the shape of input
data; a wrong trace or endpoint cannot bypass these kernel-checked proofs.
