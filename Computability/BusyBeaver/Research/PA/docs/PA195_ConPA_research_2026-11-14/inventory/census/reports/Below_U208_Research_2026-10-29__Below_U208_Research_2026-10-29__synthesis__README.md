# Below-208 research: conditional selectors and head-offset aliases

No 207-state machine was obtained. These are bounded negative search receipts,
not a lower bound and not proof that any rejected table changes the blank run.
The inputs are the two 208-state rooted graph classes in ProveIt commit
`ef5a23e04b0285e321ceec5f4b329223cee0ab57`. Conditional Context supplies the
first two snapshots; History supplies the isomorphic pair used with its native
labels by the neutral-rewrite search. Notices are retained under `licenses/`.

## Terminal searches

1. Two conditional-history pair folds share one newly introduced selector
   (two deletions plus one new state). Unlike the earlier one-bit predecessor
   template, guards may depend on the scanned symbol and seven preceding
   transitions. 111 and103 disjoint pair combinations: no accepted table.
2. Broader driver macros, and either left or right neighboring tags, at history
   depth8. ClassA:226 left and6 right combinations; classB:205 left and6 right.
   No common driver survives the bounded exact-macro preselection.
3. A deleted noninitial state q is represented by an existing state r at
   relative head offset ±2. All external entrances to q must have the same
   direction, and are reversed. 179 eligible q and37,053 (q,r) choices per
   class; no candidate passes the necessary finite40-step screen.
4. The same offset family composed with one of351/357 separately supplied
   context-neutral row rewrites:999,875 and1,001,952 action trials. Another
   12,001,891 and12,222,115 choices are excluded by first divergence on a
   failing concrete context. No candidate survives the finite screen.
5. Initial-state q=0 extension, including its essential runtime role and
   self-loop:480 nine-cell inductive blank-run windows per class;7,794 and7,798
   candidates after first-divergence filtering, no survivor. Initial translation
   on the all-zero tape is legitimate; simply removing an initializer is not.

A finite screen rejects a *bounded sufficient macro contract*. Its test tape
satisfies an overapproximating entry context; it need not occur on the actual
blank run. Failure is neither a semantic counterexample to blank equivalence
nor evidence that a longer macro cannot work. All returned candidates would
need the subsequent exact branching checker and full independent validation;
there were none.

The neutral input files contain only the351/357 selected rewrite rows and the
hash of each full proof receipt, not the bulky independent certificates. The
negative combined search does not rely on their correctness: it considers
these explicit finite lists as a search-family definition. No new assertion
that those rows are neutral is certified by this bundle.

## Reproduction

`python3 -B replay.py` checks all sealed bytes and reruns the two selector
families, offset-only aliases, and initial-state extension in a disposable copy.
`python3 -B replay.py --full` also repeats the roughly two-million-trial
neutral-offset family. Python3 standard library only; no network. The original
upstream program histories and supplied tables are read, never executed as
shell commands. This is an ordinary finite computation, not a proof-assistant
certificate or a new consistency calibration.

The frozen main receipts count only terminal runs. Two early implementations
of the neutral-offset runner were interrupted for performance improvements;
those partial logs are not counted as searches completed.
