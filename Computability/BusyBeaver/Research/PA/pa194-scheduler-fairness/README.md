# PA194 scheduler fairness and finite words

`PA194EncodedWord.word_halts_scheduler` first proves the explicit-pointer
bridge: if a finite command word halts from a store, then the scheduler halts
when started with that word's encoded positive continuation pointer, any
candidate counter, and that store.

`PA194Fairness.reach_fresh` proves that, unless it has already halted, the
actual scheduler eventually reaches every later candidate with an empty
continuation. It uses the strict decrease of positive continuation codes and
increments the candidate only at a fresh start. Consequently,
`PA194Fairness.derivation_halts_initial` proves that any derivation of code 1
in the displayed separate-diagonal numerical calculus makes the scheduler
halt from its actual initial state `(N,L,T,W,D,H) = (2,0,0,0,0,0)`. These
results print `[propext, Classical.choice, Quot.sound]` for the fairness and
initial-state theorems, and `[propext, Quot.sound]` for the explicit-word
bridge.

The result concerns standard finite computations and the specific numerical
calculus of `../pa194-derivation-compiler`. It does not translate PA
refutations into that calculus, establish the reverse soundness direction, or
prove any equivalence inside PRA/iPRA. The exact source/clock bridge is
separate, and the source retains the pinned Python grammar-translation
boundary documented in `../pa194-source-tree`.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-scheduler-fairness/check.sh
```

The script rebuilds the source, scheduler, selectors, and derivation compiler
in private tmpfs, then checks the encoded-word and fairness theorems. The
complete fresh run has passed, as has an independent replay of the fairness
modules against the retained clean compiler objects.
