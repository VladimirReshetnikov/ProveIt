# A clean member of every native clause pair

`NativeTemporalSupport54.lean` proves that partial temporal bit shifts do
not create positions outside the periodically repeated assignment support,
after accounting for their whole-digit rotation. The proof covers every
bit phase0–88. Ordinary digits are Boolean; the only possible radix carry
comes from the two-bit dummy507 and lands at508, which is already in the
literal support. No zero bit phase is assumed.

`clause_pair_one_zero` proves that any two targets separated by606 have a
zero temporal digit at one member, for every bit phase and every whole-
digit rotation. Two supported positions cannot differ by606 modulo4831:
the coarse literal support is at most583, or equals1203 or1807. This
argument also covers a single-cell cyclic word.

Consequently the two native clause targets2409 and3015 include a clean
member in each cell before global phase alignment. Both targets have the
same local coefficient sum, so their paired mask tests can recover the
actual local clause-mask zero. Global bit/cell alignment and machine
interpretation remain separate obligations.

The main and all four public-API axiom checks pass. The only dependencies
reported are `propext`, `Classical.choice`, and `Quot.sound`. No accepted
local clause or native-correctness hypothesis is introduced.

`NativeLocalMask54.source_local_masks` now implements that composition.
From a positive literal source zero and the explicit symbolic coefficient
Interface/K binding, it constructs the assignment and proves the actual
`localCell &&& clauseMask = 0` in every cell. Its `addition_residue` lemma
handles the cyclic cell indices; `localContribution_eq_cell` identifies the
two local sums. No temporal-phase or accepted-clause assumption is present.
The new main and all three public-API axiom checks pass with the same
standard three axioms. Global phase alignment and machine interpretation
remain open despite this unconditional local-clause extraction.
