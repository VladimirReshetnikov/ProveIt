PA194: a 194-state binary Turing machine for Con(PA)
=================================================

Definitive table: pa194.tm
Start: 0. Working states: 0 through 193. Halt: 194.
Tape: one two-way infinite binary tape, initially all zero.
Initial head position: 0. Every working state has exactly two transitions.
The distinct halting control is excluded from the 194-state count.

Literal table SHA-256:
9087d70fc0e1878c38ceff928e6e7e0999c86b6efed00a5ec353821c00641c87

Reproduction
------------
From the complete package root, using Python 3 and its standard library:

    python3 -B pa194/build_verify.py

The script locates all inputs relative to itself, so it also works when invoked
by an absolute path from another working directory. No network, optimizer,
solver, Lean installation, or Rocq installation is needed. Do not use Python -O.

--quick omits only the two complete universal symbolic runtime checks.
--export regenerates derived certificates; the literal tables are reconstructed
and compared exactly on every run. The reference compiler, symbolic register
routines, and their pinned original sources are in ../reference/pa195_conpa/.

Construction and evidence
-------------------------
The physical allocation has 134 inherited controls and 68 new AX readers,
then removes eight controls by one simultaneous quotient: 134 + 68 - 8 = 194.
All 194 advertised working states are reachable in the transition graph.

The emitted word is the previously supplied separate190 axiom emitter. It is
obtained from PA195's 191-token word by deleting token 184 (zero-based), a cons.
The separate diagonal-vacuity formula Gamma(A)=A -> forall A A remains on the
stack; the accumulator contains the previous guarded gate neg(V -> Q).
The whole stack, accumulator, parameter reads, guard, and cleanup are checked
as identities in a free term algebra. The command pushes ten entries.

The source has 3,673 primitive occurrences and 4,780 primitive branch cases.
Every operation and every ordinal successor agrees with the archived separate196
source. Two independent source CFG resolvers agree. Both the unfolded 202-state and
folded 194-state tables pass all 4,780 symbolic whole-frame contracts.

The quotient certificate contains all 23 incoming-history rows and all 32 local
cases. They use only the current cell and its immediate left neighbor, so the
checks hold for every outside-tape extension. The literal durations are twelve
cases of length 1, sixteen of length 3, three of length 5, and one of length 7.
Every remaining raw row commutes with the state projection in one step.
The complete blank startup reaches the standard clean source frame in exactly
58,154 literal transitions; the complete tape and head, not a prefix, are checked.

Proof scope
-----------
The accompanying article gives the ordinary mathematical proof that PA proves
Nonhalt(PA194, blank) iff Con(PA). The executable certificates establish finite
literal-program facts and universal symbolic frame contracts used in that proof.
They retain the inherited register-box lemmas. They are not a newly compiled
end-to-end Lean or Rocq theorem. No global minimality claim is made.

Files
-----
pa194.tm                    Dense literal table, authoritative for the machine.
pa194.native.tm             Equivalent table using inherited native state names.
unfolded202.native.tm       Deterministically rebuilt pre-quotient table.
labels.json                 Dense-to-native bijection, including the halt control.
grammar.json                New AX association and shared-subtree grammar.
folds.json                  Eight paired aliases and replacement actions.
source.json                 Every primitive path, operation, and ordinal successor.
source_binding.json         Exact comparison to the archived separate196 source.
emitter_certificate.json    Whole-stack and accumulator free-algebra checks.
local_fold_certificate.json All incoming-history premises and complete local traces.
startup_certificate.json    Complete standard clean blank-start configuration.
input_hashes.json           Pins every imported construction/checking input.
validation.json             Full reconstruction and runtime receipt.
verification.log            Output from a fresh full portable build.
