# Invariant-restricted physical reduction research

This auxiliary research uses the frozen PA194QN machine from the three incoming
archives at ProveIt commit `317b07268681b44ff352d173a162e2a8c241b2fe`.
It does not claim a smaller consistency machine.

## New invariant certificates

The source begins at instruction 25 with register vector
`[2,0,0,0,0,0,0,0,0]`. A monotone finite abstract interpretation gives
3,236 exact-zero and 5,924 positive-register facts across its 3,654 source sites.
The source has no decrement whose branch is decided by this nonrelational
zero/positive domain. Nevertheless, other known-zero registers can constrain
the local tape during an instruction.

`modular_invariant.py` strengthens the domain to exact zero and the four
positive residue classes modulo four. It produces 750 nontrivial congruence
facts, including 283 facts that a register is a nonnegative multiple of four.
It checks the resulting invariant as a post-fixed point independently of the
work-list iteration. Ordinary induction on source steps proves its soundness.
These are executable mathematical certificates, not a proof-assistant theorem.

The second invariant is that the spare registers all have value one. The exact
blank seed has 26 such spares; a source increment appends another value-one
spare and every other primitive instruction preserves the spare list. The
tail after separating the first spare therefore always contains at least 25
value-one blocks. This permits periodic tape-window analysis instead of
arbitrary spare-list bits.

The pairwise register-coalescing screen certifies no alias under the sufficient
condition that every access to either register occurs with the other zero.
This is failure of that sufficient criterion, not a proof that all semantic
register reuse is impossible. The closest pair, registers 0 and 8, has twelve
source sites where that condition is not established.

## Reproduce the modular certificate

From this directory, with Python 3.10 or later and assertions enabled:

```sh
python3 -B replay.py
python3 modular_invariant.py inputs/instructions.json mod4_replayed.json
python3 register_alias.py inputs/instructions.json
```

The first command verifies the frozen invariant and repeats all six local
screens from the recorded windows. Add `--derive-contexts` to regenerate both
complete symbolic context sets as well, which takes several minutes.

The complete frozen modular invariant is `mod4_verified.json` and its summary
is `mod4_receipt.json`.

## Local physical search

`collect_zero_contexts.py` restricts the independent affine tape checker by the
proved-zero primary registers. `collect_modular_contexts.py` additionally uses
positive and modulo-four facts and the value-one spare invariant. It preserves
conservative uncertainty about other values. The latter covers periodic list
interiors through first-three-block and last-three-block cases, which also
cover all middle phases because the tail has at least 25 blocks.

Both collectors retain radius-five windows, cover the interiors of accelerated
unary sweeps, and include all 58,154 startup transitions. Their outputs are
search inputs, not newly certified transition tables.

```sh
python3 collect_zero_contexts.py zero_contexts
python3 collect_modular_contexts.py modular_contexts
c++ -O3 -std=c++17 action_merge_all.cpp -o action_merge_all
c++ -O3 -std=c++17 edge_bypass.cpp -o edge_bypass
./action_merge_all inputs/machine.native.tm 5 300 zero_contexts/patterns_k5.txt
./edge_bypass inputs/machine.native.tm 5 300 zero_contexts/patterns_k5.txt
```

The first C++ screen identifies two controls by selecting a common first action
for each read symbol, followed by at most 300 steps of the existing machine.
The second removes a non-self-looping control by independently rewriting each
incoming transition. The programs retain their avoidance conditions. Empty
output means no candidate in that finite screen, not a lower bound on all
possible PA-consistency machines.

An additional new screen, `marker_folds_all.cpp`, permits changing predecessor
writes to encode which of two controls was entered. It then replaces the pair
by one surviving control. The local detour must restore the original entire
window and reproduce the endpoint of two original transitions. It excludes
self-loops and edges between the selected pair, and avoids other modified rows
inside the detour. On the zero-restricted windows it checked 14,401 independent
pairs and 22,148,352 candidate first-action trials, with no candidate. These
trial counts include different marked predecessor conventions; they do not
count distinct complete machines.

```sh
c++ -O3 -std=c++17 marker_folds_all.cpp -o marker_folds_all
./marker_folds_all inputs/machine.native.tm zero_contexts/patterns_k5.txt
```

Both complete derivations and all three searches finished. The zero-only
pass produced 29,479 windows. The modular and periodic-spare pass produced
24,388 windows, a strict subset with 5,091 windows removed and none added.
Both cover all 4,755 primitive outcomes and all 194 controls. Every local
screen returned zero candidates. The exact scopes, counts, elapsed times,
input hashes, and empty outputs are in `zero_contexts/` and
`modular_contexts/`. The result is a sharper unsuccessful bounded search,
not a state-count lower bound.

## Attribution

The input machine/source are the supplied PA194QN artifacts. The affine tape
engine, legacy entry labels, local screens, and notices are retained from the
supplied PA194N6 research package. The invariant analyses, specialization,
periodic-spare collector, and current search runs are new to this report.
See `PROVENANCE.json` and `reference/` for the pinned origins and licenses.
