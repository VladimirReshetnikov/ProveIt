# Native predecessor of subtraction-zero implication

The source proves `∀u v ((u − S v = 0) → pred(u − v) = 0)` in native intuitionistic PRA. It obtains a classical candidate-PRA proof from the actual all-model subtraction recursion theorem, transfers that proof by GG, and removes double negation using native zero decidability. It does not assume general equality decidability. Parent object and external production ancestry remain inherited; unrelated historical source-guard exclusions are recorded in the manifest. Run `python3 Computability/DiophantineConsistency/reviews/ipra-subpred-zero-native-replay/replay.py`.

Author `/tmp/ipra-induction-nozero-mtrwi8zg` and independent peer
`/tmp/ipra-induction-nozero-6qvb2j7w` both passed. All three source, object,
complete-log, and exit rows match. The independent endpoint report contains
exactly `propext`, `Classical.choice`, and `Quot.sound`; both receipts and
logs are frozen here.
