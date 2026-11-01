# Native predecessor reconstruction

The source proves `∀x (x = 0 ∨ x = S(pred x))` in native intuitionistic PRA using the actual primitive-recursive predecessor equations, direct native add-one, Leibniz equality and native open induction. It does not assume general equality decidability or any consistency bridge. Parent and external production ancestry remain inherited; unrelated historical source-guard exclusions remain recorded in the manifest. Run `python3 Computability/DiophantineConsistency/reviews/ipra-pred-reconstruct-replay/replay.py`.

Author `/tmp/ipra-induction-nozero-khvwvxld` and independent peer
`/tmp/ipra-induction-nozero-h_u7ke2y` both passed. Their two source, object,
complete-log, and exit rows match; the independent endpoint report contains
exactly `propext`, `Classical.choice`, and `Quot.sound`. Receipts and logs for
both runs are frozen here.
