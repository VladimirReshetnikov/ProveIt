# Native subtraction recursion equations

The source derives `∀x x−0=x`, `∀x y x−S(y)=pred(x−y)`, and `pred(0)=0` directly in native intuitionistic PRA from the actual primitive-recursive defining equations and native Leibniz equality. It assumes neither equality decidability nor classical transfer. Parent object and external production ancestry remain inherited; unrelated historical source-guard exclusions are recorded in the manifest. Run `python3 Computability/DiophantineConsistency/reviews/ipra-sub-arithmetic-replay/replay.py`.

Author `/tmp/ipra-induction-nozero-neyh6hgu` and independent peer
`/tmp/ipra-induction-nozero-2s1e85a6` both passed. Both source, object,
complete-log, and exit rows match. All three independent endpoint reports
contain exactly `propext`, `Classical.choice`, and `Quot.sound`; receipts and
logs are frozen here.
