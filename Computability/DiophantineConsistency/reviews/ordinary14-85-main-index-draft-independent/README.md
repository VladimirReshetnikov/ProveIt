# Independent source review: direct 85 main Pell index

The source classifies the same d produced by the 85 own-zero main balance.
The identity `3+4a+a²=(a+1)(a+3)` matches the Pell classification's delta,
and its argument and coordinate orders agree. The balance retains the old
`X*Y*q` carrier term. The source makes no assumption `q | X` and no claim
that m equals the rank.

The checker pins the source interfaces, replays the author and independent
main-balance receipts, and checks finite Pell recurrences including zero
index. This is source and finite review only; Lean elaboration, exact index,
provider compatibility, external-file binding and iPRA remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-main-index-draft-independent/check.py > /tmp/main-index85-independent.json
cmp /tmp/main-index85-independent.json reviews/ordinary14-85-main-index-draft-independent/result.json
```
