# Independent source review: direct 85 q⁴ congruence

The proposed 85 own-zero balance retains the old `X*Y*q` carrier term.
Using `Y=q³*slot7`, `U=q⁵*slot7` and `H=3+4Y(X+1)`, its rearranged natural
balance matches the argument order of `q4_rank_from_balance`. The conclusion
is q⁴-divisibility of the magnitude of `R+1−k`; no q-divisibility of X or
coprimality with three is assumed.

The checker pins the source interfaces, replays author and independent
dependency receipts, and independently tests finite nonnegative old-carrier
balances including both difference signs, q not dividing X and a sharp q=3
case. These balances are not asserted to be graph zeros. This is source and
finite review only; Lean elaboration, exact calibration, provider ancestry,
external file binding and iPRA remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-q4-rank-draft-independent/check.py > /tmp/q4-rank85-independent.json
cmp /tmp/q4-rank85-independent.json reviews/ordinary14-85-q4-rank-draft-independent/result.json
```
