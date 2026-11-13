# Independent source review: direct 85 q divides 3X

The own-zero exact-index witness supplies `2n=R+1`, the first quotient and
the old carrier balance. With `Y=q³*slot7`, the proposed W rewrites the
quotient as `k=R+1+U*W`. Cancelling the positive natural factor qY from the
carrier balance is valid because `U=Y*q²`; the retained `H*X*Y*q` term becomes
`H*X`. The identity `H=3+qD` and the stated modulo calculation yield
`q | 3X`. Neither `q | X` nor an 84 or FreeJ zero is assumed.

The checker pins the exact-index interface, replays author and independent
dependency receipts, and tests finite old-carrier balances including q=3,
X=1. These finite examples are not claimed to satisfy Pell norms or be graph
zeros. This is source review only: Lean elaboration, power recovery, Mersenne
cancellation, providers, external file binding and iPRA remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-divides-3x-draft-independent/check.py > /tmp/divides3x85-independent.json
cmp /tmp/divides3x85-independent.json reviews/ordinary14-85-divides-3x-draft-independent/result.json
```
