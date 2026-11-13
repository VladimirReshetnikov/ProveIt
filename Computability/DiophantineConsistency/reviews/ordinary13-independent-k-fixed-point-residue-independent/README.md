# Independent compact fixed-point residue calculation

This packet independently reconstructs the provisional fixed point for the generalized fixed compact slice using only modular arithmetic and pinned source recipes. It does not materialize beta, K′, the fixed masks, R, or any Pell coordinate as a huge integer. The full witness and graph zero require the separate arithmetic audit described below.

Set `N=67*8807=590069`, `q=2^N`, `beta=q−1`, `rho=2^67`, and `K0=rho^42*beta+K′`. The checker parses all 943 pinned selector rows and the 41 pinned slot positions; it evaluates the finite reflected kernel sum, including the extra `rho^42` in K′, modulo N. It separately evaluates the low and high masks from their pinned little-endian base-rho digit recipes, and uses the once-shifted fourth port `MF=beta+high`.

For the proposed coordinates `J=1`, `F=K′+2^r`, `alpha=beta−F`, the actual graph rank has

```text
G=alpha+(q−F)*beta=q²−1−q*F,
R=G*(q²−1)+MC+q*MF.
```

Consequently its residue modulo N is `A−B*2^r`, where

```text
A=((q²−1−q*K′)*(q²−1)+MC+q*MF) mod N,
B=q*(q²−1) mod N.
```

The independently computed residues are `q=273473`, `beta=273472`, `K′=551654`, `MC=428453`, `high=73733`, `MF=347205`, `A=365222`, and `B=460162` modulo N. For `r=439547`, `2^r mod N=55048` and `(A−B*55048) mod N=439547`. Thus the stated rank formula satisfies `R≡r (mod N)`; no primality assumption on N is used.

The separate bound `K′<q/8`, together with `r<N`, gives `F<5q/8` and positive `alpha=beta−F`. The literal `C=q−F−alpha` is 1. Provided the rank lower bound gives `R≥N`, choosing `w=2^(R−N)` makes `X=q*w=2^R`; the fixed point yields `X≡2^r (mod beta)`. With `h=(X−2^r)/beta+rho^42`, the literal first carrier becomes `Bfirst=beta*h`. These deductions use exact integer divisibility and symbolic exponents; the accompanying checker verifies the modular facts, not an all-model formalization or a full Pell witness.

A useful generalized growth estimate for a subsequent witness audit is: with `Y=q³`, `M=X*q⁶`, `a=X*q³+q³`, `R=2n−1`, q≥24, n≥14 and X≥q, the cited Pell recurrence bounds give

```text
k ≤ 2*(6*X*q⁶)^(n−1),
c ≥ (X*q³)^(2n−2).
```

As `Y+1≤2q³`, the strict comparison `c>(Y+1)k` follows from `X^(n−1)>4*q³*6^(n−1)` and the earlier bound `q^(n−4)>4*6^(n−1)`. This extension, rank lower bound, positive first-root and main/strong/auxiliary witness identities need a full independent review against the finalized construction. No Lean, build, staging, model theorem or parent-child zero correspondence is claimed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-independent-k-fixed-point-residue-independent/check.py | cmp - reviews/ordinary13-independent-k-fixed-point-residue-independent/receipt.json
```
