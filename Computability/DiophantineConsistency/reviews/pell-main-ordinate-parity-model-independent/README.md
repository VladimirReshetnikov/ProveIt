# Independent source review: main Pell ordinate parity

The proposed arbitrary-model statement is `ycoord n b % 2 = n % 2`. For a model-even index `n=2t`, the pinned `ArithmeticPellPeriodicity.double_y` gives `ycoord n b=2*xcoord t b*ycoord t b`, so both remainders vanish. For a model-odd index `n=2t+1`, the second component of `ZRowsPellEvenChebyshev.sign_index b t` has exactly the required direction modulo `2*(b+3)`. Because 2 divides that modulus, the pinned `ArithmeticPellResidueClasses.mod_reduce` transfers both sides to modulus 2. The source calls and positive-modulus/divisibility arguments match these two cases.

The odd-index source theorem itself uses `ISigma1.sigma1_succ_induction` with a definability side condition; the represented recurrence source supplies a Sigma-1 function instance for `ycoord`. Thus the intended source interface quantifies over internal model indices, rather than only externally enumerated standard naturals. This review pins those source declarations and checks finite recurrence controls, but does not replay that induction or authenticate compiled providers, and cannot claim Lean accepted the parity client.

An eta-zero contradiction still requires independently deriving the actual graph's even k, `c=Y*k`, main Pell index `c=ycoord R a`, and exact relation `2n=R+1` in the same model. The generalized index, graph/unit extraction, source/provider ancestry and internal iPRA endpoint remain separate. The author's lexical receipt reproduces; no Lean was run.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/pell-main-ordinate-parity-model-independent/check.py | cmp - reviews/pell-main-ordinate-parity-model-independent/result.json
python3 -I -S -B research/pell-main-ordinate-parity-model-draft/check.py | cmp - research/pell-main-ordinate-parity-model-draft/result.json
```
