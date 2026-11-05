# Candidate-index modular Pell evaluator

`Trace74CandidatePellChecker.candidate_run_at_index` composes the checked
power-period reduction, sparse coefficient reduction, and bit-list Pell
evaluator. Under explicit internal-model assumptions

```
q = power 2 590069
q² = m+1,    m>0
b+1 = q³*(power 2 3056651345 + 1),
```

it proves that the bit-list evaluator's pair is exactly the pair of
represented Pell-coordinate residues modulo `m` at index `3056651345`.
The evaluator takes sparse coefficients built from `q` and
`x=power 2 93925`, rather than the enormous original Pell base. Lean
also checks that the explicitly listed 32 bits encode the required
index in every IΣ₁ model.

This is a correctness theorem for a symbolic evaluator. It does not
evaluate the candidate residue, check the finite gcd/Bézout certificate,
establish the parameter assumptions for a fixed graph, or prove a graph
zero or iPRA endpoint. Feasibility of the million-bit kernel calculation
is still untested.

## Check

The following command exited 0 without warnings on 2026-11-04 with Lean
4.32.0 and the previously built dependencies:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-candidate-pell-checker Computability/DiophantineConsistency/research/trace74-candidate-pell-checker/Trace74CandidatePellChecker.lean -o /tmp/Trace74CandidatePellChecker.olean
```

All three results report `[propext, Classical.choice, Quot.sound]`.
SHA-256 hashes:

```
9cbf1d167427190d98bc6bba34f1e155a91d36615d244dfd4ae143716b1a81bf  Trace74CandidatePellChecker.lean
0a0dabce4365623b3c593cb5739b696d5b8c650196179b03aa2fd3ceb7dcee49  Trace74CandidatePellChecker.olean
267fe25684d61dff426ed5f6557427808629c0b5a6a6230448574aac6ebb1d26  Trace74PowerPeriodResidue.olean
6872f8485465666a95dac3de9893c9b102913ae4454f704e1e077c286ea7ada9  Trace74PellBitlistChecker.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
