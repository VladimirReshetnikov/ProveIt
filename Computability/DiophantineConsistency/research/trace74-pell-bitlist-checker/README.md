# Finite bit-list Pell residue evaluator

`Trace74PellBitlistChecker.run` processes a most-significant-first list of
bits, carrying the pair of Pell-coordinate residues modulo a positive
modulus. Each bit performs a verified doubling and optionally a
successor step; the state is reduced modulo `m` after each bit. The
evaluator takes `L` and `D` as inputs congruent modulo `m` to the Pell
base `b+2` and discriminant `delta b`. Therefore the evaluator need not
construct the potentially enormous base or discriminant.

`run_correct` proves, for every IΣ₁ model, that the final pair equals the
represented Pell-coordinate residues at `runIndex bits`, assuming those
two coefficient congruences. The bit list is a standard Lean list; the
represented index and arithmetic are model elements. The theorem makes
one transition per list element. Intermediate expressions and modular
arithmetic still have computational costs depending on input sizes.

This generic correctness theorem does not evaluate the concrete 32-bit
index, establish the required reduced coefficients, check the million-
bit gcd or Bézout certificate, or bind the external payload. Whether the
actual certificate can be checked within available Lean kernel resources
remains untested. No graph zero or iPRA endpoint is claimed.

## Check

The following command exited 0 without warnings on 2026-11-04 with Lean
4.32.0 and the previously built dependencies:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-pell-bitlist-checker Computability/DiophantineConsistency/research/trace74-pell-bitlist-checker/Trace74PellBitlistChecker.lean -o /tmp/Trace74PellBitlistChecker.olean
```

`step_correct` and `run_correct` report `[propext, Classical.choice,
Quot.sound]`. SHA-256 hashes:

```
e963b1968c87d43026092808932532364f51a8427c266039b47786dd8784ba92  Trace74PellBitlistChecker.lean
6872f8485465666a95dac3de9893c9b102913ae4454f704e1e077c286ea7ada9  Trace74PellBitlistChecker.olean
f0a8f423ed4b78497b71eb25903fc2581b7091a298cab6e53d266b68902d3a5a  Trace74PellModularBinary.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
