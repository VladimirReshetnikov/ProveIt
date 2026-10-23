# Signed 15-variable Con(ZFC) polynomial

The equation is the division-free DAG `generated/signed15.json`.
Its only variable leaves are its 15 listed unrestricted integer inputs;
fixed leaves are determined by `COEFFICIENT_BINDING.json` and the preserved
original T4 coefficient recipe. The proof is `SIGNED15_16_PROOF.md`.

Run from this directory, with Python 3 standard library only (an absolute script path also works from any other directory):

```sh
python3 build_signed15.py
python3 check_new_lemmas.py
```

The first script authenticates source files, reconstructs the DAG, checks exact
degree/operation counts, compares named body nodes against the original literal
Jones body modulo three primes using the actual T4 coefficient recipe, and checks
the norm/intersective/interval arithmetic. The second supplies finite negative-
and zero-sign Pell orbit cases and checks the signed weight and coprimality bounds.
These finite tests supplement the written proofs.

Every newly adapted result is an ordinary proof. The native compiler, Jones
arithmetic and K215 calibration remain explicit inherited dependencies. This
package does not include an end-to-end Lean or Rocq build.
