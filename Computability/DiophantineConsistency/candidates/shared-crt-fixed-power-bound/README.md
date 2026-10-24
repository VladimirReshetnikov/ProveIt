# Fixed common bound for the direct positive-power graphs

The literal quartics in `affine/` and `retained/` use `W=n+k` in every
positive-power certificate. They have respectively **3,443** and
**5,960 natural variables**, exact degree four. [PROOF.md](PROOF.md)
proves both directions, including fresh completeness witnesses at the
fixed bound. The frozen prime-lift parent and its 8,619-integer companion
are preserved.

From the repository root:

```sh
python3 -B Computability/DiophantineConsistency/tools/build_shared_crt_fixed_power_bound.py --check
python3 -B Computability/DiophantineConsistency/candidates/shared-crt-fixed-power-bound/check.py
python3 -O -B Computability/DiophantineConsistency/tools/build_shared_crt_fixed_power_bound.py --check
python3 -O -B Computability/DiophantineConsistency/candidates/shared-crt-fixed-power-bound/check.py
```

The direct C222/refutation calibration remains the same named ordinary
argument as the parent. No native tuple or new Lean/internal-ZFC proof
is claimed. Lean formalization remains paused.
