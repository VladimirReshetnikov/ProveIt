# Represented power period modulo a square minus one

`Trace74PowerPeriodResidue.power_period` proves in every IΣ₁ model that
if `q=power a e`, `q²=m+1`, and `m>0`, then for all internal `k,j`:

```
power a ((2*e)*k+j) ≡ power a j (mod m).
```

The proof uses represented-power identities and Σ₁ induction; it does
not evaluate the represented powers or assume `k` is standard.
`candidate_power_period` checks the concrete small-numeral index
decomposition in Lean and specializes the result to

```
power 2 3056651345 ≡ power 2 93925 (mod m),
```

under the explicit conditions `q=power 2 590069`, `q²=m+1`, and `m>0`.
This supplies the remaining power-congruence premise in the
[sparse coefficient reduction](../trace74-pell-coefficient-reduction/README.md).
It does not evaluate those residues or prove a concrete gcd certificate.

## Check

The following command exited 0 without warnings on 2026-11-04 with Lean
4.32.0 and the previously built dependencies:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-power-period-residue Computability/DiophantineConsistency/research/trace74-power-period-residue/Trace74PowerPeriodResidue.lean -o /tmp/Trace74PowerPeriodResidue.olean
```

All three printed results use `[propext, Classical.choice, Quot.sound]`.
SHA-256:

```
ad0c42ea3c38bcd064dc9e66ed65a8f815b6e9577a5ca2cc904fc36e1b130991  Trace74PowerPeriodResidue.lean
267fe25684d61dff426ed5f6557427808629c0b5a6a6230448574aac6ebb1d26  Trace74PowerPeriodResidue.olean
478d822f10dcbf0ec065695e8f683043ff23cfb644f9e0d2318f55178e19e714  Trace74PellCoefficientReduction.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
