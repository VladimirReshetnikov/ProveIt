# Root-switch witness extraction: source-only model draft

This packet proposes to obtain the fact-level root-switch witnesses from a
signed first norm in an ordered IΣ₁ model. **No Lean source, tactic or
provider has been elaborated for this client.**

For natural `b,ell,k` with `b>0`, `k≥2`, and signed `P,z` satisfying

```
z = b*(ell+k-k*P)-P,
z² = b²*(1+ell*(ell+k)),
```

the proposed `P_positive` first rules out `P≤0` by comparing the first root
with `b*(ell+k)`. `root_data` then proposes to construct in the same model:
a positive natural `Pn` representing P; a natural signed-root magnitude and
quotient tau with `tau>ell` and `z=±b*tau`; and a positive natural t with
`Pn=b*t`. The source calls `ReducedNormSigned.natural_magnitude_square`,
`ArithmeticAdaptiveQuotients2011.scaled_quotient`, and
`Trace75IntegralTransport.natural_dvd_of_signed`. None of those source matches
is a compiled-provider audit. The root-switch lemma then proposes a positive
replacement preserving the first-root square. This fact-level statement has
no K0 upper-bound assumption and does not claim original r was positive.

A graph client must still prove the exact signed first-root/norm premises at
`r=0`, `b>0`, the shift and preservation of the other three residuals, and
then establish the appropriate existential zero map. Compact K/port binding,
gamma, parent bridge, provider provenance and iPRA endpoint are separate.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue-root-switch-extraction-draft/check.py | cmp - research/ordinary13-residue-root-switch-extraction-draft/receipt.json
```

The bounded checker pins source bytes and sanity-checks the norm comparison
and divisibility algebra on finite signed cases. It does not run Lean, stage
artifacts or verify reasoning in nonstandard models.
