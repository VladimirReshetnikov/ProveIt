# Delayed power signs: direct quartic in 780 integers

This component supplies a literal integer polynomial `P780` whose lack of
integer zeros is equivalent in ZFC to Con(ZFC), through the explicitly
pinned direct C222 calibration inherited from ProveIt. It improves the
888-integer direct quartic in `ConZFC_407_888_Quartics_2026-10-24.zip`.

| Property | Value |
|---|---:|
| Domain of every final unknown | Unrestricted integers |
| Unknowns | 780 |
| Quadratic residuals | 434 |
| Exact polynomial degree | 4 |
| Collected monomials | 9,628 |
| Maximum absolute collected coefficient | 2,445,790,974,704 |
| Independent source sign guards | 131 |
| Signed monic eliminations | 303 |

The equation is the sum of squares of all residuals in
`equations/equation.json`. Its entire expansion is in
`equations/expanded_polynomial.json`. Each term `[c,[i,j,...]]` means the
integer coefficient `c` times the listed variables, with repeated indices
for powers and an empty index list for a constant. Indices start at zero.
No additional sign restrictions or hidden parameters accompany the final
equation.

The parent used 167 sign guards. The new proof recovers 23 private power
quotient signs after proving the exponentiation graphs correct. It also
derives nine modulus signs, a discriminant sign, and three signs from
stronger elementary positive-factor inferences. Removing 36 guards saves
108 integer unknowns. The new result has the same degree and coefficient
height as that parent, with 528 fewer monomials. It is an improvement in
this specific direct family, with no absolute minimality claim.

## Verification

Python 3.10 or later and its standard library suffice:

```sh
python3 check.py
python3 -O check.py
python3 verify.py
python3 -O verify.py
python3 build.py --output /path/to/a/new/directory
```

`check.py` is independent of the producer and its elimination module. It
authenticates immutable source bytes, reconstructs the raw interface,
checks the ordered sign proof and every Pell/power premise, replays the
integer inverse substitutions, and recomputes the complete collected
polynomial. Explicit exceptions perform its checks; Python optimization
does not disable them. `verify.py` additionally rebuilds every equation
file byte for byte in an isolated directory and requires six deliberate
corruptions to be rejected.

The universal mathematical proof is `PROOF.md`; the separate adversarial
review is `INDEPENDENT_REVIEW.md`. The mathematical and computational
roles are distinct: finite checks certify this exact instance, while the
proof uses the stated Pell classification, Pell-index theorem,
three-square theorem, and inherited C222/refutation calibration. This
component does not supply a new Lean or object-language ZFC proof object,
and does not decide consistency.

## Files

| Path | Purpose |
|---|---|
| `PROOF.md` | Complete new mathematical sign and projection argument |
| `INDEPENDENT_REVIEW.md` | Separate proof review and independent checker run |
| `build.py`, `parameters.json` | Deterministic producer and frozen guard choice |
| `check.py` | Independently implemented finite audit |
| `verify.py` | Byte reproduction and rejection controls |
| `equations/equation.json` | All 780 variables and 434 quadratic residuals |
| `equations/expanded_polynomial.json` | Complete 9,628-term single polynomial |
| `equations/domain_certificate.json` | Ordered sign inferences, with semantic stages |
| `equations/projection.json` | Exact signed inverse-substitution certificate |
| `equations/signed_source.json` | 690 source coordinates plus 393 guard witnesses |
| `equations/METRICS.json` | Exact producer metrics, independently recomputed |
| `certificates/` | Receipts and complete guard-change inventory |
| `SOURCE_PINS.json` | Immutable parent and extracted-member identities |
| `upstream/` | Exact parent archive, retained inputs and source proofs |
| `vendor/terminal_elimination.py` | Unmodified inherited producer helper |

The source archive is pinned at ProveIt commit
`ec80841c07e91be8956ce6ed4af9a9c0b782d3d9`; its SHA-256 is
`59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59`.
The expanded output's SHA-256 is
`45a5f432474ccbefa050b8c4d95059c8587f0697789c0f1209df2cdd3b558a8e`.

The accompanying article contains a typeset version of this proof.
Original attribution and license terms are preserved under `upstream/`;
see `NOTICE.md` and `LICENSE` for this component.
