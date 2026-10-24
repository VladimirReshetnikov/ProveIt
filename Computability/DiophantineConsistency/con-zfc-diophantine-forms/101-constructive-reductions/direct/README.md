# Direct proof-calculus quartics

The final natural equation is `equations_v3/cap64/equation.json`; the final unrestricted-integer equation is `integer977/equation.json`. Each is a sum of squares of literal quadratic residuals and has a complete collected expansion beside it.

| Measure | Natural equation | Integer equation |
|---|---:|---:|
| Variables | 495 nonnegative | 977 unrestricted |
| Quadratic residuals | 391 | 533 |
| Exact degree | 4 | 4 |
| Collected monomials | 15,377 | 24,632 |
| Coefficient height | 83,867,632 | 83,869,250 |

`report_section.tex` gives the source projection, finite-tree/carrier argument, and domain recovery proof. `PROOF_PROJECTED.md` gives a longer source discussion. Immediate ordinary arithmetic and consistency calibration sources are under `provenance/`.

## Domain recovery

`DOMAIN_CERTIFICATE.json` specifies 170 nonnegative guards, 531 local sign implications, 29 common-frame conclusions, and 21 further local implications. `RAW_FRAME_INTERFACE.json` binds the raw frame and power identities to the contracted natural equation. The independent checker validates 1,243 arithmetic-gate bindings before using them to expand expressions.

The three-square identity `x=u^2+v^2+w(w+1)` represents precisely the nonnegative integers. Adjoining it at the 170 guarded coordinates gives 1,005 integer coordinates and 561 quadratic residuals. The 28 signed monic contractions in `integer977/elimination_certificate.json` give the final dimensions while retaining quadratic residuals. Their negative coefficients are legitimate after the integer lift; the same eliminations must not be imported into a natural-domain system without further sign arguments.

## Commands

The packet root driver runs all of these checks and byte comparisons in a temporary copy. Individual commands from this directory are:

```sh
python3 code/audit_projected.py --equations equations_v3 --output /tmp/direct_audit.json
python3 code/check_domain_certificate.py
python3 code/domain_negative_controls.py
python3 code/verify_integer.py
python3 code/build_projected.py --output /tmp/rebuilt_direct
python3 code/build_integer.py --output /tmp/rebuilt_integer
```

`code/build_domain_certificate.py` reconstructs the domain and raw-frame certificates from the supplied `domain_guard_seeds.json`; it writes the two certificate files in this component. The checker imports neither that producer nor its sign-discovery implementation. Run the producer in a copy if preserving the original files is important.

The universal source/refutation equivalence is proved mathematically and inherits the pinned ordinary C222 calibration. The finite checks do not establish consistency or replace those unbounded arguments. No new end-to-end kernel proof is claimed.
