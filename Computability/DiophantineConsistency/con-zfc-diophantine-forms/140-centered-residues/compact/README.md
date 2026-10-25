# Four explicit ten-positive consistency polynomials

| JSON circuit | Operations | Exact degree |
|---|---:|---:|
| equation_XY_V2.json | 75 | 626 |
| equation_XY_bV.json | 76 | 464 |
| equation_q4_V2.json | 76 | 622 |
| equation_q4_bV.json | 77 | 460 |

`PROOF.md` states the full equations, proves the new admissible-denominator
criterion, supplies both unshifted sign arguments, and identifies the
retained ordinary native calibration. Each graph has precisely ten
strictly positive integer inputs. The four fixed coefficient ports are
literal integer constants, included as canonical little-endian bytes in
`coefficients/`, and do not count as unknowns.

The polynomial definitions share `XY` between both Pell bases. Their
carrier denominator is either that existing `XY` or the smaller-degree
`q^4`. The bounded first-index error is recovered modulo `q^4` before
the complete carrier denominator is recovered. No pairwise coprimality
of the latter with every other denominator is required.

Reproduce with Python 3, using only its standard library:

```
python3 build.py
python3 verify.py
python3 -O verify.py
python3 rebuild_coefficients.py
```

The first command regenerates all four full JSON graphs from the two
copied parent graphs. The second and third verify every gate through
exact free-polynomial cut identities, all leading homogeneous parts,
operation counts, liveness and literal coefficient hashes. The final
command independently reconstructs the complete four integers from the
published finite code and compares every byte; no network is required.
It does not search for a consistency witness or run the encoded machine.

`verification.json` contains complete leading-polynomial coefficient
vectors and per-register degrees, alongside the exact cut counts.
All graph changes are explicit: remove the private `T+alpha` addition;
share `XY` in `A-1=XY+Y` and `ell=(XY)(kY)`; change every occurrence of the
carrier denominator coherently.

The `q^4,V^2` point is retained as the simpler V-squared proof comparison,
although `XY,bV` has the same operation count and smaller degree. The
other three points trade cost and degree. No global optimum is claimed.

The ordinary unbounded proof composes with inherited source-61 Pell and
indexed native/refutation theorems. This component supplies actual fixed
polynomials and new arithmetic proofs; it does not supply a fresh
end-to-end Lean/Rocq proof or a consistency decision. See `PROOF.md`,
`proof_sources/`, and their retained notices/licenses.

Audit snapshot: ProveIt e0c98c629bf10d30b695884f6b1d2ab361bdf513.
Prepared with AI assistance for incorporation into ProveIt, 2026-10-25.
