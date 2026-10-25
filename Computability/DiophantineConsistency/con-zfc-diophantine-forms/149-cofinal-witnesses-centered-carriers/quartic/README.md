# Common-remainder quartics in 246 and 247 integer variables

This standalone component combines the 252-coordinate normalized-remainder
source with the independently proved odd-square radix choice, then applies
exact affine projections and frozen coordinate/row transformations.

| Endpoint | Variables | Quadratic rows | Quartic monomials | Height |
|---|---:|---:|---:|---:|
| integer246 | 246 | 178 | 12,541 | 12,227 |
| integer247_sparse | 247 | 179 | 4,352 | 23,316 |
| integer247_balanced | 247 | 179 | 4,432 | 17,235 |
| integer247_lowheight | 247 | 179 | 5,648 | 6,144 |

All variables independently range over **Z**, and every polynomial has exact
degree four. The extra variable in the 247-coordinate profiles preserves a
useful affine gate and avoids dense substitution. None of these profiles is
claimed globally optimal. Main sources retain the proven horizon t>=16.

The ordinary result is that ZFC proves integer unsolvability of each fixed
polynomial equivalent to Con(ZFC), using the identified inherited arithmetic
and C222/ZF/ZFC-refutation calibration. This is not a consistency decision,
and no new end-to-end Lean build is claimed.

## Exact objects and proofs

* `ODD_SQUARE_COMPOSITION_PROOF.md`: acyclic arithmetic proof of the new
  common-remainder/odd-square composition, with both directions.
* `PROOF.md`: universal row/coordinate/projection identities and the stronger
  affine-polynomial-multiplier obstruction.
* Each endpoint directory: all residuals in JSON, text and TeX; all collected
  quartic coefficients; metrics; coordinate names; complete source-restoration
  map.
* `certificates/`: finite ordered transformations. Optimizer/search code is not
  needed and search optimality is not a premise.
* `source_closure/common_remainders/`: complete portable inherited 252-source
  replay and ordinary proof closure; other `source_closure` files preserve
  credited prior arguments and an independent composition review.
* `SOURCE_PROVENANCE.json`: repository/archive/source pins and attribution.

## Offline replay

Python 3 standard library only. From this directory:

```
python verify_all.py --output VERIFICATION_NORMAL.json
python -O verify_all.py --output VERIFICATION_OPTIMIZED.json
```

Both modes reconstruct the inherited source, authenticate its retained files,
check the literal odd-square edit, independently verify every endpoint and
universal source pullback, reject deliberate corruptions, compare fresh
builds byte-for-byte, round-trip the printed text and TeX, and prove the
43,966-column Macaulay matrix has full rank modulo 1,000,003. A duplicated
residual must lose rank. The rank conclusion rules out all nonzero
*affine-polynomial* combinations of the 178 residuals that would be affine;
it is not a lower bound against arbitrary Diophantine constructions.

For endpoint-only construction into a fresh directory:

```
python build.py --output /tmp/conzfc-quartic-rebuild
```

`build_source.py --check` checks the frozen 252-to-250 edit. `check_source.py`
is independent of that producer. No command uses the network or searches for
a zero. The finite audits do not replace the unbounded ordinary arithmetic
proofs.

## Optional lower-horizon companion

`horizon4/PROOF.md` independently closes the t>=4 arithmetic argument,
including all 144 possible exceptional fixed-point cases at t=4 and t=5.
It explicitly replaces, rather than reuses, the old false-at-t4 label
inequality. The four optional quartics have the same variables, rows,
support and height as the main profiles; their coefficient L1 norm is
lower by 288. Their exact universal difference is
`P4-P16 = 24*t - 24*horizon_root^2 - 240`.

```
python horizon4/factorial_small_horizons.py
python horizon4/companion.py --output /tmp/conzfc-horizon4
```

The optional helper reconstructs the complete quartics and independently
checks this three-coefficient delta. Main recommended artifacts retain t>=16.
