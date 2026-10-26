# A 212-variable degree-ten consistency companion

This separate Round22 artifact has **212 unrestricted integer variables**,
**151 residuals**, **degree 10**, **55,820 collected monomials**, and coefficient
height **31,104**. It trades degree and coefficient size for a smaller
dimension; it does not replace the preferred quartic in the sibling `signed/` component.

`equations/equation.json` defines every literal residual. The equation is their
sum of squares equal to zero. `expanded_polynomial.json` gives every collected
coefficient of that single polynomial. No coefficient search is implicit.

`PROOF.md` proves the new q=1 modulo 3 cofinal restriction, its noncircular
composition with the even CRT anchor, and reciprocal pooling. Its inherited
proof sources and exact source builder are retained in the explicitly bound sibling signed/ component. ZFC proves that the new
polynomial has no integer zero iff Con(ZFC), without deciding either side.
There is no claimed global optimum or new end-to-end proof-assistant build.

## Offline exact verification (Python standard library)

```sh
python3 -B verify.py
python3 -B -O verify.py --deep
python3 -B build.py --check
python3 -B build.py --output /tmp/conzfc-reciprocal-fresh
```

The builder reconstructs the weighted source from the pinned original parent,
changes only the actual q+1 coordinate to 3z+2, performs 123 checked chart
operations and 2 common-Hessian projections, and merges the two private pools.
The independent checker imports neither producer, and checks every substituted
row, all inverse identities, pool privacy, the exact forward ideal identity,
all 55,820 collected coefficients, and deliberate corruption rejection.
Deep mode additionally replays the complete inherited signed and CRT packages.

`evaluate.py point.json` evaluates one supplied 212-integer tuple; it is not a
root search or consistency decision. `witness_maps.py project point.json` maps
a 215-coordinate protected pool-source point to 212 coordinates. `lift` restores
the old private pool quotients when its integral-domain conditions hold. The
proof guarantees these conditions on the new zero set; they are not asserted
for arbitrary integer tuples.

The literal array `[c,[i,j,...]]` means c times the listed coordinates, with
zero-based indexing and an empty list for a constant. The four removed pool
coordinates and rows, both actual bases, both moduli, and all restoration
formulas are listed in `equations/certificate.json`.

Original licenses and notices accompany copied ProveIt materials. The incoming
168 theorem is used only at its proved arithmetic interface; its obsolete
factorial bootstrap is not substituted for the new cofinal restriction proof.
No upstream repository was modified or published by this work.

## Explicit component dependency

Extract the ordinary archive parts into the same directory. This component
(`reciprocal212/`) requires the sibling `signed/` directory; no network fetch
or opaque file reconstruction is used. `SOURCE_BINDING.json` pins the exact
frozen signed manifest. Before importing any shared kernel, both entrypoints
verify that manifest hash and every declared file. The original signed files
are unchanged; the duplicate tree is intentionally omitted.
