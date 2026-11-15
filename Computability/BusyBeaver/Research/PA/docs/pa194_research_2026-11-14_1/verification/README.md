# Independent checks of the new work

`independent_variant_review.py` independently parses the frozen literal
parent, selector and child tables; checks the four selector cases, twelve
shortcut cases, and the child predecessor conditions; validates each dense
conjugacy and printed digest; then rebuilds all package outputs in a
fresh temporary directory and compares every generated file byte-for-byte.

```sh
python3 -B verification/independent_variant_review.py
```

This needs only Python 3.10+ and the standard library. Its receipt is
`variant_review.json`. It checks finite premises of the written relative
proof and package reproduction. It does not independently reconstruct the
inherited PA-refutation compiler or supply a new proof-assistant theorem.

`startup_review/` contains the source review and positive controls for the
new adaptive bootstrap search. The baseline frame was independently
replayed using a scalar Python simulator. Deliberately damaged baseline
tables test nested repairs and the future-edit-aware ray cut; they are
checker controls, not proposed consistency machines. The recorded pair
cross-check uses all 58,485 distinct-row pairs at native start 74.

To regenerate that evidence in a fresh output directory, with a C++17
compiler available:

```sh
python3 -B verification/startup_review/replay.py --output /tmp/pa194-startup-review
```

The default replay includes the pair cross-check; `--skip-pairs` omits it.
The frozen review logs have machine-dependent elapsed times. The standalone
review explains which results are bounded and why unresolved leaves are
not treated as divergence proofs.
