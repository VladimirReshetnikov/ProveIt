# Radix49 finite completion

This self-contained package completes the pinned conditional shared-marker
radix49 construction. The architecture is prior ProveIt work; the new work
is the exact controller, whole coherent coefficients and verification.

Read `radix49/radix49_completion.md` for the theorem, constants, full
polynomial, proof composition, metrics and limitations.

Reproduce with standard-library Python:

```sh
python3 radix_probe.py
python3 materialize_radix49.py
python3 verify_radix49.py
```

The standalone checker also passes under `python3 -O`. The files under
`sources_pinned/` are unchanged exact primary sources; DEPENDENCIES.json
identifies their repository commit and hashes. `radix49/equation.tex` is a
complete one-page formula source; its PDF is produced in the enclosing
research report package. The polynomial domain is strictly positive integers.
