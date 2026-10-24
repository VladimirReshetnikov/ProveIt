# Twelve positive variables at degree 110

The equation is `adaptive_centered12.json`. All twelve inputs are strictly
positive integers; the four named constant inputs are fixed numerals bound
by `native/COEFFICIENT_BINDING.json`, with the graph's `K0` mapped to native
port `K` and `MF` to native port `MF_source`. There are no unbound program
parameters. Intermediate registers are polynomial abbreviations.

The complete new mathematical argument is in `PROOF.md`. It combines the
first carrier of ProveIt package 61 with the adaptive main carrier of package
65 and a new centered auxiliary norm. The result has exact degree 110 and
102 live binary arithmetic operations, compared with the inspected package
61 point at degree 118 and 104 operations, on the same positive domain.

The centered norm's denominator cannot vanish at a zero. Its canonical
positive witness is justified by an explicit Pell growth inequality. The
adaptive carrier restores the index before deriving q divides X. The written
proof separates these new reductions from the inherited native compiler,
Pell sequence results, and syntactic refutation calibration. This is not a
new end-to-end Lean/Rocq certificate or a global minimum claim.

With Python 3 and its standard library:

```
python3 check.py
python3 -O check.py
```

This verifies exact sparse identities and degree certificates, the 102-gate
literal graph, byte-exact graph regeneration, liveness, and all authentic
fixed coefficient bytes. The 60 scalar comparisons are diagnostics only;
the polynomial identities and weighted leading forms are checked exactly.

To regenerate the compact tuple from the literal transitions:

```
python3 native/build_coefficients.py
python3 check.py
```

The upstream builder is retained byte for byte. Its finite checks do not
prove the unbounded compiler theorem; `native/PROOF.md` gives the inherited
mathematical adapter. The native and source notices/licenses are retained.
`PROVENANCE.json` records the pinned source identities. The new top-level
builder reuses the retained package61 DAG helper from its original builder.
