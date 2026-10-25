# Eleven-integer center compression

New literal endpoints: **298/147** and **300/145** (degree / live binary gates),
each over eleven unrestricted integers with the unchanged six actual numerals.
The incoming full-modulus construction already attained298/150; this component
saves three gates. Against the previous300/148 delivery,298/147 improves both
metrics. The300/145 companion saves two additional gates at two extra degrees.

Read `PROOF.md` for complete formulas, exact integer shears, the critical
rebased native handoff, exact degrees and calibration boundary.
`REBASED_FIXED_FRAME_DEGREE_FLOOR.md` proves the matching restricted298 minimum.
The historical `SCALAR_FIXED_FRAME_DEGREE_FLOOR.md` remains true for the OLD
q^8 frame; no contradiction or global optimum is claimed.

The entire equation is its named JSON DAG plus the six bound numerical leaves
in `coefficients/`. No port or intermediate register is another unknown.
`inherited_rebased/` contains the complete unchanged incoming298/150 source
and other historical input artifacts; those are not additional new endpoints.
`BASELINE_PROOF.md` and `source/` retain the old300/148 calibration closure.
All source licenses and notices are preserved.

ZFC proves absence of integer zeros equivalent to syntactic Con(ZFC), through
the explicitly retained ordinary source theorems. Neither side is proved true;
no new end-to-end proof-assistant certificate is claimed.

## Portable checks (Python standard library)

```sh
python -B build.py --check
python -B check.py --receipt CHECK.json
python -B -O check.py --receipt CHECK_OPTIMIZED.json
python -B audit_mutations.py
python -B -O audit_mutations.py
python -B check_scalar_top_forms.py --graph integer11_degree298_ops147.json --output TOP_FORMS_298.json
python -B check_scalar_top_forms.py --graph integer11_degree300_ops145.json --output TOP_FORMS_300.json
python -B replay.py
```

`check.py` imports no producer and verifies every arithmetic gate, complete
center remainders, attained actual coefficients, source pins, and full coefficient
reconstruction. The separate top-form checker imports neither builder nor checker.
Both alternative operation labels at all292 gates are rejected (584 mutations).
`MANIFEST_SHA256.json` authenticates the release closure.

For packaging, two optional historical rendered PDFs and two copies of a repository-wide
aggregate delivery index are omitted; all proof
Markdown/TeX, actual coefficients and licenses remain. `CLOSURE_MAP.md` identifies
the active root manifests and distinguishes nested historical provenance
indexes that still mention those four optional files. No mathematical or graph change is
part of this size reduction.
