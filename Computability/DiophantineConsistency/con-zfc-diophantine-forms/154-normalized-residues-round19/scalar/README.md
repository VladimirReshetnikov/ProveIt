# Exact restricted degree-300 minimum

**New result:** degree 300 is the exact minimum among all constant nonzero
weights and integer centers in the retained eleven-integer free-scale frame.

**Unchanged attaining equation:** `free_whole_center11_c300.json`, with eleven
unrestricted integer variables, degree 300 and 148 binary arithmetic gates.
This graph is byte-identical to the Round 18 delivery, not a new endpoint.

Read `PROOF.md`, `SCALAR_FIXED_FRAME_DEGREE_FLOOR.md`, and `BASELINE_PROOF.md`.
All six actual coefficient payloads, their finite reconstruction recipe,
licenses and the inherited ordinary proof closure are included. The claim is
ZFC-provable equivalence of unsolvability with Con(ZFC), not a proof of either.
The minimum theorem concerns only the precisely stated fixed frame.

## Reproduce (Python standard library only)

```
python build.py
python check.py
python -O check.py
python audit_mutations.py
python -O audit_mutations.py
python check_scalar_top_forms.py --graph free_whole_center11_c300.json --output SCALAR_TOP_FORMS_NORMAL.json
python -O check_scalar_top_forms.py --graph free_whole_center11_c300.json --output SCALAR_TOP_FORMS_OPTIMIZED.json
python replay.py
```

`RELEASE_WHITELIST.json` lists the exact release closure; `MANIFEST_SHA256.json`
authenticates it. Checks never rely on removed Python `assert` statements.
The independent floor checker binds 23 complete leading forms. The baseline
checker additionally certifies the exact degree-300 center cancellation and
all actual coefficient numerals. Both alternative operation labels at every
arithmetic gate are deliberately rejected.
