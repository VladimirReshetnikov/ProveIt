# Reproduce the frozen compact coefficient tuple

Use ordinary Python 3 standard-library modules only. No installation or
execution of an upstream program is needed. Preserve the packet's directory
structure, with `compiler/` and `audit/` as siblings.

The authoritative binding is `COMPACT_COEFFICIENT_BINDING.json`. In particular
the arithmetic source coefficient named MF is `MF_source.bin`, NOT the
native field mask. The four compressed files alone contain all four actual
integers; they are not generators or symbolic stand-ins.

From the packet root, inflate the shipped bytes without evaluating code:

    python - <<'PY'
    from pathlib import Path
    import gzip, hashlib, json
    p = Path('compiler')
    binding = json.loads((p / 'COMPACT_COEFFICIENT_BINDING.json').read_text())
    for row in binding['files']:
        raw_path = p / row['path']
        zipped = Path(str(raw_path) + '.gz').read_bytes()
        assert hashlib.sha256(zipped).hexdigest() == row['gzip_sha256']
        raw = gzip.decompress(zipped)
        assert len(raw) == row['bytes']
        assert hashlib.sha256(raw).hexdigest() == row['sha256']
        raw_path.write_bytes(raw)
    print('All four actual coefficient files inflated and verified.')
    PY

To rebuild the same tuple from its literal 430-action inert transition table:

    python -B compiler/build_wang943.py
    python -B compiler/build_wang943_compact.py
    python -B compiler/materialize_wang943_compact.py

The first command generates the shared language and fallback layout metadata;
it does not generate the large fallback binary integers. The second command
selects the recommended compact geometry; the third emits exactly the four
compact coefficient files and deterministic gzip copies. All outputs remain
in the packet directory.

For independent semantic, geometric and byte-for-byte checks:

    python -B compiler/check_wang_helices.py
    python -B audit/audit_wang943_independent.py
    python -B audit/audit_wang943_compact_independent.py

The first audit reconstructs all 943 tuples without importing the builder;
the last reconstructs the compact sparse coefficients independently. They
perform finite checks only; the universal argument is in the two compiler
proof notes and `audit/WANG943_INDEPENDENT_AUDIT.md`. The imported arithmetic
and exact-machine theorems remain dependencies, as documented there.

Frozen output sizes:

- beta: 9,765,625 bits, 1,220,704 bytes.
- K: 13,201,251 bits, 1,650,157 bytes.
- MC: 9,765,625 bits, 1,220,704 bytes.
- MF_source: 9,765,626 bits, 1,220,704 bytes.
- Total: 5,312,269 bytes, or 20,260 compressed bytes.

All binary files are unsigned, little-endian, minimal-byte integers without
headers. In Python, interpret a raw file with `int.from_bytes(raw, 'little')`.
