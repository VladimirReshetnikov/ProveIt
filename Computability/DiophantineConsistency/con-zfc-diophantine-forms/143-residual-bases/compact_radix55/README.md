# Alternate whole radix55 specialization

This standalone component selects **radix55 only**, binding all four ports
together. The sibling `compact/` remains unchanged with its radix67 default.
These are different specialized integer polynomials with identical free-port
arithmetic DAGs, ten-positive domain, and operation/degree profiles.

The useful points are **77/626, 78/464, 79/460, 80/384**.
`q4_v2.json` (78/622) and `partial_v2.json` (79/518) are dominated controls.
The exact literal files are `xy_v2.json`, `xy_bv.json`, `q4_v2.json`,
`q4_bv.json`, `partial_v2.json`, and `partial_bv.json`.

The accepted upstream radix55 encoding reduces total raw fixed-port storage
from295,388 to242,484 bytes (52,904 fewer); its largest port is486,696 bits.
That encoding/storage improvement is credited reuse, not a new encoding
claim. Our new bridge is `PROOF.md`; the unchanged arithmetic argument is
`REDUCTION_PROOF.md`, retained with its original radix67 historical labels.
All actual current payloads and circuit bindings are radix55, never mixed.

Reproduce with Python3.10+ standard library from this directory:

    python3 -B build.py --check
    python3 -B verify.py --output /tmp/compact55-check.json
    python3 -B -O verify.py --output /tmp/compact55-checkO.json
    python3 -B rebuild_coefficients.py
    python3 -B verify_binding.py

The recipe reconstructs every integer from the same complete436-character
seed and943 indexed tiles, with the correct new55-bit padding, and checks
both accepted controller units using the whole actual new K0. The checker
verifies every circuit row through independent polynomial cuts, complete
leading forms, all inputs/ports/gates live, and48 algebraic negative controls.
Normal/optimized receipts agree byte-for-byte. Rebuild reads frozen JSON
only; no inherited producer, native program or proof-assistant runs.
`verify_binding.py` additionally checks the full accepted55 binding, four
raw-byte records, coherent metadata, scalar box, and exact comparison with
the frozen67 free-port templates (included as historical provenance).

The whole accepted55 wrapping controller constructs new canonical words
and actual R=3 mod4, with q³|Y and nonnegative transport quotient. Our
soundness reconstructs fresh positive accepted55 P66 witnesses before
applying its native/refutation theorem. No private67 witness or specialized
polynomial identity is transferred. No consistency decision, new formal
proof object, global optimum or printed-PDF size gain is claimed.
`radix55_section.tex` is an includable article supplement; original full
constant/seed specification remains in provenance and the complete exact
recipe code. Every new source origin is mapped in `PROVENANCE.json`.
