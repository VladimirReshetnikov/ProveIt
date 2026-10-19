# E667: combining the newest equational reductions

E667 deletes the now-derived truth equation from the complete E692 packet.
It combines the incoming E692 structural sharing and optimized closure with
the separately incoming E688 truth derivation. The optimized closure is
checked afresh with `d` an independent Boolean value; its zero cofactor is
still the first relation value `r`. The unchanged head/NAND-class equations
supply a concrete ground instance with `r = top`.

Consequently E667 and E692 have exactly the same models and equational
consequences. The existing E692 calibration therefore transfers. This is
ordinary mathematics formalizable in ZFC, not a new proof-assistant
endpoint or a counted Turing-machine interpreter.

## Reproduce

```sh
python3 -O build_e667.py
```

The script requires only Python's standard library. It pins and reconstructs
the included E692 input, checks the exact optimized closure and unchanged
structural rows, removes only the six-node truth equation, roundtrips the
new packet, rejects all 667 strict prefixes and three malformed controls,
checks 512 Boolean cofactor assignments, and writes the full artifacts to
`generated/`. Its checks remain enabled under `python -O`.

| Item | Count |
|---|---:|
| Operation symbols | 9 |
| Variable slots | 4 |
| Equations | 7 |
| Equation term nodes, both sides | 150 |
| Header bits | 43 |
| Equation bits, including markers | 608 |
| Ground endpoint bits | 16 |
| Complete logical packet bits | **667** |
| Packed bytes | 84 |
| Transport padding bits | 5 |

The bit-character SHA-256, excluding the final newline, is
`1075854399e1c3428e1c178b51bac47e428b8ef010b59e0312a3c06d409e55b8`.
The ground equation to search for is `N(d,d) = d`.

`e667_section.tex` gives every equation, the all-algebra proof, provenance,
and precise scope. `ATTRIBUTION.txt` identifies both incoming contributions.
The ground-substitution recipe is not a fully expanded contextual rewrite
trace from Sh1. A binary rewrite engine, complete enumeration, data writer,
and initialization cost still need to be supplied before using this bit
length in a Busy Beaver state-count comparison.
