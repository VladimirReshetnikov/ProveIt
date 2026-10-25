# Centered norm charts

New literal unrestricted-integer equations:

| File | Variables | Exact degree | Operations |
|---|---:|---:|---:|
| integer14_degree88_ops110.json | 14 | 88 | 110 |
| integer13_degree156_ops117.json | 13 | 156 | 117 |

Read PROOF.md for complete universal maps and edge cases; report_section.tex is
editable report content. Both equations are polynomial triangular shears of
frozen Round18 charts, not new numeral encodings. The 14/88/110 chart dominates
the previous14/94/110; the14/86/112 point remains a lower-degree tradeoff.

Run with Python3 and SymPy:

    python -B build.py
    python -B check.py
    python -B -O check.py
    python -B reconstruct_coefficients.py
    python -B -O reconstruct_coefficients.py

The checker never imports the builder. Both modes reject all227 separate gate
mutations. Reconstruction compares every byte of all six complete coefficients.
The inherited/ tree is frozen and authenticated by INHERITED_PINS.json. No
network, blank-machine simulation, consistency search or publication is used.
This is an ordinary arithmetic reduction, not a consistency proof, global
minimum or new end-to-end kernel certificate.
