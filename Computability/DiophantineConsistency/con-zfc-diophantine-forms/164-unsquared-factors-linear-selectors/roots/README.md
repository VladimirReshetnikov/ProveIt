# Thirteen unrestricted integers: degree152, 119 live operations

The complete fixed polynomial is `integer13_degree152_ops119.json`; its independent
proof is `PROOF.md`, with report-ready TeX in `report_section.tex`.

New: exact partial shear of the incoming13/152/126 equation saves seven gates;
all integer zero sets correspond by n_old=n_new-k. The new endpoint is13/152/119.
It trades two gates for four degrees against the retained13/156/117. No12-variable
breakthrough, consistency proof, global optimum or new kernel theorem is claimed.

Reproduce (Python3 plus SymPy for the independent algebra audit):

```
python3 -B build.py --check
python3 -B check.py
python3 -B -O check.py
python3 -B reconstruct_coefficients.py
python3 -B -O reconstruct_coefficients.py
```

The retained recipe was inspected before execution. No network, external tool,
blank-machine execution or Diophantine zero search is performed. The package
contains all six numeral payloads, including the already shifted MF, and their
finite reconstruction data. See `CLOSURE_MAP.md` for proof boundaries.
