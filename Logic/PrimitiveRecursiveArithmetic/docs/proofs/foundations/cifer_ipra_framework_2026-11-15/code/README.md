# Exact finite reference implementation

`cifer.py` implements:

- dependency-normal residual extraction for a topological proof graph;
- capped inflationary demand closure;
- backward finite viability and least viable paths;
- exact stable observations and rational diameters;
- finite-list height maxima; and
- exact rational bisection for `y^3 + y = x`.

Run:

```bash
python3 -m unittest -v test_cifer.py
python3 demo.py
```

Only the Python standard library is used. These programs are executable diagnostics and examples, not an iPRA proof checker.
