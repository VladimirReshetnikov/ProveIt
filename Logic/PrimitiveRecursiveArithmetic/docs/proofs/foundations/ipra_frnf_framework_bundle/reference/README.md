# Exact reference implementation

`frnf.py` implements the finite algorithms used by the paper with exact
`fractions.Fraction` arithmetic and no third-party dependencies.  It is an
executable semantic model, **not** an iPRA proof checker.

Run:

```sh
python3 -m unittest -v test_frnf.py
```

The object-theory proof obligations are stated separately in `lean/` and in the
paper.  In particular, passing these tests does not justify the label
“kernel-checked iPRA theorem.”
