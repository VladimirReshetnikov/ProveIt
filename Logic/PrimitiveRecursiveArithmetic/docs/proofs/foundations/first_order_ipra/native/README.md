# A native proof of transport under a binder

The original certificate `equality_transport.json` derives the sequent
`x = y, y = z ⊢ H(x) = H(z)` in the raw scalar presentation of ConciseIPRA.
With `I(c,b;u.t)` denoting iteration on counter `c` with seed `b` and step body `t`,
the term is

```text
H(a) = I(a, S(a); u. I(u, a; v. S(v))).
```

The two premises are the entire open context. The certificate first obtains
`y = x` by transport along `x = y` with the constant template `x`, then
obtains `x = z` by transport along `y = z` with the identity template.
For `H(x) = H(x)`, let `b = H(x)`. The raw iterator axiom gives
`I(0,b;u.u) = b`. Using this equation for both premises of an identity-template
transport yields `b = b`. The final transport uses template `H`. The occurrence
of the free slot in the inner iterator seed crosses the outer iterator binder.
Thus the seed's de Bruijn index is 1 for the left endpoint and 3 for the right.

## Replay

The upstream standalone Python checker is maintained in Vladimir Reshetnikov's
ProveIt repository. The certificate and these instructions are the only files
included here. Run the following from this directory with Python 3.10 or later.

```sh
revision=a5eb061b91d220c0e3a7532bdca6a957cc1ebac0
checker_path=Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Artifacts/full_normalization/goal_checker/code/raw_checker.py
curl -fsSL "https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/$revision/$checker_path" -o raw_checker.py
echo '6af3134ce7c917d54b77ce552038ac23bac359b2b77ef78b181ddde291848556  raw_checker.py' | sha256sum -c -
python3 raw_checker.py < equality_transport.json
```

The expected output is `ACCEPT` with exit status zero. The checked source has
Git blob ID `54420de88335c456325f583e8522083798afb300`. The certificate
SHA-256 is `40cda3cbb6a0000e7e174125a73368fc73ceeae797b70a045af8166a8af32642`.
Removing the premise `y = z` or replacing the right-hand inner seed index 3
by 2 gives exit status one in separate negative controls.

This checks one concrete sequent in the native scalar object calculus.
The general substitution theorem is treated separately in the manuscript and Lean files.

[Upstream checker at the tested revision](https://github.com/VladimirReshetnikov/ProveIt/blob/a5eb061b91d220c0e3a7532bdca6a957cc1ebac0/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Artifacts/full_normalization/goal_checker/code/raw_checker.py)
