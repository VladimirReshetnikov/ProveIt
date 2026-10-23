# Sixteen unrestricted integers

The complete formula and ordinary proof are in `../sections/signed16.tex` and the
compiled report. All sixteen coordinates range over Z. `generated/signed16.json`
is a division-free circuit with exactly 1,617 binary operations and exact degree
813056·5^32+10016 = 18930435180664062500000010016.

`data/INSTANCE.json` binds the whole fixed instance. The parent is the original
unshifted-transport package-30 quartic; its historical inline coefficient metadata
is superseded by the explicit active instance. `data/constants.json` contains the
weighted quartic coefficients and current index metadata. Historical reference
data under `data/reference_instance` is not active.

The base is b=kappa*t², where kappa=2^99415332078933715820316769856. This is an
explicit fixed integer, not a variable exponent or an existential parameter.
The product enforcing nonzero witnesses deliberately omits t; t≠0 follows from
the recovered positive g and strict margin.

Run:

```sh
python3 build_signed16.py
python3 verify_signed16.py
python3 ../quartic31/audit_signed16_independent.py --signed-dir .
```

The last command independently transcribes the formula and imports neither the
builder nor its circuit utility. The top-level driver supplies an absolute path
so all commands work from arbitrary directories.

The source of the digit-evaluation identities is ProveIt package 27. The inherited
Jones interface and signed reductions are from packages 29/30. See `../NOTICE.md`.
