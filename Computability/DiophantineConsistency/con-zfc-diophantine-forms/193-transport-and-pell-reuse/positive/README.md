# Folded weighted transport and a degree 190 consistency equation

The principal literal polynomial has ten strictly positive integer variables,
exact degree 190 and 118 live binary arithmetic operations. The companion has
the same domain and fixed constants, exact degree 202 and 99 operations.

At the explicitly retained native/K215/refutation calibration, the new ordinary
proof establishes in ZFC that absence of a positive zero is equivalent to
syntactic Con(ZFC). It assumes neither consistency nor inconsistency. This is
not a new end-to-end Lean/Rocq certificate or a global simplicity minimum.

## Core files

- `whole190.json`: every live gate of the principal polynomial and fixed ports.
- `quotient202.json`: the lower-operation companion.
- `PROOF.md`: full new arguments, carrier bootstrap, positive witness maps,
  exact degrees, dependency boundaries, and attribution.
- `BASELINE_COMPARISON.md`: bounded comparison with the placed and incoming work.
- `coefficient_recipe.tex`, `retained_coefficient_recipe.py`, and `coefficients/`:
  complete finite definitions and actual bytes for all four fixed integers.
- `inherited172/`: the unchanged selected historical source closure, including
  its proof texts, calibration boundary, source equations, recipes and licenses.
- `source178/`: retained whole-product center argument and algebra.
- `SOURCE_LEDGER.json`: immutable repository/archive source identities.

The symbolic input order is `J,F,alpha,i,T,w,s,n,eta,zeta`. Named circuit values
are abbreviations, not additional variables. The fixed coefficient tuple has
295,388 raw bytes; its largest port has 592,884 bits. Operations count fixed scalar
products and squares but treat constants as available leaves, so this count is
not a bit-complexity estimate.

## Finite replay

Python 3.10 or later and the standard library suffice. Run from this directory:

```sh
python3 -B verify.py
python3 -B -O verify.py
```

The main verifier is read-only unless an explicit `--receipt PATH` is supplied.
It authenticates retained sources, reconstructs all four integers, checks the
literal graph identities and exact degrees, proves actual input dependence
through exact modular derivatives, rejects targeted corruptions, and reconstructs
both equation files byte for byte. The principal algebra checker imports no
producer. The companion checker separately derives the quotient identity.
The mathematical source proofs and finite checks play different roles; these
programs neither search for zeros nor decide consistency.

The unfolded whole-product center has 84 free-ring terms and its norm defect
has 594. Folding the transport adds one center term; the resulting 85-term center
has a 679-term defect. Both defects have the same degree 94 leading part under
the stated formal weights, yielding actual total degree 190. These different
counts refer to different explicitly identified polynomials.

## Evaluate an explicitly supplied tuple

```sh
python3 -B evaluate.py --variables
python3 -B evaluate.py --values example_tuple.json --modulus 1000000007
python3 -B evaluate.py --equation 202 --values example_tuple.json --modulus 1000000007
```

Omit `--modulus` for exact integer evaluation. Add `--value`
only when the full integer value is wanted; the normal exact output gives its
zero test, sign, bit length and hash. The example is merely a reproducible
evaluation fixture. A modular zero, if any, would not be an integer zero.

Historical receipts and script claims inside the retained source directory
refer to their original releases. The new replay authenticates those bytes
but does not relabel a historical formal verification as a new one.
The top-level `PARENT_PROOF.md` is an unchanged convenience copy; its historical
relative source paths resolve from `inherited172/`, where the original proof
and selected closure keep their delivered layout.
