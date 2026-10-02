# Binary Carry Structure in Iterated Lacunary Series

This archive contains an unrefereed research article proving a complete
modulo-four classification for OEIS A168362 and a stronger theorem for every
coefficient of every iterate of

```text
F(x) = x + x^2 + x^4 + x^8 + ... .
```

## Main result

For every iterate `m`, the coefficient of `x^N` in `F^m(x)` is divisible by
4 whenever the binary expansion of `N` has at least three 1-bits.  The
remaining exponents have exact bitwise formulas.  On the diagonal A168362,
this proves the OEIS mod-4 observation, gives all future exceptions, and
proves a logarithmic counting law for them.

## Verify

From this directory:

```sh
python code/verify_a168362.py --limit 256
```

The script uses only the Python standard library.  It independently performs
dense truncated polynomial composition modulo 4, verifies the whole-array
formula through a 256-by-256 square, checks the 21 published initial terms by
exact integer composition, and regenerates the data files.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

## Status

AI-assisted, unrefereed, and not formalized in Lean.  The proof is symbolic;
the computation is an independent regression check, not an assumption.
Independent review is recommended before using the proposed OEIS update.
