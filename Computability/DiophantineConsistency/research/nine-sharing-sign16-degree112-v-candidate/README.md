# Sign16 degree-112 conditional signed-V candidate

This external research candidate substitutes the signed right-hand side of the
sign17 row `V = f² * inner - c` for old coordinate 17, then removes that row.
The remaining seven squared residuals use 16 natural witnesses and keep input
coordinate zero unchanged. Every old natural zero projects to a new natural
zero. The reverse direction is proved only **conditionally**: it works when the
signed replacement is nonnegative. Establishing that condition for every new
zero remains open, so no unconditional sign16/sign17 equivalence, consistency
claim, Lean bridge or iPRA endpoint is asserted.

A possible route to nonnegativity is to obtain the maintained window and strong
norm premises from the seven remaining rows. The deleted V coordinate occurs
elsewhere only squared, in Na. Its square agrees with the square of the natural
absolute difference `absdiff (f² * c * T) (f² * R + c)` even before its sign
is known. This may permit `Sign33Windows.windows_from_maintained_norms` to yield
the half-window inequality and then `Sign33InnerVRing.inner_v_of_window_and_strong`
to yield the desired nonnegative representative. Derivation of all premises
from this reduced AST and their formal model transport are **not yet proved**;
the route must not assume the very V witness it seeks to construct.

The retained residuals have syntactic total degree at most 56. Specializing all
witnesses to t, Na does not use input zero, and its t^56 coefficient is
`64 * beta^34` in `Z[t,beta]`. The fixed-port square-sum therefore has t^112
coefficient at least `4096 * beta^68` and exact external degree 112 for nonzero
beta. The inherited beta bytes decode as positive unsigned big-endian bytes;
all port hashes are checked. This is not a Lean interpretation or byte binding.

Run from this directory:

```
python3 -I -S -B build.py --check
python3 -I -S -B check.py
```

The author checker verifies exact AST substitution, the degree witness, port
hashes and finite integer lifts, including a natural-lift example. Finite
controls cannot prove nonnegativity for every zero. The
[independent external audit](../../reviews/nine-sharing-sign16-external-independent/README.md)
and [independent final-plan review](../../reviews/nine-sharing-sign16-final-plan-independent/README.md)
passed; the candidate packet is frozen. The natural lift and equivalence remain
open, and the degree claim is external only.
