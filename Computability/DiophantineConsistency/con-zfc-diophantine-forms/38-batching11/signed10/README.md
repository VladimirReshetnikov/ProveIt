# Ten unrestricted integer variables

`generated/signed10_b2.json` is a completely fixed integer polynomial in
`f,g,h,k,l,w,x,y,z,m`. Its exact total degree is 449,607,016 and its
division-free evaluator has 773 binary operations. `PROOF.md` gives its
definition, source theorem, imported Lucas interface, and consistency
equivalence.

Run from any working directory:

```sh
python3 path/to/signed10/build.py
python3 path/to/signed10/verify.py
```

Python 3.10+ and the standard library suffice. The sibling `compiler/`
directory is the single authoritative complete native four-port binding. The generic
symbolic source in `data/parent_quartic31.json` is retained byte-for-byte from
upstream; its historical default-binding metadata is inert. The active binding
is `data/INSTANCE.json`, which points to the sibling compiler. Every derived
weighted coefficient and `beta_sun=2^1359528` is fixed by the supplied recipes.

The final theorem additionally invokes Sun's 2026 modified Lucas certificate
(Theorem 3.1), full residue interpolation (Theorem 4.1), and positive/reverse
binomial bridges (Propositions 6.1 and 6.2). This dependency is independent
of the nine-natural construction elsewhere in the archive. No new end-to-end kernel certificate
is claimed.

Attribution: `build.py`, `verify.py`, and `circuit.py` adapt source `31-sun10`
in ProveIt at commit `22e75dd6b87b1b199bb08c778d7cf075ae5aae08`; the new source
packing uses the shared construction that packs 22 quadratics at Sidon
positions. The parent archive's license and preserved source notices apply.
The byte-exact source proof and finalizer in `inherited/` are provided for
offline audit; their old source and binding metadata are inactive. The finite
audits are transcription and coefficient checks, not a test of unbounded
solvability.
