# Constructor sharing in a finite equational presentation

This directory contains the E679 experiment described in the enclosing paper.
It specializes the 688-bit presentation from the pinned ProveIt236 packet by
identifying three closure-witness operations with existing constructors:

```text
Target(b) = Q(b)
Next(b,z) = P(b,z)
Mem(b,z) = A(b,z)
```

The result has nine operation symbols and seven equations. Its complete
fixed-width packet is **679 bits**. The enclosing package's separately charged
prefix codec represents the same presentation in **586 bits**. The E663
presentation from ProveIt235 has a smaller 574-bit prefix packet, so E679 is
retained as a proved semantic experiment rather than the selected packet.

`constructor_fusion.tex` supplies both mathematical directions. Literal
identification of operation names gives one direction; the other requires a
model construction with fresh copies of membership types and compatible
constructor/witness choices. The script does not infer that model theorem from
finite tests. The optional eight-operation specialization is also discussed in
the TeX proof, with a larger 684-bit fixed-width cost.

## Reproduce the exact finite packet

Use Python 3 with assertions enabled:

```sh
python3 -B build_e679.py --out /tmp/e679-replay
```

The default inputs are the exact `E688_reference.json` and
`E688_reference.bits` supplied here. The script checks their fixed hash,
preserves every term tree and variable occurrence, checks the nine changed
operation sites and their context-dependent structural inverse, round-trips
the complete packet, and rejects every strict truncation and the malformed
controls. Compare the generated files with `generated/`.

`E679_manifest.json` pins the contents of this directory. The mathematical
argument is ordinary mathematics; the executable checks establish exact
construction and encoding. No binary TM proof-search interpreter, packet
writer, initialization, or native state bound is supplied for this route.

The inherited equational target is noncollapse, equivalently nonderivability
of the designated ground query. An equational theory always has a one-element
model; its ordinary model-theoretic consistency alone is not the target.
