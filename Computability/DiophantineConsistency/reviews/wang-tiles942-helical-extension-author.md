# Twisted band to helical plane: author receipt

Date: 2026-10-26. Author: `complemented47_review`.

This is the author self-review of two new Lean files, not an independent
peer review. All complete source and check code was read before the
first builds. Both first builds passed, and there were no source
corrections after execution. No existing frozen file, shared document,
or git state was changed.

## Frozen files

Paths are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `WangTiles942HelicalExtension.lean` | 187 | 7865 | `1ca88d926e0002f2ee0eb7974176ebbe0f400c473e3b7ab742a44421b834bdc6` |
| `WangTiles942HelicalExtensionChecks.lean` | 92 | 4065 | `4be293fb69c978e38d562934ef42370eb34b92e7899b8b00a9d0757c3abe7cda` |

The only direct main import is `WangTiles942HelicalQuotient`, SHA
`dd7e2a20254aba54f57d03cc6690a6c18d3d45d83fe3c44383f53be4c3162481`.
The author also wrote that imported module. The focused checks import
only the new main file.

## Exact scope

For positive natural width `w`, integer `L`, and a band function `C`,
the extension is literally

```text
r = (x+L) % w - L
q = (x+L) / w
extend C w L x t = C r (t+q).
```

`representative_in_band` proves `-L ≤ r < w-L` for arbitrary signed
coordinates. `extend_on_band` proves exact binding to `C` at all
canonical-band positions. The quotient and remainder arguments use
Euclidean integer division, including negative inputs.

`extension_properties` derives all the geometric hypotheses needed
by the earlier helical quotient: every actual tile is allowed,
horizontal and temporal matching hold globally, the origin is Start,
and `(w,-1)` and `(0,H)` are periods. Its premises are only:

- actual allowedness and temporal matching on the canonical band;
- horizontal matching between adjacent sites strictly inside the band;
- the actual twisted edge equality
  `(C (-L) (t+1)).west = (C (w-L-1) t).east`;
- vertical period `H` on the band;
- `C 0 0 = start` and `0 ≤ L < w`, so the origin lies in the band.

The horizontal proof splits at the rightmost representative. Before
that point, the representative increases by one and the quotient
does not change. At that point, it becomes `-L` and the quotient
increases by one, which gives precisely the supplied twisted edge
equality at time `t+q`. The period proof uses the same sign: adding
one width increases the quotient by one, so time must decrease by
one to leave the extension unchanged.

No machine execution, cofinality, coprimality, uniqueness of Start,
or assumed global-plane factorization is a premise or a conclusion.
The main theorem even permits zero `H`, since preservation of a
period does not itself require positivity. The focused composition
with `HelicalQuotient.exists_marked_word` requires `H>0` and proves
an actual `MarkedWord (w*H) (w:ℤ)` with every original band tile
preserved pointwise. Constructing the band from a computation and
proving the final `Con(ZFC)` equivalence remain separate work.

## Fresh checks

Both source files set `Elab.async false` and `maxRecDepth 10000`.
Fresh builds, executed sequentially from the repository root, were:

```sh
lake env lean -M 6000 -j 1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942HelicalExtension.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942HelicalExtension.lean
lake env lean -M 6000 -j 1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942HelicalExtensionChecks.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942HelicalExtensionChecks.lean
```

Both exited zero. The main log is empty. All fourteen axiom reports
contain only subsets of `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorry`, `admit`, `native_decide`, new axiom, or incoming
program execution.

Focused examples check negative-coordinate representatives and the
incorrect truncated quotient, the positive seam time shift and its
opposite-sign negative control, width one, both canonical-band
endpoints, failure of origin binding when `L<w` is omitted, and the
complete composition to the marked word. They retain the actual
tile directions and the original signed-address convention.

| Log | SHA-256 |
| --- | --- |
| `/tmp/wang-tiles942-helical-extension-main-stage1.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/wang-tiles942-helical-extension-checks-stage1.log` | `a097dca664f283673dfcab0e5c086fb9c9663c33df3899a03465c0da6cb9662d` |
