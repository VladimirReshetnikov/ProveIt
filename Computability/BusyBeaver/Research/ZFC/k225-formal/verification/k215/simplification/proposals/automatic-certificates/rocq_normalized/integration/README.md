# Production source bridge integration sketch

The standalone checked target is `Source215Normalized.v`; its receipt covers
that exact source and the original programs. `Source215.v` provides the same
proof under the existing public theorem name `p215_dagPerm`.

`source_bridge.patch` is an exact unified diff against reviewed commit
`53269bcab1efc0f82d3022645bd7cf0c22d84959`. It installs the four required helper/data
modules in `K215F` and replaces the generated source facade. Only imports are
adapted to that production namespace. The patch was checked for application;
this namespace-adapted production patch has not been compiled in the complete
Rocq 9.1 endpoint build.

Production adoption must also update `regenerate215.py` to emit/copy the same
sources and refresh `add_variant215.py` plus `manifest.json` with the new
compile order and hashes. The required relative order is:

```
Prog215, PathCodec, BisimMirror, NormalizedBisim, NormalizedCert215, Source215
```

`DagPerm` and the inherited `K230`/`K230P` dependencies must precede this block.
The old `OffsetBisim230` and `Cert215Offsets` modules are unused by this facade;
retaining them elsewhere is harmless. The new forward certificate theorem
replaces the previous two concrete direction checks. The public all-register
statement used by `Correct215.v` is unchanged.

After regenerating sources and manifest metadata, run the full maintained
237-module endpoint closure with the pinned production toolchain. Do not
interpret the source-only receipt as evidence that this integration gate has
already run.
