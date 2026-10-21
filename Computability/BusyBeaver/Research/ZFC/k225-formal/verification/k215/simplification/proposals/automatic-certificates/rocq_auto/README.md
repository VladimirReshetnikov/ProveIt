# The same automatically inferred certificate checked by Rocq

The Lean generator's **exact `entries.json`**, SHA-256
`5f78445c4455e6cef2a7bf5fd321fb940a05194d967fbe66c55b5fc1cde90eb2`,
also passes the normalized Rocq checker. No separately curated Rocq
correspondence table is required. The generator still has no trusted role:
Rocq checks the resulting certificate against the two actual source programs.

## Checked result

```coq
Theorem p215_dagPerm_auto R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
```

`AutoCert215.v` renders the 1,426 automatically inferred path pairs and
successor ranks. `Source215Auto.v` proves their acceptance and derives the
all-register theorem from the already checked `NCheck.check_one_sided_iff`.
The JSON's positive path codes use a high sentinel one followed by the
path bits from most to least significant. Accordingly the renderer uses
`rev (decode_path code)`; it preserves full consumed paths, including zeros.

Both new modules compiled successfully with Coq 8.18.0. Their three printed
assumption reports are closed. They reuse **ten** dependencies from the
previously accepted normalized source closure, whose original build and
ordinary recursive kernel audit passed. Each reused source and compiled
object is hashed in `verification/result.json`, together with that accepted
closure's receipt identity. The two new compiler invocations took 11.798 and
19.429 seconds; the concrete checking transaction reported 7.378 seconds.

This is a check of two new modules against bound reused dependencies. The
new automatic instance did **not** receive another full fresh dependency
build or recursive `coqchk`, and it is not a rebuilt binary/ZFC endpoint.
The logs contain three expected load-path remapping warnings per invocation:
the broad accepted build root is followed by its explicit K230/K230P/K215F
namespace mappings. These are namespace search-path warnings, not proof errors.

## Reproduce

From the parent research packet directory, reproduce using the supplied
`rocq_normalized/` dependencies:

```sh
python3 rocq_normalized/build.py --out /tmp/k215-rocq-normalized --recursive
python3 rocq_auto/render.py
python3 rocq_auto/build.py --accepted-build /tmp/k215-rocq-normalized --out /tmp/k215-rocq-auto
```

The delivered `rocq_auto/entries.json` is byte-identical to
`lean_auto/verification/entries.json`. The Lean emission metadata and receipt
record this same JSON hash. To regenerate the shared correspondence from the
actual decoder trees, rather than replay the delivered cache:

```sh
python3 lean_auto/build.py --lean /absolute/path/to/lean --out /tmp/k215-lean-auto
cp /tmp/k215-lean-auto/generated/entries.json rocq_auto/entries.json
python3 rocq_auto/render.py
python3 rocq_auto/build.py --accepted-build /tmp/k215-rocq-normalized --out /tmp/k215-rocq-auto-regenerated
```

The output directory must initially be empty. The build checks the compiler
identity against the accepted dependency receipt, binds all reused providers,
and compiles the two new modules under the shared proof-build lock. It performs
no network access and does not modify the normalized package or its outputs.

To refresh correspondence, regenerate `entries.json` with the Lean source-tree
emitter, replace this cache, rerender, and check both lanes. Identity of generated
data is a reproducibility fact; semantic acceptance is the logical premise.

## Sizes and attribution

`AutoCert215.v` has 1,445 lines / 110,668 bytes; `Source215Auto.v` has 22 lines /
788 bytes. Full consumed path codes make this data slightly larger than the
109,115-byte previously maintained normalized certificate. The benefit here
is sharing automatic inference across both proof assistants, not a further
state or certificate-entry reduction.

The source semantics, literal programs, and checker are inherited from the
accompanying normalized Rocq packet and its pinned ProveIt references. Its
license directory retains their notices. This supplementary rendering,
instance proof, and build work follows ProveIt's MIT No Attribution terms.
