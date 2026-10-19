# Optional alternate-layout verification

The retained `cluster_variant1` is a different **240-state** layout. It is
an optional research artifact; the main 239-state machine does not depend
on it.

From the companion package root, with the verifier installed in
`verification/`, run:

```sh
python verification/verify_alternate_layout.py \
  --baseline-table reference/zfc240_old.tm \
  --baseline-sites machines/sites_logical.json \
  --alternate-dir research/cluster_variant1 \
  --output alternate_layout_replay.json
```

This quick, standard-library-only check validates the four exact table and
source hashes, complete transition domains, and complete source trees. It
recomputes all 1,932 pairs and edges of the source segment bisimulation and
compares the result with the supplied certificate. It also executes both
literal tables for 409,691 transitions from blank tape and checks their
identical complete seed frames, including the zero exterior. It does not
infer unbounded table-to-source correctness from that finite initialization.

To repeat the optional unbounded runtime proof, append:

```sh
  --runtime verification/symbolic_runtime.py
```

That mode rechecks all four list-block schemas and all 8,386 symbolic cases
for the **alternate** source, with arbitrary natural register values,
additional gap, and spare-list length. It uses the packaged engine and its
adjacent `independent_runtime.py` helper. The original baseline validation
remains enabled; the alternate source receives equivalent structural and
type checks plus its own exact hash validation. No engine rule or validator
is replaced. This is an executable mathematical check, not a
proof-assistant kernel theorem.

Run Python without `-O` or `PYTHONOPTIMIZE`. The default replay has been run
successfully against the packaged files. The full alternate runtime proof
was completed during research and recorded in `construction.json`; this
packaging replay did not repeat that longer computation.
