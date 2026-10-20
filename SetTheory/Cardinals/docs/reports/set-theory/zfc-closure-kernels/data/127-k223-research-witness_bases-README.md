# Uniform equality witnesses

These are separate research results, not premises of the 223-state construction.
The ordinary uniform proof is in uniform_witness_basis.md. Both finite proof-local
certificate families have passed two separate checkers. They exercise 71 closed
roots each; the uniform theorem is not inferred from those finite instances.
TAUT leaves abbreviate classical consequences of the retained logical basis and
are independently checked by Boolean evaluation. No new proof-assistant endpoint
is claimed. Source-only and provisional machine costs are distinguished in the
cost snapshot; neither basis has supplied a smaller verified machine here.

Recommended read-only certificate replay from this directory:

    python3 -B check_witness_strict.py uniform_witness_tag1_dag.json --output /tmp/uw-check.json
    python3 -B check_witness_strict.py symmetric_witness_tag1_dag.json --symmetric --output /tmp/suw-check.json

The other checker writes its deterministic receipt beside the input certificate;
run it in a copy if preserving the archive byte-for-byte:

    python3 -B check_uniform_witness.py
    python3 -B check_uniform_witness.py --symmetric

The generator scripts and hilbert_builder.py reproduce the compact formula-DAG
certificates. Their noncompact development intermediates are intentionally omitted.
