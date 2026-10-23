# Smaller coherent coefficients for Con(ZFC) equations

This directory provides a new fixed tuple with B=2^1064921, combining
mixed-radix clauses (wave4 package25), parity-separated copies (26), and
an explicit arbitrary-odd-factor Boolean controller (24). It is not a
splice of their numerical ports. All four values are recomputed together.

The mathematical adapter and its limitations are in COEFFICIENT_PROOF.md.
The exact current-pin sources are recorded in SOURCE_LEDGER.json. Programs
under sources/ are inert references and must not be executed for replay.

Payloads are actual minimal unsigned little-endian integers. The canonical
binding is payloads/COEFFICIENT_BINDING.json. MF_source is already shifted
by B−1. The total raw size is532479bytes; supplied gzip size10466bytes.
The two Python scripts are newly authored and use only the standard library.

Read-only audit:

    python verify_independent.py

Independent regeneration without changing delivered files:

    python build_coefficients.py --output /tmp/conzfc-coefficients-replay
    python verify_independent.py --payloads /tmp/conzfc-coefficients-replay

The verifier imports no builder. It reconstructs the full tile language,
decodes every actual DC digit and every mask bit, checks69230basis identities,
all modular-controller certificates, carry/slack bounds and73511small
coverage-algebra regressions. Mathematical equivalence is not inferred from
those regressions; its universal proof is provided separately.

A gzip implementation may choose a different header or deflate stream when
regenerating. Compare raw payload hashes and decompressed integers; the
manifest created by each run binds its own compressed bytes. The shipped
compressed bytes are also individually hashed and checked on read-only replay.

For the source-language notices, see the containing report's licenses/
directory, including the Wade K215 notice. New material is AI-assisted and
provided under the containing report's MIT-0 notice. No new end-to-end
Lean/Rocq certificate or global optimality claim is made.
