Frozen QH5 dependencies for check_inherited_emitter.py

The wrapper calls only emitter_check() from check_commands.py, with its ROOT
redirected to this release's frozen construction/inputs/qh5/construction.
It independently resolves coefficient-six and coefficient-five source trees,
replays all 61 multiplier bindings and 3409 outside instruction edges, and
compares the coefficient-five graph with the frozen QH5 graph used to build
the new machine. It separately replays the 61-line K/S/MP exchange certificate.

source_binding_reference.py is the unmodified original construction/build.py,
retained for attribution and comparison, and is not imported by the wrapper.
exchange_certificate.py is retained unmodified; the wrapper independently
replays exchange_certificate.json without importing that generator.

PROVENANCE.json records source archive members and SHA-256 digests. These
finite source/term checks support ordinary mathematical proofs; they are not
an end-to-end proof-assistant certificate or a physical TM replay.
