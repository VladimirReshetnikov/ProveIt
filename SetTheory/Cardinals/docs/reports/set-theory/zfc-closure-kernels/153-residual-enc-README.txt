ENCODING EXPERIMENTS AND REPLAY
=============================

Run from the archive root:

  python encoding/reproduce.py --output-dir replay/encoding

Python's standard library is sufficient. The command takes a few seconds
and writes fresh JSON receipts and the reconstructed source into the chosen
output directory. It does not modify the bundled inputs or sources.

Contents
--------

encoding_results.tex
  All-natural arithmetic arguments, exact source changes, independent
  source-audit scope, and the remaining binary-machine limitations.

inputs/k219.sites.json
  The original K219 source at repository commit
  26d5de6d21fa354d50e0b84fe851c289925b8d72.
  Input SHA-256:
  0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789

sources/counter_salt_208.sites.json
  Repaired, mathematically calibrated 208-DAG-node source; 4,741 primitive
  occurrences; maximum depth 38; maximum zero run 6.
  Output SHA-256:
  dc32510df9ffb07c2e106d835f735baff4a19989198a7f5bfec3f34e0046559d

macros/asymmetric.json, macros/strict_order.json
  Exact plain source-tree representations of the two arithmetic macros.
  The strict ordering gate's lower equiconsistency direction is not closed.

source_experiments.py
  Rebuilds all four repaired associations from pinned K219 input, checks
  source metrics and exact output bytes. It measures the unsafe 205-node
  all-asymmetric intermediate but does not present it as a valid machine.

check_arithmetic.py
  Direct structured interpreter; 4,165 finite inputs per macro.

audit_counter_salt_source.py
  Executes the actual repaired source's command AST with exact symbolic
  natural expressions. Checks DISCARD, RESET, and initial AX0 for arbitrary
  stack/current/parameter/cache cases. Its accelerated transfer, pairing,
  unpairing and equality rules have 1,622 additional unaccelerated finite
  checks. The mathematical loop invariants appear in the TeX section.

receipts/
  A successful local replay, provided for comparison. Fresh replay outputs
  are generated in the caller-selected output directory.

Status
------

The 208-node counter-salt SOURCE has the ordinary correctness argument in
theory/counter_salt.tex. Source DAG counts do not equal TM state counts.
The machine directory contains the separately checked 223-state primitive
interface implementation. Its blank-tape startup contract remains open.
No <=218-state Con(ZFC) machine is asserted by this directory.

The unsafe all-asymmetric 205-node variant can appear to compile to 218
states, but it admits the forbidden freshness triple (a,b,c)=(2,0,2), and
naive decoder reuse also fails primitive-interface checks. This negative
result is retained to prevent mistaking a small count for a valid machine.

Provenance
----------

The baseline source is derived from the user's ProveIt repository:
https://github.com/VladimirReshetnikov/ProveIt/tree/26d5de6d21fa354d50e0b84fe851c289925b8d72/Computability/BusyBeaver/Research/ZFC

It is bundled only to make the reconstruction self-contained. Repository
licensing and upstream attribution are retained by the enclosing archive.
