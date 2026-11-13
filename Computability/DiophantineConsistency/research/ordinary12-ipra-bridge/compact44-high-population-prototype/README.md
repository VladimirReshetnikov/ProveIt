# Symbolic high-mask population: exploratory result

`CompactHighPopulation` defines an explicit 8,807-digit radix-`2^67` list
using constant runs. Lean proves that its digits are in range and that its
population is `986` in every `IΣ₁` model, together with the corresponding
model word bound. This is currently **single-side exploratory evidence**:
session 70407 actually exited 0 with no warnings or `sorryAx`; its log is in
`observations/attempt03.log`. A matched replay and independent review remain
required.

The [external transcription check](check_display.py) pins the exact Lean
list source and the retained compressed β and shifted MF payloads. It compares
all 8,807 digits and the full integer against `MF_source − β`, reproduces the
population 986 and rejects three digit mutations. Normal and optimized Python
runs actually exited 0. This is an external finite source/byte comparison;
it does not prove an internal equality between the symbolic list and the
graph's high port, nor prove machine simulation or an iPRA derivation.

Early attempts 01 and 02 failed on simplifier recursion and redundant tactics;
their sources and logs are retained. An optional attempt to prove the mod-8
residue was then explored separately: attempts 04, 06, 07 and 08 exited 1
with recursion-depth errors, and attempt 05 exited 134 after the configured
3,000 MB Lean memory limit. Their sources and logs are retained; none supplies
a residue theorem. The successful source and its population/word-bound
theorems do not import those failed attempts.

The proposed [paired replay](replay.py) has not yet run. It targets the
audited 342-module endpoint successor and retains its inherited Foundation
outer-wrapper, package-transitive and dynamic ancestry qualifications;
resource monitoring is sampled rather than a hard whole-process-tree quota.
