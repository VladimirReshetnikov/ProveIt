PA194CSZ: an optional 194-state companion
======================================

This auxiliary construction combines the supplied symmetric-guard PA194CS machine
with a proved-zero-register jump. It is a separate 194-state companion to the
main report's 4R, radix-5 and radix-6 machines, not a result below 194 states.

The authoritative table is machine/pa194CSZ.tm. Its working states are 0 through
193, its initial state is 0, and its separate terminal halt label is 194. The
head starts at cell 0 on an all-zero two-way infinite binary tape. Every one of
the 388 transitions writes a bit and moves exactly one cell left or right.
Rows have five columns: state, read bit, write bit, direction, next state.

Dense-table SHA-256:
62e93098caf7c09ff2938d07064f0dbbb47c71ec369892968258fff708592269

Native-table SHA-256:
7ee1623cecc0134e5d95d81634f334df446bccc95ea08d9f56ef45d06dd8da2f

Construction and proof
----------------------

Relative to the pinned PA194CS predecessor, the only native table edit is:

  (27, 1): 0 L 40  ->  1 R 21

The only source edit is at site 26:

  jump 34  ->  decrement register 6, zero successor 34, positive successor 27

The source still has 3,646 sites. A finite positivity-mask invariant is computed
from the exact clean seed at site 25 with logical registers
[2,0,0,0,0,0,0,0,0]. Its 263,180 (site,mask) pairs form a common inductive relation
for the old and new sources. Every reachable mask at site 26 has bit 6 clear,
and old and new abstract successors agree throughout the relation. Induction
therefore proves equality of their concrete source executions from that seed.
The relation is recomputed for the symmetric guard; the older cached-controller
invariant is not assumed to apply unchanged.

The complete invariant is stored as text in machine/positivity_invariant.hex.
Each line contains the decimal source site and a 128-digit hexadecimal integer;
bit m records membership of (site,m). The SHA-256 in the JSON metadata binds the
decoded 3,646*512 bytes, indexed by 512*site+mask. This representation preserves
the original logical certificate while keeping the package free of binary files.

proof_csz.tex gives the new invariant argument. proof_symmetric.tex preserves the
supplied predecessor's guard argument as an attributed reference fragment. The
ordinary PA nonhalting/consistency calibration is inherited through these source
and physical equivalences. No new end-to-end Lean or Rocq theorem is claimed.

Reproduce
---------

Python 3.10 or later and its standard library suffice, with assertions enabled:

  python3 -B build.py
  python3 -B verification/check.py

The scripts resolve all inputs relative to their own files and can also be called
by absolute path from another working directory. No network, repository checkout,
compiled executable, or proof assistant is required. Replay rewrites the generated
machine evidence and verification/results_csz receipts in this directory.

The construction checker verifies all 4,746 arbitrary-register source outcomes,
including the invariant-excluded positive branch of the new decrement. Its recorded
run uses 1,513,882 symbolic steps, maximum 508 per outcome. The independent literal
checker imports neither the compiler nor an arithmetic-box oracle. It rederives
four generic list traversals and verifies the same 4,746 outcomes in 1,100,566
symbolic steps, maximum 403, with minimum positive-duration constant 3. Frames
quantify over arbitrary natural register values, an affine gap and an arbitrary
finite nonempty spare list.

Both checks bind the exact complete clean blank-start frame reached after 58,014
literal transitions. The independent check separately simulates the whole tape
and checks the dense/native control bijection and two source-graph resolvers.

Package scope
-------------

Only this companion's tables, source, invariant, recorded evidence, replay code,
required predecessor inputs and attributed runtime/parser sources are included.
The four retained baseline_tools.py functions are unchanged extracts of the
supplied builder. The Lean files under reference are source/reference material;
this is not a standalone Lean project. Licences and provenance are retained.

The expensive construction and independent physical checks were completed before
packaging. Packaging checks preserve the exact table, source and receipt identities,
parse the Python files, verify local dependencies and decode the text invariant;
they do not claim another physical-proof replay. See PORTABILITY.json and
PACKAGING_CHECKS.json for that boundary.
