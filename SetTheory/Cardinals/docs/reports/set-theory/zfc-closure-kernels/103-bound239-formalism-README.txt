FORMALISM AND SOURCE-CONTROL CONTRIBUTION

Positive result
--------------
The original rotation240 register source and the supplied boundary224
register source have identical complete ordered control graphs. Thirteen
stages (25 local tree rotations) reduce the distinct internal source nodes
from 202 to 201 while preserving all 6,455 expanded instructions and a maximum
zero run of 6. This is a source result; 224 total source DAG nodes is not a
binary Turing-machine state count.

Run the complete portable checker, from the archive root:

  python3 formalism/extra/check_rotation_certificate.py

Python 3's standard library is sufficient. All acceptance checks remain
active under python3 -O. The checker verifies the pinned baseline bytes,
every replay stage, all 8,385 control edges and the unique halt descriptor,
canonical trailing-zero successor paths, the final source, and exact DAG
metrics. source_result.tex gives the general bisimulation proof.

Theory diagnostics
------------------
theory_filters.tex proves in ordinary ZFC that two explicit weakened CP/GIC
packets have set models: H_(omega1) for one good container without arbitrary
root coverage, and V_omega for containers containing each subset but not
necessarily an internal bound for all subsets. Consequently they cannot
have the requested ZFC-provable consistency calibration if ZFC is
consistent. Equality and all finite-parameter GIC instances are retained.

  python3 check_flat_container.py --max-root 255

The bit-code test is an exact finite diagnostic, not the proof of those
infinite model claims. The recorded result is flat_container_results.json.

alternative_formalisms.tex compares finite class theory, substitution,
ground rewriting, and interpreter approaches. Primary references actually
inspected are recorded in references.json. Known syntax measurements are
distinguished from binary state counts and open proof obligations.

Optional experiments
--------------------
The AX-clearing protocol in extra/ax_clear_notes.md has an exact arithmetic
simulation argument and a finite executable check, but the attempted
source change costs extra nodes. It is a rejected compression direction.

A bounded boundary223 source search was explored and then stopped after
the final239 binary construction succeeded. It supplies no accepted
additional source reduction or source-size lower bound. Large intermediate
checkpoints are excluded from this package.

Artifact selection
------------------
INCLUSION.json gives an explicit required/optional file list. Files outside
that list are intermediate discovery state and should not be copied into
the final research archive merely because they are present in this folder.
