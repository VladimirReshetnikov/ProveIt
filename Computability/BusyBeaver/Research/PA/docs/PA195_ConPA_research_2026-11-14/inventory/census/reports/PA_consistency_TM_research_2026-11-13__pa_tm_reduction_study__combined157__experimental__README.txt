EXPERIMENTAL ALLOCATION MATERIAL -- NOT A SMALLER MACHINE

The baseline197 files describe the existing combined negation/MP candidate.
The fixed-node allocator is adapted from the repository's restricted
allocator. It treats unchanged compatible source nodes as fixed, preserves
the supplied core/startup rows and any discovered helper rows, and injectively
assigns all remaining source nodes to available state labels.

The new implementation collapses labels that are fully unprotected, are not
the root label 84, and are not required targets of any protected transition
into a single anonymous choice with a capacity bound. Such labels have no
remaining semantic distinction in this restricted allocation model. After
solving, anonymous assignments receive distinct concrete labels. Constraints
and runtime/prefix validation otherwise use the inherited model. This reduces
SAT symmetry; it does not expand the feasible family or establish correctness
of the model as a Turing-machine compiler.

Reproduction, from the parent bundle directory:

    python3 experimental/allocate_collapsed.py experimental/baseline197.sites.json experimental/identity --protected experimental/protected-startup.txt --seconds 5 --feasible-only --fresh 0

    python3 experimental/allocate_collapsed.py experimental/estimated196.sites.json experimental/rejected --protected experimental/protected-core.txt --seconds 30 --feasible-only --fresh 0

These commands require z3-solver. The recorded run used version 5.4.1.
The identity control returned PREFIX_PASS with 197 states and zero changed
rows. The second input has 158 internal nodes and a nominal retained-group
estimate of 196. The original explicit-label formulation timed out at 30
seconds; the capacity formulation returned UNSAT in less than 0.01 seconds.
The result applies only to this protected/fixed-node assignment model. The
second source also changes the startup seed path from 100000 to 1000000,
so even a feasible core-only allocation would require a separate startup
construction. It is not an acceptable blank-input candidate as supplied.

No finite run prefix, source-node count, or failed allocation establishes
that a smaller consistency machine is impossible.

source_language.py and build221.py are inherited compiler utilities, with
original provenance retained in ../licenses/. The baseline table was copied
from the combined negation/MP candidate at the pinned ProveIt revision named
in ../README.txt, adding only its explicit '#! start 74' header.
