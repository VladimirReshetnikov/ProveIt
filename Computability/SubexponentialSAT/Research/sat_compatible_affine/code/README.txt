EXACT FINITE VERIFICATION CODE
==============================

Requirements: Python 3.9 or later; standard library only. No external
repository checkout, network access, numerical package, SAT package, Lean,
or Rocq installation is required for these finite checks.

Recommended commands, from the archive root:

    python3 verify_all.py
    python3 -O verify_all.py
    python3 verify_all.py --quick

The default runs all eight checks. --quick skips only the independent
ten-group root replay, the most expensive checker. -O is propagated to
child processes. Every acceptance condition remains active under -O.

The wrapper copies the code and necessary inputs to a temporary directory,
regenerates the certificates there, runs the independent audits on those
regenerated certificates, and compares exact JSON fields with ../results/.
It automatically removes the temporary directory. Delivered files remain
unchanged. For a persistent run summary, pass --output PATH to verify_all.py.

Wall-clock times and convenient decimal displays are excluded from the
reference comparison; exact fractions, rational intervals, witnesses,
pruning bounds, plans, support counts, and status fields are compared.
An input certificate path is compared by filename because its directory
changes during an isolated replay.

FILES
-----

anchored_backend_checker.py
    Constructs all twelve affine ten-group plans, all 1,152 supports and
    pair tables, proves the global support maximum by exact pruning, and
    checks the complete three-stage coefficient bounds. The thirteen-group
    fraction is a named dependency independently proved by the next file.

check_anchored_thirteen.py
    Constructs the three thirteen-group plans with a breadth-first traversal
    and evaluates all 132^3 = 2,299,968 support triples with exact integers.

independent_affine_audit.py
    Independently reconstructs root supports and recomputes each prefix
    bound rather than reusing the producing checker's incremental state.
    Standalone invocation:
        python3 independent_affine_audit.py anchored_backend_certificate.json

independent_thirteen_audit.py
    Reconstructs the middle-stage supports in a different traversal order,
    enumerates the complete support product, and independently checks the
    strict schedule gates and rational final coefficient intervals.

check_consistent_certificate.py
    The exact compatibility certificate for the inherited nine-plan menu.
    It is also the sole local import used by the next file.

fixed_menu_optimal_certificate.py
    Proves the optimum of the old nine-plan Euclidean support envelope
    using exact rational weights, a matching direction, and a complete
    finite support certificate. Its optimality is restricted to that
    envelope; it is not a lower bound for SAT or other algorithms.

verify_selector.py
    Checks exact plan selection and contraction regrouping on finite
    dyadic mode lists over Z/8Z, including empty-list and invalid-dimension
    cases. These are semantic fixtures, not a performance benchmark.

check_local_obstructions.py
    Finite illustrations of the prime-cycle and variable-coherence lemmas,
    with composite-cycle and vector-space scope controls. Their proofs
    belong to the research report; finite examples do not replace proofs.

The two adjacent anchored_*.json files are frozen inputs for convenient
direct audit invocation. Reference results for every checker live in
../results/. Running individual producers directly writes their generated
JSON beside the script; use verify_all.py to avoid modifying the package.

LIMITATIONS
-----------

These scripts certify finite combinatorial maxima, exact rational bounds,
and small semantic identities. They do not implement the asymptotically
fast matrix multiplication backends, the full tensor contractor, or a
complete 3-SAT solver. The source analytic theorems remain explicit
dependencies of the research result. The leading coefficient is per
normalized wire, and the logarithmic asymptotic order is unchanged.
