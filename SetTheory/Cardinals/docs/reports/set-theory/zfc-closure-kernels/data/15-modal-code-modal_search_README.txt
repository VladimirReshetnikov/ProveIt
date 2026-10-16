Non-reflexive coordinate quantifier diagnostic
=============================================

Run with Python 3.10 or newer from the archive root, after fetching the
source dependencies using machines/fetch_dependencies.py:

    python code/modal_search.py --output results/modal-search.json

To use an existing checkout with the pinned files:

    python code/modal_search.py --repo /path/to/ProveIt --output /path/to/result.json

The default --repo is machines/upstream relative to the archive root, so
the script also works from another working directory. With no --output,
the full JSON is printed. No third-party Python packages are needed.
Python -O, -OO, and PYTHONOPTIMIZE are rejected because assertions perform
the evaluator crosschecks. The checkout is read without writing bytecode.

Before importing any research module, the script verifies SHA-256 hashes
against machines/source_pins.json for theory_backend_experiment.py and its
two imported research dependencies, recover_wade_dag.py and
pairing_backend_experiment.py, plus the published logic/spec.py. The
published_spec() loader parses only the pure formula definitions in that
specification; its enumerator is not run. The result records these hashes
and the source commits. The CP and GIC formulas are not copied here.

Semantics and scope
-------------------

D has size 2 or 3. At valuation v, All(x,A) holds iff A holds after replacing
v[x] by each point of D other than v[x]. Each coordinate quantifier thus uses
the complete irreflexive accessibility relation. Implication is Boolean.
Membership is an arbitrary irreflexive relation R, making the runtime's
relative falsity R(v[0],v[0]) false at every valuation. This is deliberately
nonstandard first-order semantics.

The exact named CP and GIC ASTs come from the pinned published specification.
Every shadowed binder is respected. Labels a,b,c are pairwise distinct;
their assigned domain values may coincide. A GIC matrix is an arbitrary
Boolean function phi(a,b), independent of the fresh c coordinate. This is
a diagnostic of these formulas in these frames, not an implementation of
the program's entire gated axiom enumeration or proof search.

Result: none of the four IR relations on D=2 or the 64 IR relations on D=3
satisfies CP at every assignment. Consequently there is no CP survivor to
test against all GIC matrices. The JSON contains an explicit CP-violating
assignment for each relation and specifies the bit order of relation masks.
No all-matrix GIC model, completeness theorem, instantiation theorem, or
Turing-machine halting conclusion is claimed.

An independent direct recursive Boolean evaluator agrees with the bit-vector
evaluator for CP on every tested relation and assignment: 32 cases for D=2
and 1728 for D=3, totaling 1760 CP crosschecks. It also agrees for GIC on
all 4 relations, all 16 binary matrices, and all 8 assignments for D=2,
giving 512 GIC crosschecks. These comparisons validate evaluator agreement;
they do not assert that the checked GIC instances hold. There are zero
GIC_candidate_matrices_checked_after_CP because every relation fails CP.

The finite search outcomes and violating assignments are deterministic.
The elapsed_seconds fields are timing metadata and vary between runs.
