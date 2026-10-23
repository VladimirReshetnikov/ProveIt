# One-stack proof source, independent of K215 and Jones

## Delivered result and limits

`section.tex` gives the mathematical proof. A finite path from stack 0 to
stack 2 is equivalent, provably in ZFC, to a finite syntactic ZFC refutation.
The proof uses the numerical C222 calculus and its semantic calibration,
not any Turing-machine implementation or Jones universal polynomial.

The fully explicit **local** relation has three branches and five natural
witnesses. Its literal DAG has 382 operations. Nonlinear-wire flattening
gives 89 natural local witnesses and 85 quadratic residuals; their sum of
squares is a degree-4 polynomial with 3,108 monomials. These are local counts,
not the final global equation's counts. The optional cap4/cap16/cap64 files
trade additional local variables for smaller coefficients.

`OneStackEquation.lean` specifies a closed global constructor proposal using
one beta-coded state sequence, remainder graphs, bounded-forall closure,
and the existing direct quartic compiler. The construction deliberately
stops BEFORE Jones. It has no unspecified MRDP index or coefficient.
However, this new file has NOT been elaborated or kernel compiled. Its full
output polynomial is NOT materialized, and its final size is unknown.
Consequently this component does not claim a new smaller completed equation.

All arithmetic variables here are natural numbers including zero. The
existing final compiler's domain conventions must be preserved when its
result is integrated; do not silently reinterpret natural local witnesses
as unrestricted integers.

## Reproduce the local data and checks

These scripts are authored for this packet and execute no upstream code:

    python build_stack_step.py
    python flatten_stack_step.py
    python emit_stack_constructor.py
    python check_stack.py

The last command independently reads literal JSON. It checks exact sparse
sum-of-squares expansions for all four local variants, 160 modular circuit
replays with mutation controls, 148 branch fixtures, and a syntax-only
parenthesis check of the Lean proposal. Modular replay is regression testing,
not a proof of unbounded semantic equivalence or a Lean typecheck.

## Source pin and provenance

`SOURCE_PINS.json` records twelve sources at repository commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`. Their local bytes were checked
against GitHub API Git-blob SHA identifiers, and SHA-256 hashes are included.
The inherited calibration is `KEndpoint.c222_iff_zf_refutation` followed by
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`; `Bridge.lean` displays
the exact composition. Included source files are reference copies, not a
self-contained Lean dependency closure. Use the full pinned repository for
future elaboration. Source licensing remains the repository's license.

The conceptual novelty here is architectural within this comparison:
existential witnesses directly choose a proof tree; postfix evaluation
needs just one stack. No claim of historical novelty for arithmetizing
proofs, stack machines, CRT coding, or MRDP closure is intended.
