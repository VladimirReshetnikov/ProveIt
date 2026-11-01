# Finite-parameter matrix for Foundation induction

For each actual Foundation induction matrix this constructs a free-variable-free
finite-parameter matrix by fixing its free variables, proves openness is
preserved, and constructs its native intuitionistic induction instance. The
free-variable bound comes from `(succInd φ).fvSup`; no unproved equation
between the body and matrix free-variable bounds is assumed. Identifying this
instance with the previously proved GG-translated closed body, and deriving
the actual classical induction axiom image in native iPRA, remain open.
External transitive ancestry is inherited.

Run `python3 Computability/DiophantineConsistency/reviews/ipra-induction-finite-matrix-replay/replay.py`.

Author and independent peer PASS with identical source, object and full-log hashes for both modules.
