# Attribution, reuse, and proof scope

Prepared as a research contribution for Vladimir Reshetnikov's ProveIt
repository. New prose, scripts, and certificates use the MIT No Attribution
terms in `LICENSE`. Existing third-party materials retain their own terms;
this notice does not replace or expand them.

## Immediate predecessor

The complete `K221_Construction_2026-10-20.zip` delivery is retained unchanged
under `portable/vendor/`, with SHA-256
`a06c99b775193d9642a2734b7dd5fe7b72736fbdf9d9d8be438321d5e5d57ba4`.
It was taken from `docs/incoming/` in ProveIt revision
`c011e44bc2df6238940bb600833730873b308334`.

The final K220 construction preserves K221's logical theory. The calculus,
output-root and seed reformulations, ordinary-core interpretation, and
set-theoretic consistency calibration are inherited from the retained
construction packets and Elliot Glazer's K230 development, pinned at
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`.

The predecessor notices credit Mira, ProveIt, Jeff's busy-beaver development,
Andrew James Wade, BusyCoq, and the Coq Library of Undecidability. Their MIT,
MIT X11, MIT No Attribution, and MPL 2.0 notices remain with their materials
inside the unchanged recursive parent delivery. No repository-wide relicensing
is asserted for files whose upstream license is unspecified.

## New contribution and adapted code

The new construction re-encodes a nonpure decoder role, performs two exact
closed source reassociations, and folds one additional role using an existing
predecessor-bit helper path. It supplies the resulting literal 220-state
machine, canonical relabeling, full source, and fresh final runtime receipts.

- `portable/build220.py` implements the new deterministic construction. It
  imports authenticated source and decoder utilities from the retained K221
  packet instead of modifying their implementations.
- `portable/check_runtime220.py` adapts the parent runtime driver to the exact
  new source/table and authenticates the unchanged `symbolic_runtime.py` and
  `independent_runtime.py` dependencies. The inherited runtime's mathematical
  representation and induction engine are not rewritten for this candidate.
- `portable/canonicalize220.py` provides an independently implemented dense
  canonical simulation as well as sparse native simulation and exact frame
  reconstruction.
- `portable/audit_runtime220.py` independently checks the case inventory,
  literal unary/list block schemas, source identity, contextual fold blocks,
  positive durations, table identities, and exact blank initialization. It
  does not claim to turn stored summaries into a fresh proof trace.
- `research/encoding/` adapts the pinned compiler, source definitions, and
  runtime for precisely scoped finite experiments. It includes its own
  attribution and copied license notices.
- `research/theory/` and the report contain the new formalism investigations,
  uniform arguments, countermodels, and independent source reassociation check.

The new endpoint is an ordinary mathematical proof formalizable in ZFC, with
executable symbolic certificates. No newly compiled exact-K220 proof-assistant
kernel endpoint, internal PA proof-code endpoint, absolute consistency,
unconditional nonhalting, global priority, or minimality claim is made.
