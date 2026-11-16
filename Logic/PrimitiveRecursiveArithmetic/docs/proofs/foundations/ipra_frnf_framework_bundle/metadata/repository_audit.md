# Repository audit and contribution boundary

Snapshot inspected on 2026-11-16, with the current PRA README at commit
`67f5216e0b1337b533b43064262aeff268bc56db`.

## Existing checked base

- `ConciseIPRA` defines the embedded calculus `Prf PRAAx` and proves the bridge
  `pra_iff_native` to the native scalar core.
- `Derivations` contains kernel-checked object-iPRA derivations and a substantial
  arithmetic library: quantifier-free induction, coding and simultaneous
  recursion, bounded search, sums, order, division, gcd, Bezout, linear algebra,
  and generic descent.

## Existing packet status

The `docs/proofs` corpus contains many strong mathematical blueprints and many
related general frameworks.  The repository README explicitly warns that the
packets were filed as delivered, generally were not rebuilt, and that most Lean
files are outlines.  Several framework files construct small `Prf PRAAx`
combinators, but no prior packet supplies a checked generic compiler for all of
its main claims.

## Contribution of this package

This package does not pretend to replace the checked `Derivations` library.
It proposes a common intermediate normal form and a migration route into that
library:

1. static specialization of fixed primitive-recursive transducers;
2. separate computation and justification horizons;
3. reverse demand closure before object induction;
4. one quantifier-free trace invariant per bounded component;
5. relational finite witnesses and backward viability;
6. stability/gap certificates for erasing internal choices;
7. an explicit producer/verifier boundary; and
8. a proof schedule whose output type is `Prf PRAAx`.

The paper proves the generic mathematics at the human-readable level.  The
reference Python implementation checks finite algorithms.  `lean/FRNF/Kernel.lean`
contains source-level logical combinators with no placeholders, while
`lean/FRNF/ObjectTargets.lean` deliberately exposes the remaining object-level
arithmetic implementation targets with visible `sorry` markers.  No kernel-check
claim is made for this archive because Lean is not installed in the artifact
runtime.
