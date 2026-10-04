# Five-signal branching and a uniform ordered-section counter compiler

Core packet frozen on 4 October 2026 for independent mathematical audit.

- `PROOF.md`: complete proof, exact test rules/tables, physical inverse, encoded-state guard coverage, counter-machine compilation, timing, and primary-source positioning
- `static_algebra.py`: newly authored static rational checker; inspected before execution; no simulation or collision search
- `evidence/static_checks.json`: successful exact arithmetic and rule-syntax certificate
- `dependencies/realization63_PROOF.md`: unchanged predecessor proof; the needed translation primitive is also re-proved in this packet
- `MANIFEST.json`: SHA-256 pins for every content file above

Result: a nondestructive full-section branching gadget on two explicit open cones, and one fixed finite rule table per fixed two-counter program, correct for every initial counter pair. Exactly five signals remain live, all instruction sections have L<X<Y<R and one messenger at L outgoing +1, and every nonhalting transition takes at most 32 binary events and time between D and 10D. A common 19-element rational speed set suffices.

Five-live-signal universality is a known precedent, credited prominently to Durand-Lose's MCU 2004/2005 construction. No novelty, minimum-population, noise-robustness, fixed-arity Diophantine-halting, or proof-assistant claim is made. The static certificate passed; independent mathematical audit is pending at freezing.
