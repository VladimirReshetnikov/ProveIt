# Fully closed parameterized separation instances

For every model of PRA plus IΣ₁ and every internally valid arity-one property φ, including nonstandard codes, define

```
fullyClosedSeparation φ = modelClose (formulaFreeBound (sepRoot φ)) (sepRoot φ)
```

`formulaFreeBound` is a fixed Σ₁ structural recursion that computes the maximum free index plus one in a source formula. A binding decreases the bound by one, and model-internal induction establishes the exact truncated-subtraction law for any model-valued number of bindings. Zero bound implies shift invariance by structural induction. Thus `fullyClosedSeparation_sentence` proves that the result is an arity-zero formula fixed by free-variable shift. The imported Foundation source comments out its proposed `Language.IsFVFree` declaration, so the theorem states the equivalent intended conjunction explicitly.

`fullyClosedSeparation_leaf` proves the numerical compiler leaf from `SeedAdmission` at the actual closed axiom. This combines the new closure proof with the previously replayed separation simulation. It covers model-valued, possibly nonstandard, syntax and uses no extra size or pushed-environment assumption. It is a Lean metatheorem about models, not a native iPRA derivation; it does not establish that these instances form a uniform Δ₁ theory, nor the PA194 halting equivalence.

Replay from the repository root, using a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-fully-closed.sh "$PWD" \
  /dev/shm/pa194-model-separation-full-replay \
  /dev/shm/pa194-model-separation-seeded-replay \
  /dev/shm/pa194-model-closure-definability-replay \
  /dev/shm/pa194-model-closure-replay \
  /dev/shm/pa194-general-separation-replay \
  /dev/shm/pa194-ranked-open-separation-replay-v3 \
  /dev/shm/pa194-unrestricted-all-replay \
  /dev/shm/pa194-full-one-level-audit \
  /dev/shm/pa194-fully-closed-replay
```

Seven source modules and a 12-declaration audit are rebuilt together in a fresh output. The source files and the key previous separation object are pinned before and after; other staged overlays, Foundation and Mathlib are prebuilt. Successful log: `/tmp/pa194-fully-closed-replay.log`; no `sorryAx` appears in the audited declarations.
