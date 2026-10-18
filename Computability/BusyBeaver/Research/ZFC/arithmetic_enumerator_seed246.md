# Seeded arithmetic scheduler for the 246-state route

`ArithmeticEnumeratorSeed246` proves the internal scheduler/validator equivalence at candidate `NP=3`, pointer `CP=0`, and working fields `TW=WS=H=0,D=3`. Both the proof-code witness and the run-time witness range over every value of an arbitrary IΣ₁ model. Its fixed closed arithmetic sentence is provable in IΣ₁ and PA.

The forward direction generalizes candidate reach to any internal starting index. Every candidate at or above that index is reached unless a prior halt has already occurred. The existing refutation word has raw candidate code at least 3, so starting at 3 still schedules it. A uniformly halting word works from arbitrary initial working data. For the reverse direction, the initial working state is certified: top and cache are truth, the stack is empty, and the certificate imposes no condition on `D`.

This extends the [earlier arithmetic enumerator equivalence](arithmetic_enumerator_equivalence254.md) to the required seed. It does not identify this scheduler with the [exact246 binary run graph](arithmetic_machine_run_prefix246.md), and it does not yet identify validator acceptance with a standard ZFC contradiction-proof code. Those two comparisons remain part of the [PA internalization work](pa_internalization.md). The ordinary [logical seed theorem](logical_seed246.md) and the [arithmetic bootstrap](arithmetic_bootstrap_prefix246.md) remain separately recorded facts.

The [successful record](results/arithmetic-enumerator-seed246-verification.json) passes ten named axiom probes and eleven typed callers. Every probe uses only `propext`, `Classical.choice` and `Quot.sound`. Source and audit took 4.779 and 2.071 seconds, with no warnings. The fresh source object was recorded before the audit and remained unchanged afterward.

The [history](results/arithmetic-enumerator-seed246-history.json) preserves the original preparation, run1's source failure and two unused-simp warnings, and run2's successful result. The repair rewrites the conditional with `if_neg hv` before normalizing addition associativity; theorem statements, the audit and proof limits are unchanged. Run1 did not reach its audit and produced no successful source object. The initial inventories and review remain descriptions of their original unbuilt source, while the [successor review](results/arithmetic-enumerator-seed246-review.json) separately covers the repaired source and existing successful evidence.

The guard selects exactly 48 project modules from the frozen EnumeratorEquivalence254 evidence, three direct Foundation/Mathlib cache boundaries, Init, and the explicitly retained Omega toolchain boundary. All 122 inputs are pinned. The legacy enumerator evidence has four successful commands and two fresh objects; its schema does not record the stronger pre-audit object-hash fact. The new seeded record does. MP254 supplies matching compiler and boundary evidence, while its unrelated project modules are excluded.

The portable guard changes only the default locations of this source and audit. Both parent evidence records already use maintained defaults. Successful records preserve their historical source/object paths, and the packet does not rebuild or redistribute those cached objects. With those exact prerequisite bytes available, prepare from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_enumerator_seed246.py \
  --repo "$PWD" \
  --output /tmp/zfc-arithmetic-enumerator-seed246-prepared \
  --prepare-only
```

Preparation executes no compiler or version query. Removing `--prepare-only` checks this source and audit under a shared 120-second bound, one thread, 4,096 MiB, and default new-source proof limits. No dependency build or download occurs. This is a recipe using the recorded caches, not a clean-checkout build claim.

Attribution follows the underlying program and calculus: Mira-Cult, Jeff Ketchersid and Andrew James Wade, with source63's contextual reduction supplying the 246-state candidate.
