# Abstract mask-cover diagnostic

This held, source-pinned single-stage check targets the strict natural-number cover lemma in the independently reviewed split draft. It does not prove a symbolic mask bound, an all-model cast, or a graph guard.

The direct `Mathlib.Data.Nat.Basic` import was absent from the inherited 81-provider outside baseline. `capture-outside.py` records its first selection and all companion presence, hashes and targets under the same project, package, core search order. The resulting capture is pinned in the runner and rechecked before and during the check. The outside capture does not establish transitive package or dynamic ancestry.

The read-only preflight exited 0, 25 runner-policy controls passed, and six copied-wrapper controls passed; none invoked Lean. The [independent prelaunch review](../../reviews/trace74-symbolic-mask-abstract-cover-prelaunch-independent/README.md) approved one run.

Runner SHA-256: `0496724f61a2cee6e9dc4f808893dec3b07f4b5c53329c574b01b0c38dc4ed9a`; wrapper SHA-256: `f63cf891352e8756c9f3feae574253eb810f794c14f07c35ec1e26454549cd03`; outside capture SHA-256: `fafc32d5893032eac67ac31a54113056e00573066d57a98b3b179c695d42a40e`.

Attempt01 completed with actual outer exit 0 and child status PASS. The [child result](observations/attempt01/result.json) SHA-256 is `afc1610f51385166532983d2d5179872a8fc026049eb82a2455caa36b4e47a30`; the [outer receipt](observations/outer-attempt01/terminal.json) SHA-256 is `b769e3ebcfea926a1cd91e09a22d91c922070a5ee535c52b9cb49fe6eea83251`; the output object SHA-256 is `72d5c66a1959b6a5e52811a7a277296e6434cd4f1865e2199b6b89abcb45ac80`. The [independent result audit](../../reviews/trace74-abstract-cover-result-independent/README.md) passed. The theorem assumes the strict defect bound and the exact low identity; it does not establish either for the actual symbolic ports.
