# Natural norms from actual 72 zeros

[`FreeMainStrongNorm.strong`](FreeMainStrongNorm.lean) passed its guarded
[Lean check](observations/strong02/result.json). For every positive 72-graph
zero at natural ports in any `IΣ₁` model, it derives the natural strong norm
`(i c²)²+delta(a)=delta(a) f²`. It transports the unchanged W residual through
the checked q-cube lift to `P64Root.strong`.

Lean exited 0 with `[propext, Classical.choice, Quot.sound]`, no warnings or
`sorryAx`, stable direct guards and no monitor stop. Output object SHA-256:
`0396dc0d272ba556762ac08c1b80a8b4669b74af2117176cc7b15547c3f51918`.
The first failed simplification attempt is retained at `observations/strong01`.
The source comment saying “unchecked draft” predates the successful check and
is retained for hash linkage. Direct-provider transitive, dynamic and
between-sample ancestry remains inherited.

This establishes the strong norm only. The independent-y auxiliary natural
norm and actual rank/window extraction remain to be derived. No unconditional
`m=R`, reverse implication or iPRA endpoint is claimed here.
