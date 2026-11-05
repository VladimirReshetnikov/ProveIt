# Natural norms from actual 72 zeros

Both clients below have clean guarded Lean checks. For every positive 72-graph
zero at natural ports in any `IΣ₁` model:

- [`FreeMainStrongNorm.strong`](FreeMainStrongNorm.lean) derives the natural
  strong norm `(i c²)²+delta(a)=delta(a) f²`, by transporting the unchanged
  W residual through the checked q-cube lift to `P64Root.strong`.
- [`FreeMainAuxNorm.auxiliary`](FreeMainAuxNorm.lean) derives the natural
  independent-y auxiliary norm at the **actual graph rank**. Its absolute
  difference correctly covers either sign of the auxiliary expression; it
  uses the checked strong norm and the actual transport residual to cast the
  graph rank.

| Client | Clean receipt | Output object SHA-256 |
|---|---|---|
| strong | [strong02](observations/strong02/result.json) | `0396dc0d272ba556762ac08c1b80a8b4669b74af2117176cc7b15547c3f51918` |
| auxiliary | [aux04](observations/aux04/result.json) | `42c353eec1f0e4150ec9787dc82e5bcc34bff1419df3d5e8c8ef6ce4359b2bd8` |

Both Lean checks exited 0 with `[propext, Classical.choice, Quot.sound]`, no
warnings or `sorryAx`, stable direct guards and no monitor stop. Earlier
failed sources, logs and receipts remain under `observations/strong01` and
`observations/aux01`–`aux03`; aux03 compiled but was rejected for an unused
local warning. The source comments “unchecked draft” predate the clean checks
and are retained for hash linkage. Direct-provider transitive, dynamic and
between-sample ancestry remains inherited.

These are the two natural norm identities. Actual rank positivity and
compact-port half-window extraction and their final composition with the
conditional signed-half-index theorem remain. No unconditional `m=R`,
reverse implication or iPRA endpoint is claimed here.
