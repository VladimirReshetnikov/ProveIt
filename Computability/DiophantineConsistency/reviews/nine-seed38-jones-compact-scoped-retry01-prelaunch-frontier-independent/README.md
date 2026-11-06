# Independent prelaunch review: explicit scoping target retry

**Pass for bounded launch.** The sole proof change exposes the definitionally equal boolean target with `change Norm38MacroRecipe.recipe.scoped = true` before `decide`; the theorem statement is unchanged. This directly targets the failed synthesis of `Decidable` for the named proposition. The runner uses a fresh output path, pins the exact failed state/log, verifies the source-only delta and retains the same recipe provider guards and resource limits. Lean's ability to reduce the target within those limits remains untested.

`check.py` checks exact packet pins, full proof delta, prior failure, direct recipe producer and fresh no-Lean preflight. Provider checks are point-in-time, monitoring is sampled and inherited initial-agreement numeric outer exit is unavailable. A success would show boolean binder scoping, not graph semantics or JSON binding. Preflight requires a fresh output path and refuses after launch.
