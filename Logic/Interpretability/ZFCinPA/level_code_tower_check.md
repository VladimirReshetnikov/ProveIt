# Checked internal formula-code tower

The unchanged [LevelCodeTower source](Lean/ZFCinPA/LevelCodeTower.lean) passes
a fresh Lean check and **35 axiom probes with 35 typed clients**, with no
warnings. The [actual record](results/level-code-tower-verification.json)
checks the recursive closure-kernel and level-satisfaction code builders,
their Σ₁ graphs, and their defining equations in arbitrary IΣ₁ models.

The builders are total at every model element, including nonstandard indices.
Quotation agreement with the externally defined formula families is proved
at standard natural-number inputs. The Sigma-truth, Pi-falsity and Pi-truth
wrappers retain that distinction. These are syntactic code constructions;
the module supplies neither nonstandard truth soundness nor the proof-package
base, successor and extraction obligations of the uniform selector.

Source and audit took 18.448 and 3.174 seconds with one thread, 4,096 MiB
and a shared 120-second deadline. The source retains sixteen local heartbeat
limits of 1,000,000 and one of 2,000,000 for its fixed free-variable bounds.
The audit uses default proof limits. All 398 recorded inputs and the fresh
first-provider object remained unchanged after the audit. Every probe uses
only standard Lean axioms.

The actual [UniformStatement check](uniform_statement_check.md) supplies
38 selected project providers. Seven opaque Foundation/Mathlib boundaries
and Init remain explicit, including current-only companion observations
where earlier records captured only a source/object pair. The cached D1
history and other inherited limits remain recorded; no complete cache check
or dependency rebuild is claimed.

The [publication](results/level-code-tower-publication.json) and
[history](level-code-tower/history.json.gz) preserve the source/API reviews,
audit, guard and actual logs. This closes one original validator inventory
entry; the final PA comparison remains pending.
