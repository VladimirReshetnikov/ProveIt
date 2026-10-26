# Actual internal C222 indiscernibility checkpoint

Authored and completely self-reviewed by `controller_certificate`, 2026-10-26. New files: `ZFCinPA.ValidatorEind222` (260 lines) and its 49-line checks. The main imports only the frozen relational checkpoint. Its finite argument follows the existing `BusyBeaver.ZFC.KEind222` proof pattern, but does not import or invoke that external Nat derivability/model-completeness theorem. All codes and labels below range over an arbitrary internal arithmetic model satisfying IΣ₁, and every `CProv` result contains an actual proof-code witness of the new represented C222 history.

Frozen source SHA256s:

- Main: `09ee7d8f43c4bf35486043beb4cfa191ad29ca5891797f0b2919476c825025f3`.
- Checks: `867662cc3efaef099f4e09b06ac78beeeb4f725c6dfd6b7aef0cc57ffed0e16b`.
- Replay inventory: `validator-eind222-replay.json`, `4874421e3a406aee5f59a52692790f8c1afaa24b0dbb6b6c4629fe225fbe12a9`.

The definitions are literal arithmetic constructor compositions. `Bin(v,a,b)` says that `v∈a` and `v∈b` imply each other; `Bout(v,a,b)` does the same for `a∈v` and `b∈v`. `Ev(v,a,b)` conjoins their universal closures at `v`, and `Eind(a,b)=Ev(a+b+1,a,b)`. The false code in each negative/conjunction abbreviation remains exactly 1.

The packet proves fixed-binder specialization and alpha conversion using rho1–6, derived primitive equality symmetry, membership congruence, and only gated membership vacuity. No arbitrary-binder primitive equality-vacuity theorem appears. The public endpoints are:

- `Eq_Eind a b`: primitive equality implies `Eind`; it first uses the actual equality helper at `wel(a,b)`, proves this label is larger than both inputs by Cantor bounds, then performs relational alpha conversion.
- `Eind_ex a b`: the actual existential code for `Eind(a,b)` is provable.
- `Eind_el_r` and `Eind_el_l`: both directed membership-substitution formulas are provable, with fresh label `a+b+c+1` justified internally.
- `Eind_euclid`: `Eind(c,a) → Eind(c,b) → Eind(a,b)`.
- `Eind_vac a b c`: `Eind(a,b) → ∀c Eind(a,b)` under exactly `c≠a` and `c≠b`.

The last proof handles the collision `c=a+b+1` explicitly by renaming to `a+b+c+1`, applying relational vacuity, and returning under the quantifier. Neither equal input labels nor label 0 is forbidden. Checks instantiate both `c=0,a=b=1` and the collision `a=b=0,c=1`, cover identical source/target binders, and unfold vacuity and existence results to numeric proof witnesses. Open assumptions are discharged by finite Kalmar deductions; GEN is applied only to closed proof witnesses or through explicit vacuity resources.

Complete sources and newly authored private drivers were read before execution and the final main/checks reread after compilation. The main passed its first fresh build with empty diagnostics (5.63 seconds). The first check build failed only on ambiguous imported names for `one_ne_zero` in the auxiliary-collision example. Qualifying `_root_.one_ne_zero` fixed it without changing any theorem statement or main proof. Its failed snapshot/log/time remain recorded and hash-checked. The corrected checks passed (1.93 seconds), with fourteen reports using only `propext`, `Classical.choice`, and `Quot.sound`. The failed elaboration's temporary `sorryAx` diagnostic is not an accepted theorem or successful object.

Fresh object SHA256s are `549f1f2ab2b2868a2ea3b9ab1991bc7ee60769fbfb1f391fa304deb0b0101d83` and `67416a2b2186454cecd0bf2460f110c59cb47855f3292c7990520e425582661f`. The private overlay is `/tmp/eind222-controller-10sptgah/lib`; its prerequisite inventory hash is `ae336bc172fadaf6e039d1379ff2f88a4bac41c090b8ce44b09e013981ae964e`. It reuses 125 authenticated current-source modules (95 Foundation) and 38 pinned external import boundaries. All source/object/compiler/manifest pins were rechecked before and after the builds. Only the new two leaves were compiled, using Lean 4.32.0, `-M6000 -j1 -DElab.async=false`, private symlinks, and a 512 MiB disk reserve; maximum RSS was 1,826,296 KiB. No shared sources/objects or Git state were changed.

This supplies the substantive fixed equality-interpretation deductions. It does not yet prove a represented translation of arbitrary formulas/derivations, semantic validity of every helper-free seed, internal runtime calibration, or HA provability of the final equation/consistency equivalence. In particular, none of those conclusions is an input hypothesis to the new endpoints.
