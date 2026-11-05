# Independent matrix import-order probe audit

The retained evidence supports the two reported failures: Foundation-first
and Mathlib-first each produced an actual Lean exit 1, empty stderr, no object,
no monitor stop, and the respective `Matrix.map` / `Matrix.map.eq_1`
duplicate-declaration diagnostic. The outer runner's exit 0 records successful
collection of these expected failures, not a successful Lean build.

[`audit.py`](audit.py) independently checks the exact frozen packet hashes,
child/session receipts, resource observations, copied and original sources and
logs, all 20 current direct provider companion guards, and the stated source
chains and colliding declarations. It checks raw import lines and source
hashes; the original trace also strips comments. No Lean or probe was run.
Transitive source-to-object correspondence, dynamic loading and transient
changes remain outside the evidence.

A source-only exploration initially missed a separate route because it
omitted the `Diophantine.*` namespace. Including it finds
`CurrentMasks2011 → NativeSourceMask → NativePopulationLower → NativeHalfBinomial →
Diophantine.Paper1980.PellRatio90 → … → Diophantine.Paper1976.Wilson →
Mathlib.NumberTheory.Wilson → … → Mathlib.LinearAlgebra.Matrix.Defs`, even
when direct blanket `Mathlib.Tactic` imports are suppressed. Therefore merely
narrowing the blanket tactic imports cannot resolve all observed source routes.
This is a source-import observation, not a complete closure proof or a tested
repair. The new base-only client route should be assessed separately.

Run the independent read-only checker with `python3 -I -S -B audit.py`.
