# Preventive direct tactic import for the 74 strict-guard client

This inert `.lean.src` snapshot is the reviewed `OwnZeroGuardStrict74.lean`
with exactly one line prepended: `import Mathlib.Tactic.LinearCombination`.
Its proofs, namespace, statements and all original clients are unchanged. The
source uses `linear_combination` to turn the own-zero guard unit into the
balance consumed by the strictness fact; the direct import makes that tactic
requirement explicit for this standalone module.

The recorded project-source header graph contains no observed route from this
module to that tactic, but package and Foundation source leaves were not fully
expanded. Thus transitive availability remains unverified: this is a preventive
patch, not a confirmed missing import or observed Lean failure. The object at
the selected package path is only a point-in-time presence/hash observation,
not proof of coherent providers. The existing reviewed root74 source chain and
receipts remain unchanged. Any future adoption requires a separately reviewed
source overlay, updated dependency inventory and guarded build. No Lean run,
verified iPRA endpoint or physical byte/PDF binding is claimed.

Independent source review: [74 guard tactic import](../../reviews/ordinary14-74-guard-linear-combination-patch-independent/README.md).
