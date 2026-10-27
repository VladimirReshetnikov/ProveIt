# Next checkpoint: literal shifted-z source adapter

Read-only proposal, 26 October 2026. No generator, compiler or incoming
program was run for this proposal. The frozen ordinary-source construction
is now available; this note proposes the next separate module, not a
historical small-front transfer or a new equation metric.

## Exact identities and positive domains

Suggested new `NativeShiftedSourceAdapter` imports the frozen
`NativeOrdinarySourceConstruction` and `NativeArithmetic52`. Define, for
an arbitrary commutative ring R,

```lean
def toOld (x : Fin 31 → R) := Function.update x 3 (x 3 + 1)
def toNew (x : Fin 31 → R) := Function.update x 3 (x 3 - 1)
theorem rows_toOld (p : Fin 4 → R) (x : Fin 31 → R) (j : Fin 22) :
    SplitCertificate59.sourceRows p (toOld x) j =
      NativeQuadraticParent.sourceRows p x j
```

All 22 identities are literal ring identities, without positivity,
coefficient, source-zero or canonical-witness premises. The finite row
order is the original order, not either package's delivered row permutation.
Only original row14 (zero based) mentions coordinate3. It changes
`(K+w)C-F-(q-1)(z_old-1)` to `(K+w)C-F-(q-1)z_new`.
The remaining rows, including rank row13, are unchanged. Prove the two
function-update maps inverse over R, with a companion `rows_toNew` obtained
from `rows_toOld`; no certificate assertion replaces these identities.

The reverse **positive** direction needs a separately derived strict bound:

```lean
-- Proposed; not yet compiled.
theorem source_old_z_gt_one
    (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : NativeSourceMask.Interface p d MC MF)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun i => (x i : ℤ)) j = 0) :
    1 < x 3
```

This lemma does **not** need `MC % 4 = 2`, a Carrier65 zero, or a chosen
canonical source. Its proof uses the same supplied x:

1. `NativeSourceMask.source_gap_bounds p hi.portBox x hx hs` gives
   C=gap>0 and F<q=sourceQ.
2. `ThirteenCarrierComplete.source_spatial_gt_base p hi x hx hs` gives
   w=x10>q. This theorem is already a direct source consequence.
3. `NativeSourceWindow.source_transport_identity` gives the natural
   identity `(K.toNat+w)*C=F+(z_old-1)*(q-1)`.
4. Since C>=1, `(K.toNat+w)*C>=K.toNat+w>=w>q>F`.
   If z_old<=1 then its natural predecessor is zero and the right side
   equals F, a contradiction. Hence z_old>=2.

Thus integer `toNew` preserves strict positivity for every positive old
source under the interface. Integer `toOld` preserves positivity
unconditionally. Positive integer vectors convert to natural vectors by
`Int.toNat`, with each cast equality proved from coordinate positivity;
there is no truncated negative-coordinate conversion. Alternatively a
natural predecessor update uses `Nat.sub_add_cancel` only after the bound.

The generic existence theorem can therefore state, with only `hi`,

```lean
(∃ x : Fin 31 → ℤ, (∀ i, 0 < x i) ∧
    ∀ j, NativeQuadraticParent.sourceRows p x j = 0) ↔
  NativeOrdinarySourceConstruction.PositiveSource p
```

At the current once-shifted ports, compose this theorem with the already
frozen `current_source_iff_not_conZFC` and `no_current_source_iff_conZFC`.
This provides an external Lean equivalence for the literal shifted source.
It does not identify arbitrary ordinary private seeds with canonical ones.

An economical final corollary can use the existing
`NativeArithmetic52.exists_positive_zero_iff`. Its left side is exactly
the shifted source above. Its right side is

```lean
∃ v : Fin 16 → ℤ,
  (∀ i : Fin 31, 0 < NativeArithmetic52.lift p v i) ∧
  ∀ j : Fin 7, NativeArithmetic52.residuals p v j = 0
```

Retain **all31** lifted positivity conditions, including V and y²−V².
Do not replace them with positivity of just the sixteen inputs. There is
no claim here that this constrained16-coordinate endpoint is a new
unrestricted small-variable polynomial. Adaptive-carrier/free-J soundness
and canonical completeness are still separate later work.

## Exact prerequisites and bounded build proposal

The current direct custom closure of `NativeArithmetic52` has seven
modules, not the preliminary ten counted in the earlier transfer audit.
Four are already source/object authenticated in the frozen ordinary-source
provider: `SidonPositions`, `QuadraticFiber`, `QuadraticCoding`, and
`SelectiveQuadraticCoding`. This is a corrected static inventory; the three
missing module names themselves are unchanged.

| Fresh prerequisite, in order | Source SHA-256 | Lines |
| --- | --- | --- |
| SelectiveCertificate52 | `19d0987f82005b0f978562679ebe4b6ec511df334a211cc3aeff49f3e27c9872` | 128 |
| NativeQuadraticParent | `6764c7bd216dabaf5338a245817d7297e14f152aa0c033d2b766aba472c38509` | 661 |
| NativeArithmetic52 | `b0cb8b658d200933cc47fc71aee016efd6bdad95a4926b377b794be95b49aada` | 376 |

No objects for these three were found in the worktree central cache, its
DiophantineConsistency subproject cache, or the central source checkout
cache. No accepted receipt authenticating them was identified. This is
not a claim to have searched every temporary directory. The safest proposed
path is to freshly build these three, in this order, in a new private
overlay after authorization and complete source review.

The combined future overlay can reuse the364 authenticated custom modules
plus the freshly accepted `NativeOrdinarySourceConstruction` main:365
cached modules. It needs only three fresh prerequisites and the new
adapter/check pair. Seven of the eight explicit Mathlib names in the
seven-module legacy closure, plus implicit Init, already occur among the64
authenticated boundaries. `Mathlib.Tactic.LinearCombination` is an
additional explicit boundary for `NativeArithmetic52`; this raises the
union to65. Its current source/primary observations are respectively
`a59009a15dc914d2774e01cfb1afcbf6490e9e1015587f2ab89c22a2778f2e6d` and
`e4487ef3e033c8a8cfe8562ee7a96d2926444bd73c7f138f265b58a8d1d14c08`.
These two hashes are observations, not yet a prior source/object
authentication receipt: no such prior explicit pin was found in the
inspected native/root receipts. Resolve this boundary explicitly before
compilation, including its companions; do not silently treat it as one of
the64 already authenticated names. Alternatively, the ring/positive source
adapter alone imports `NativeQuadraticParent` and needs only its two fresh
prerequisites, deferring the optional16-coordinate corollary. Existing focused
`checks/NativeQuadraticParent.lean` and `checks/NativeArithmetic52.lean`
may also be replayed as two small explicit commands; they are not new
prerequisite modules. No Foundation or whole native closure rebuild is
needed. Reauthenticate every selected source/object and package boundary
before/after; keep `-M6000 -j1 -DElab.async=false` and the512MiB reserve.

The exact new provider is `/tmp/native-ordinary-source-onjq2zfu`, input
manifest `5a5833081c2167e5b7ad8b150fff7306f8a6cdfddf678c2c4f8e239a0bceee13`.
Its new main source/object pins are respectively
`95e7a8cd4d2dd8f64554cbd9273d96e9629d12583f111cc0b89bee325712838b` and
`67c28fd51812ecf959df72aaa46cbdaa243ea629c860ffd57fe5808fe6fc49d8`.
Its durable replay is
`c73617b3fd69519347f1b329b2167d2be394ec974ee17bbe7a540417c5d65d2b`.

## Inert source/builder bindings

The generic Lean rows, not a historical coefficient binding, are the
authority for the proposed adapter. The source JSON contains60 binary
gates and22 comparisons; transport is literally gates45–48, with
`g47=beta*J*z_new` and `g48=F+g47`. The generator was read but not executed;
it would overwrite the accepted parent source and is unnecessary here.

| Path relative to DiophantineConsistency | SHA-256 |
| --- | --- |
| scripts/generate_native_quadratic_parent.py | `432c9ce82523d9aff4517a17f94ea477701dc26caf906d9fafec248c8122e319` |
| data/native-quadratic52/source_system60.json | `ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48` |
| con-zfc-diophantine-forms/52-sparse-pell/packing/CERTIFICATE_174_interior_regular.json | `c1740ad4de5142143ee7282a8229fe6e76e26a74128846cba9b2212e1b27033c` |
| Lean/checks/NativeQuadraticParent.lean | `45b0a9a2fd4a06c3a638cbc22a3af0a9373419def2113af3ef4aa9e07abfee80` |
| Lean/checks/NativeArithmetic52.lean | `b49286d209f72004cab9ba7e4398c77f7951f684dfc6103be8ad95cdc2ef839e` |

The source/check files, generator, exact row definitions and relevant
transport/domain contracts were inspected read-only. This note does not
claim a new full review or fresh validation of every generated quadratic
extraction proof or certificate record. Before any new prerequisite build,
read the entire remaining generated proof source and authenticate its
current bytes. The frozen authoritative old-z `SplitCertificate59` source
is SHA `0b6082b0af3f092f6914263eb1568da1d3730df24032b6c1dff5489875da0a03`.
