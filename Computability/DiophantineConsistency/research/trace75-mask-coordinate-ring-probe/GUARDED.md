# Positive witnesses on the guarded charts

`Trace74GuardedIff.guarded_positive_zero_iff` is Lean checked in every
`IΣ₁` model for arbitrary natural ports. It equates:

* a positive trace75 valuation with `F + alpha < q` and trace75 ring value
  zero in the model's difference ring; and
* a positive trace74 valuation with `F + C < q` and trace74 ring value zero
  in the same difference ring.

Both sides retain their own explicit guard. The coordinate map sends either
third coordinate to `q - F - third`, is involutive under that guard, and
preserves positivity and the other side's guard. Neither guard is proved from
a zero here. In particular, the theorem does not identify an unguarded
trace75 zero with a guarded trace74 zero, and it gives no unconditional
consistency, halt or iPRA equivalence. The result concerns the Lean-defined
ring values; converting their displayed/JSON descriptions into Lean syntax is
an external boundary described in `README.md`.

`Trace74Guarded.guarded_to_old` is the one-way transfer and was checked with
`run-guarded-v4.py`, accepted `observations/guarded-attempt04/`, object
`/tmp/trace74-guarded-x79wd3vc/Trace74Guarded.olean` SHA-256
`9729356ff22b501454abbd77b7319bb00b222f83a6a4b79404ebef93281dceda`.
Source SHA-256:
`d820b1dd2c11fd246ef0df5518f25a249b63213daf78f716a9032272362587c8`.
The two-sided theorem passed with `run-iff-v2.py`, accepted
`observations/iff-attempt02/`, object
`/tmp/trace74-iff-bilwy87m/Trace74GuardedIff.olean` SHA-256
`841fa8255b84d3b6e9de8cf0ce25c995c6c94e8fd5ee6694b48803e994fec255`.
Source SHA-256:
`df80dc6159d3006652bfb039d8c97d2af0e92910a28ccb9979a0e4e776df4efc`.
Both report `[propext, Classical.choice, Quot.sound]` as Lean axioms.
The earlier failed attempts retain their source snapshots and diagnostics.

The runners pin direct selected providers, record resource samples and apply
the 8-GiB/two-Lean-process guard. Lean selects project modules by their shared
namespace: the guarded runs use a fresh overlay of symlinks into the existing
project library, plus the freshly compiled trace75 module. The direct hashes
are recorded, but transitive project, package and dynamic ancestry remain
inherited; no complete selected-closure audit or independent replay is claimed.
