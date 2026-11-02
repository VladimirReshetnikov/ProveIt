# Exploratory model row and field transport

`CompactRowModel.lean` extends the standard-index theorem to any `IΣ₁` model: a model index below 942 is the cast of a natural `m < 942`; the actual `rowLookup` equals the cast of the corresponding row-index array entry; and any standard function `f` on compact row tuples with `f (0,0,0,0) = 0` has its model `compactField` lookup at that row equal to the cast of `f` applied to the translated old tile. The file includes the standard-row proof rather than relying on an unrecorded object.

The author-only exploratory Lean session 96268 exited 0, without warnings or `sorryAx`, with the four explicit reports `[propext, Classical.choice, Quot.sound]`. It used the author side of the independently audited compact lookup pair (`6354398167`) and the guarded Foundation package. No object or raw tool transcript was retained. This is not a paired replay or independent artifact audit.

The theorem does not yet identify the model's horizontal/vertical color lookup values with all four field values. Matching-neighbor conditions, wrap, all-model tiling transport, compact calibration, and the 12-variable iPRA endpoint remain separate.
