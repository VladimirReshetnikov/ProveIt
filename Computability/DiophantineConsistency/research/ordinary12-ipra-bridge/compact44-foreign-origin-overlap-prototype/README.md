# Exploratory obstruction to shifted single-band decoding

`ForeignOriginOverlap.selector_origin` proves in an arbitrary IΣ₁ model that a selector whose reflected offset is in range reads `C[0]` at its own offset column. In particular, `overlap_5488` proves that for `5488 < n` and `C[0] = 1`, selector 7 of the 5495 band at column 5488 equals 1. Column 5488 is the 4393 target shifted forward by the occupied source offset 1095. Thus the selector family of the other band is not all zero there; the previous single-band vanishing argument cannot be used at this column.

`ForeignPhaseMask.shifted_mask_zero` proves in the model that the symbolic high-mask digit at 5488 is 0. The local decoder argument previously used high-mask digit `2^51-2` at 4393 or 5495; it cannot be applied at 5488 using the same mask premise. This is an obstruction to that particular proof route, not a contradiction in the graph or a proof that no other decoding method works.

The author-only checks compiled `ForeignOriginOverlap` then `ForeignPhaseMask` over the same overlay as `8d1f182e38`. Sessions 65603 and 13456 actually exited 0 without warnings or `sorryAx`; named axiom reports are retained. These are exploratory results, not a paired replay or independent artifact audit. No claim is made about retained port/K binding or machine semantics.
