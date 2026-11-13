# Expanded compact/iPRA rebuild: stage 276 failed

Stage 276, `ZFCinPA.NativeSchema`, exited 1 in 4.285 seconds with the error
that `InternalInterpretation.consistent_of_falsum_transfer` is unknown at line
187. No object or later stage was produced. The source and direct dependency
guards remained unchanged. The failed receipt and full compiler log are
retained; no warning exception is applicable.

The current workspace source `ZFCinPA/InternalInterpretation.lean` defines
that declaration at line 618. However, `ZFCinPA.InternalInterpretation` is
not one of the 425 rebuild candidates: this cone was determined from selected
serialized import edges, not declaration-level freshness. Its selected
pre-existing object does not supply the new declaration to this compile. This
is evidence of a source/provider mismatch, and the prefix through stage 275
cannot by itself establish a current-source-coherent endpoint. Rebuilding that
provider may require a larger reverse dependency cone; changing the client
instead would require a separately pinned source correction and proof review.

Runner SHA-256 is
`f2b3dbea1661fc4702625bafcd7aa474227f4d73b3d77a7cb08cee0098df9788`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,510,968 KiB; brief children and overlap can be missed. The author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
