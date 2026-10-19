# Reverse path copier: valid-frame proof

Let the initial frontier be at c, the initial blank gap have length G>=n+2,
and the anchor be five consecutive ones followed by0. The n source fields,
in root-to-leaf order, have lengths b_i+3 followed by0. Exactly the last1 of
the final source field is erased; for n=0, erase the anchor's last1 instead.
The head enters on that erased cell. Arbitrary exterior cells may exist outside
the stated frame as long as the frame itself is unchanged.

After j completed iterations, 0<=j<=n:

1. Cells c through c+j-1 contain b_(n-1),...,b_(n-j), and c+j is a frontier1.
2. The remaining gap is G-j>=2.
3. The last1 of the rightmost unprocessed field is the sole erased source
   marker. If no source field remains, it is the anchor's last1.
4. All processed source fields and all other source cells are exact originals.
5. The machine is entering `restore` on the erased marker.

Restoring the marker and moving left reads two mandatory payload ones. A next0
identifies a length3 field (bit0); a next1 followed by0 identifies a length4
field (bit1). In either case the separator preceding this field has been found.
The immediately preceding field's last1 is erased, installing the next marker.
The left scan starts strictly left of that new marker. Every other separator in
the prefix is isolated, so the first pair of zeros encountered is in the blank
gap. The gap scan then reaches the rightmost1 before that gap, exactly the
frontier. It overwrites this frontier with the extracted bit and writes a new1
one cell right, consuming one blank cell. The gap still has at least two zeros.

The right scan crosses the nonempty anchor and all unmarked source fields.
Its first consecutive-zero pair is the newly erased last1 followed by its field
separator. It returns left onto the erased last1. Thus all five invariants hold
for j+1.

When the anchor itself is reached, after the two mandatory payload ones the
next two bits are both1 (the five-one anchor). No legal source field has this
pattern. Restoring the anchor leaves the head just to its left, in the blank
gap. A left scan over zeros reaches the frontier and returns one cell left of
it. No output bit is altered in this final scan. Therefore the machine writes
the reversed source word, preserves the full source, and returns at c+n-1.

Every iteration reduces the unprocessed-field count; each scan crosses a finite
valid interval, so the run terminates. The argument covers n=0, minimum gap,
all-zero/all-one words, and arbitrary finite source lengths. It proves the
forced-read guards used for pooling: restore reads0; payload1 and payload2
read1; both mark_previous states read1; append reads0.

## Mirrored selector/oracle composition

The source word is the four-bit rule number followed by an exact complete leaf
path. The reversed raw word is read root-first by moving left from c+n-1. A
mirrored twelve-state selector consumes the first four semantic bits and enters
the correct trusted template state. The mirrored 102-state oracle then consumes
the leaf path and emits its three-bit leaf code into c-1,c-2,c-3. Those cells are
blank by the query-frame contract, so all leaf-emitter reads are0. The common
return head is c-4. Selector bits and the frontier are unchanged; every original
unary source field is restored.

No external template-root port is used by the 133-state combined query table.
The valid caller supplies only the source-frame and its marked last cell. This
composition does not enumerate paths, check an actual arena, or search proofs.
