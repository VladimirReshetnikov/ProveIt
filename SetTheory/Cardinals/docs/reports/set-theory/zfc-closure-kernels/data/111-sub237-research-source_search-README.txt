SOURCE AND CONTEXT-REPRESENTATION SEARCHES

These are discovery experiments. No sub-237 binary machine resulted.
The original source cost is 224 hash-consed nodes: 201 internal nodes and
23 distinct whole-instruction leaves. This is not a binary TM state count.

boundary_source_input.json retains the exact source DAG input. The array
also contains historical nodes; only nodes reachable from root are charged.
boundary_sites_input.json is the 6,455-leaf calibrated source. The source
invariant and proof permitting replacements are in ../source_abstraction/.

Run the exact finite substitution search from this directory:

  python3 -B dontcare_search.py

It exhausts the stated family of 1,204,224 combinations of four/six
forced-zero instruction choices and two original-subtree choices. Its best
cost is still 224. A best-source file is written only on an improvement;
the delivered dontcare_best_receipt.json records the completed negative run.

The two timed source searches use only proven local source transformations:

  python3 -B explore_nonmonotone.py --seconds 600 --seed 196237 \
    --output nonmonotone
  python3 -B explore_affine.py --seconds 600 --seed 236704 \
    --output affine_nonmonotone

exact_reassociate.py supplies the source signatures and control-preserving
rotations. affine_swaps.py supplies exact affine-transform commutations.
Runs permit temporary source growth; final acceptance still requires at
most223 nodes and zero-run length at most6. Time-bounded proposal counts
depend on machine speed. Saved receipts/logs describe the actual runs.

simplified/ contains the certified source-loop contraction, its source DAG,
the old/new instruction correspondence, and a 360-second reassociation run:

  cd simplified
  python3 -B explore_nonmonotone.py --seconds 360 --seed 163237 \
    --output simplified_nonmonotone

Its 316,755 proposals do not improve on225 source nodes. The contraction
has6452 leaves, but costs202 internal nodes instead of201. One-step loop
stuttering and the complete surviving-edge correspondence are explained in
the report; this source change was not compiled to a smaller binary table.

The three context_split*.cpp programs synthesize four binary rows with a
context-dependent representation of one deleted state. Compile with C++17,
then pass a table and finite profile:

  c++ -O3 -std=c++17 context_split.cpp -o /tmp/zfc-context-split
  /tmp/zfc-context-split ../binary_search/input237.tm \
    ../binary_search/profile237.txt > /tmp/zfc-split.out \
    2> /tmp/zfc-split.log

context_split_mirror.cpp reverses the entry direction. The general version
expands compatible retained-control choices and stops after600seconds;
its delivered log is a partial search, not an exhausted family. The
*_source logs use ../binary_search/source_profile237.txt. Any output would
need a separate unbounded simulation proof and a new startup check.

The reassociation checker/input originate in the pinned 238-state intake,
with the new bounded exploration and context-representation synthesis added
in this supplement. Original repository notices are in ../../licenses/.
