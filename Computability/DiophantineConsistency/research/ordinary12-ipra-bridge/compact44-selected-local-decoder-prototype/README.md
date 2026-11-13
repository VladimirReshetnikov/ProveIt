# Exploratory selected fixed-graph local decoder

`SelectedBandDecoder.decode` applies the existing 943-row local coefficient decoder to a selected band with explicitly bounded Boolean selector and copy digits, copy word below `2^41`, and the exact local `NoCarry` premise. Its conclusion is precisely either all 943 selector digits and the copy word are zero, or one selector satisfies `CompactSelectorSum.Selected` and the copy word equals that row's `Compact943Decoder.tileValue`.

`FixedGraphSelectedDecoder.graph_selected_decoder` combines that local decoder with the previously derived same-witness selected graph band. Assuming positive graph coordinates and literal graph zero at fixed symbolic ports with `paramKernel rho`, it retains the same N,w,t, indexed b=1 `CarryInput`, temporal and zero-carry facts, selected-band identity, Boolean/copy-word bounds and exact local `NoCarry`, and adds the decoder alternative for t=4393 or 5495. This is a conditional local graph consequence; it does not assert that a graph zero exists.

Author-only sessions 68556 and 69493 actually exited 0 without warnings or `sorryAx`; named reports use `propext`, `Classical.choice`, `Quot.sound`. Session 65193 actually exited 1 on a numeral-cast rewrite; its source/log and failure-derived `sorryAx` report are retained. The same author overlay and source chain from commits 9403a827c7, 9c585b5828, db88bbcec8 and 67875af13e were used. This is single-author exploratory evidence, not a paired replay or independent artifact audit.

No whole-word row correspondence, adjacency or machine-simulation theorem, retained K/port-byte binding, machine equivalence or internal iPRA result follows here.
