# Exploratory model clean-phase support

`CleanMaskClasses.support_subset_bad` proves that the exact symbolic low-mask support lies inside the compact blocker B from `compact44-clean-phase-geometry-prototype`, replacing that packet's external support-inclusion observation with a Lean theorem. The module also establishes the ordinary and absent symbolic low-mask digit formulas for every standard j<8807 in arbitrary IΣ₁ models.

`CleanModelSupport.zero_outside` assumes `NoCarry (dig 67 C k) (dig 67 lowNat (k%8807))` for every positive k<n, and proves that every k<n whose phase is outside B has digit zero. `boolean_away_special` assumes the same positive-index NoCarry and separately `dig 67 C 0≤1`; it proves that each k<n whose phase is not 1063 has digit at most one. The proofs lift each bounded model phase to a standard numeral and explicitly handle k=0. These are conditional model lemmas: the same-witness graph source for the NoCarry and origin assumptions still needs to be joined on a coherent provider.

Author-only sessions 94915 and 94651 actually exited 0 without warnings or `sorryAx`; named reports use `propext`, `Classical.choice`, and `Quot.sound`. First session 10627 actually exited 1 due to parser syntax and is retained as a failure. These compiles use the graph-temporal/carry author provider with the locally compiled geometry module from commit d90510c1bd; they are not a paired replay or independent artifact audit.

No selection of model predecessor positions, fractional-temporal half-radix bound, clean-carry reset, graph-column decoding, retained-K binding, machine or internal iPRA result is claimed.
