# Exploratory selected clean source phase

`CyclicPhaseTransport.cyc_period` proves in every IΣ₁ model that for `m,N>0` and `d<m`, the full-word cyclic predecessor reduced modulo m equals the corresponding phase predecessor: `cyc (m*N) k d % m = cyc m (k%m) d`. The lemma is for arbitrary k and does not identify a zero-padded next digit with a cyclic digit.

`CleanSafeSource.safe_source` combines this transport and the prior model neighbor exclusion: given a source digit whose phase is outside B, plus the explicit zero/Boolean support hypotheses, its digit is zero and its first two full-word cyclic predecessor digits are Boolean. `choose_source` uses the two-target phase geometry to select one of two supplied in-range indices with these properties; its two index-to-phase equalities are explicit hypotheses. No temporal-rotation source-index relation or temporal digit bound is asserted.

Author-only compiler sessions 10213 and 73251 actually exited 0 without warnings or `sorryAx`; reports use `propext`, `Classical.choice`, and `Quot.sound`. Initial session 67396 exited 1 because a modular-divisibility lemma was unavailable; its source and log are retained, and its `sorryAx` report proves nothing. The same fresh author overlay and dependencies documented in commits 9403a827c7 and 778847d293 were used. This is exploratory evidence, not a paired replay or independent artifact audit.

No same-witness temporal source-index derivation, half-radix predecessor bound, clean-carry reset, graph-column decoding, retained-K binding, machine or internal iPRA theorem is claimed.
