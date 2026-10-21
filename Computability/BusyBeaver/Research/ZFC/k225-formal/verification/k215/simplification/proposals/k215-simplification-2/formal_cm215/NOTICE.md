# Attribution and status

The primary K215 and CM215 tables, the conditional-marker transformation,
and their ordinary mathematical calibration are prior ProveIt work. This
packet does not claim the machine or the six-row rewrite as new. CM215 is
`Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/conditional-marker/`
in the pinned upstream repository.

The new contributions in this packet are the strengthened one-step invariant,
the generic positive-step transfer lemma, its core Lean formalization, the
literal-table kernel instantiation, and the direct bridge/integration artifacts.
The independent Python finite checker is corroboration only.

The six files under `vendor/` are unchanged ProveIt sources, identified by
`upstream-pins.json`, and remain covered by their original MIT-0 license in
`vendor/LICENSE.ProveIt`. The parent K215 endpoint depends on additional work
whose attribution and licenses remain in the original repository. This packet
reuses that endpoint; it does not replace or relicense the full proof ancestry.

New code and prose in this packet may be incorporated into ProveIt under
MIT-0. Exact compile scope and the uncompiled full-ZFC adapter boundary are
stated in README.md and the retained build receipts.
