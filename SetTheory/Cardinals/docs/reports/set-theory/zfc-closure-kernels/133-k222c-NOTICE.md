# Attribution and licensing

This contribution was prepared for Vladimir Reshetnikov's ProveIt repository. New prose, scripts and certificates use the MIT No Attribution license in `LICENSE`. Existing components retain their original terms; this notice does not replace those terms.

The exact direct predecessors are the two incoming `K223_Construction_2026-10-20` ZIPs at ProveIt commit `076445a2664854d817f8a938731dcacc290dcd7b`. They are preserved byte for byte as `portable/vendor/G223_parent.zip` and `portable/vendor/Seed223_parent.zip`. Their reports, provenance, nested predecessor archives and license notices remain intact.

The K theory, seed presentation, K0 quotient interpretation, formal source and K230 calibration are due to Elliot Glazer and the credited predecessor developments. The upstream `k230-rocq` commit is `3142e4dd980f0be12f4abb636c4ae2528afc17eb`. The inherited architecture also credits ProveIt, Mira, Jeff's busy-beaver development, Andrew James Wade, BusyCoq, LibTactics and the Coq Library of Undecidability, as recorded in the preserved packages.

The equality/helper merger and G223 table belong to the G223 predecessor. The use of the witness-request formula as an emitted axiom and its 223-state source grammar belong to the Seed223 predecessor. The new contribution composes these transformations, proves the exact seed-order bundle comparison, constructs the 208-subtree source and 222-state table, and verifies their exact source, decoder, blank-tape and unbounded runtime obligations.

`portable/theory/review_logic.py` is copied unchanged from G223. The source builder imports the unchanged Seed223 source-language and macro-bisimulation utilities from its original ZIP. The runtime checker imports the unchanged G223 symbolic runtime and independent unary-frame helper. The standalone binary compiler adapts the documented decoder-reuse strategy from Seed223, with explicit final-source and final-table checks. All copied or adapted materials retain their ancestry and applicable license notices.

No new end-to-end Rocq or Lean theorem for the final 222-state bytes is claimed. The ordinary mathematical proof and executable certificates are described at their actual scope in the report.
