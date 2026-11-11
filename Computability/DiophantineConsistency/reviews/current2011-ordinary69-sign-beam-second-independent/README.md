# Independent review of the 69/84 sign-pair beam

The recorded deterministic beam reproduced byte for byte. It has four starting graphs, ten iterations, up to 160 retained states per depth, and admits intermediate graphs of at most 71 live gates. No visited graph used fewer than 69 gates. This is a bounded, nonexhaustive beam; it does not establish a global minimum or a new candidate.

The pinned 69-row graph is topological and has the stated witness and fixed-numeral interface. The three subtracted norm factors have unique canonical nodes and each is used only in the indicated product `X=N0*N1*Nt`. Reversing any two of them changes each factor's sign and leaves X unchanged; therefore the complete output remains exactly the same. The earlier independent graph/degree audit and the independent 731-case, 1,056-instance exact rewrite-template audit were rerun. The engine's positive control also checks 3-to-2 common-product factoring.

These are external graph and search checks; they are not a new Lean theorem or a binding of external JSON, TeX or PDF semantics. Run the checker from the repository root with `python3 -I -S -B Computability/DiophantineConsistency/reviews/current2011-ordinary69-sign-beam-second-independent/check.py`.
