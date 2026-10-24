# Eleven-positive Pell reductions

Proved relative to the pinned native/compiler and weighted Pell interfaces:

- p11_positive_degree277.json: exact degree277, 111 binary operations.
- p11_positive_degree257.json: exact degree257, 114 binary operations.

Both use the same eleven strictly positive unknowns and whole compact44
fixed coefficient tuple. PROOF.md gives the denominator-guard deletion;
CENTERED_PROOF.md proves the new centered sign bootstrap. section.tex is the
integrated report section. The ordinary mathematical proof boundary is
explicit: neither construction supplies a new end-to-end formal calibration.

Reproduce using Python3, standard library only:

    python build.py
    python build_centered.py
    python verify.py
    python verify_centered.py
    python -O verify.py
    python -O verify_centered.py
    python check_new_lemmas.py
    python -O check_new_lemmas.py

The component is self-contained. SOURCE_PINS.json retains byte-authenticated
earlier semantic and coefficient inputs. COMPOSITION_SOURCES.json identifies
the recent source69/source70 composition at ProveIt 2605669a532342f153b13eb6b4a0af4b54f5fa37.
All fixed coefficient payloads are included. MF is already shifted.

FOUR_ROOT_LIMITS.md records failed intermediate inferences, not a new
ten-variable endpoint. No global minimality or unconditional novelty claim
is made. Existing nine-positive universal encodings use fewer variables at
much larger degree; no single ordering makes these uniquely smallest.
