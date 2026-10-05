# Floating-point sanity only

`profile_sanity.py` evaluates the profile in report106 at n=2048 and n=4096,
with its actual fixed cutoff M=1024. It fills singleton gaps, chooses a midpoint
integer in each triangle's outgoing-margin interval, applies all moves, and
recomputes outgoing/incoming margins and entropy.

The script uses ordinary NumPy float64 operations, explicit exceptions and an
absolute tolerance of 1e-8 for consistency checks. It is not a rational fixture,
a directed-rounding proof, or a certificate of transcendental inequalities.
In particular near-integer floating results are not exact integer margins.
The exact finite fixtures are in the separate `checks/` directory.

Run from the package root:

    python3 sanity/profile_sanity.py --output sanity/profile_results.json

NumPy 2.3.5 was used for the recorded result. Different numerical libraries or
platforms may differ in their final bits. A passing sanity run is never used as
an input to the mathematical theorem or the exact verifier.
