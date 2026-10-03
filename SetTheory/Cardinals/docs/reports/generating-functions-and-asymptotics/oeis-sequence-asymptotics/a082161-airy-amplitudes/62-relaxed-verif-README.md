# Additional independent verification

This directory contains a mathematical verification review, the final integrated-source signoff, and two freshly implemented symbolic/numerical checkers. They do not import the main package's mathematical checkers. Their algebra is independent of the main checker implementation, although they use the same standard mathematical libraries.

Files:

- `mathematical-review.md`: analytical review from exact recurrence through the endpoint and all-orders arguments
- `transcription-signoff.md`: comparison and signoff for the exact delivered TeX/PDF hashes
- `check_formal_independent.py`: nonautonomous recurrence through epsilon^8, boundary/derivative conditions, grading, and coefficient conversion
- `check_frozen_and_spectrum.py`: frozen Airy residual through epsilon^5, exact gauge endpoints and recurrence identities, and nonrigorous spectral diagnostics
- `expected/`: immutable reference JSON results from these independent calculations

From the package root, run:

```sh
python verification/run_checks.py
```

The runner verifies the complete package input manifest before and after both checks. It writes only beneath `output/verification/` and checks the results against the reference JSON files. Formal outputs compare exactly; spectral floating-point entries use a regression tolerance of relative 1e-7 and absolute 1e-9, not a mathematical error bound.

The individual commands are:

```sh
python verification/check_formal_independent.py
python verification/check_frozen_and_spectrum.py
```

They use the same dependencies listed at the package root. Do not use Python's `-O` flag. The two checkers differ from their original verification runs only in an assertion-safety guard and a relocatable output destination. Their mathematical calculations are unchanged.

These finite computations supplement the analytical proof. They do not certify a uniform norm remainder, the global spectral gap, the amplitude's decimal digits, or an integer threshold near a tie. The review is technical verification of this manuscript, not external community peer review or formal proof-assistant certification.
