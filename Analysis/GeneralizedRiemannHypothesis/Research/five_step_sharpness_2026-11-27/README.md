# The five-step sharpness classification

This is an addendum to the 26 November five-step graph-tower report. It
settles exactly which primes attain the universal five-step upper bound
and classifies extremizers at 11 and 31. It also gives the exact maximum
at 131, with or without zero residues. The result is unconditional.

- Compile: pdflatex five_step_sharpness.tex (twice).
- All-primes certificate: python3 verify.py
- Independent full search at 131: python3 benchmark_131.py

Both replay scripts use Python 3.8+ and only the standard library.
The two text files record the expected output. The older search routine
is bundled as replay_previous.py so that the 131 benchmark is standalone.
