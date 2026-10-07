Report215 exact arithmetic

The certificate scripts use Python integers, fractions.Fraction, and the
256-bit directed interval primitives in certified_interval.py. No external
packages or network are used. The top-level README explains the full replay.

Dependency order: global bound -> operator constants -> exact radial values
-> operator values -> combination. The original infinite estimates and all
omitted tails are proved explicitly in the report. The large radial sieve
uses arbitrary-precision integer coefficients through 2^24, not a float fit.

The finite-model and saddle checks are supplemental checks with accurately
bounded scope. verify_arithmetic.py uses an independent positive-Taylor
rational exponential enclosure, rational four-operation probes, exact Horner
checks, and explicit exact-input API rejection tests. It does not replace a
proof of the interval primitives or the saddle remainder.

All exceptions are explicit and remain active in optimized Python. The
supplied semantic receipts exclude runtime and platform memory measurements.
Do not modify this frozen package to replay it: use the top-level runner or
make a separate copy for direct execution.
