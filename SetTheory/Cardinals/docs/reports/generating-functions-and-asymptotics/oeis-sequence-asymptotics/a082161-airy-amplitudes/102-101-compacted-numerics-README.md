# Optional numerical diagnostic

`compute_canonical_amplitude.py` evolves the signed gauged recurrence through n=3000 using NumPy and SciPy tridiagonal eigensystems. It prints projection masses, finite product factors, and uncorrected diagonal normalizations. The companion exact-integer diagnostics are under `checks/formal/diagnostics`; their source dynamic program is supplied in the unchanged relaxed source archive.

These are floating-point diagnostics only. They are not interval certificates, do not certify the decimal amplitude, and are excluded from the exact acceptance replay. The saved log records a completed run; different numerical-library versions can change its last digits.
