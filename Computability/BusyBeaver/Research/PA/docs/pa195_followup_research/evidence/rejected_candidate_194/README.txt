REJECTED 194-state local quotient
================================

These files do NOT define a validated PA-consistency machine.

The literal quotient has 194 working states, 388 binary rows, the same
3,700-site source CFG, and eight compatible local folds. Its source
encoding nevertheless contains a seven-zero run that the old scanner
mistakes for a separator.

The first failed raw runtime contract is source ordinal 1003, the zero
branch of logical register 1 (physical register 2), after 1,309 successful
earlier branch contracts.

The top-level verify_rejected.py reconstructs the local quotient and
then checks that this exact runtime failure occurs. The accepted
machine_195s8 version pays one scanner state to repair the whole runtime.
