502-BYTE GUARDED iPRA CHECKER
===========================

See PROOF-NOTES.txt for precise mathematical claims, inherited assumptions,
source attribution, comparison scope, and limitations. Run:

    python3 reproduce.py

code/checker_compact.py is the 502-byte complete compact program.
code/checker_guarded_exact.py adds exact alphabet and guarded public-goal
validation; its complete size is 1172 bytes. Both have matched controls
and actual proof/attack certificates. No mathematical axiom is deleted.

The complete theory and iPRA interpretation belong to the enclosing report.
