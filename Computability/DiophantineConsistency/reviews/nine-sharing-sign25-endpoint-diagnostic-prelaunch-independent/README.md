# Independent prelaunch review of split endpoint diagnostic

`python3 -I -S -B check.py > result.json` completed with observed outer exit
0. The independent check compares the four source files with their draft and
manifest hashes, verifies their single-import chain and intended declarations,
and reconstructs the diagnostic runner by applying the stated substitutions
to the previous endpoint runner in memory. It checks the framework survey and
runs the diagnostic no-Lean preflight. The runner retains the previous guarded
resource limits and a distinct output directory.

The four stages test import of the existing bridge, naming the expression,
proving its typed bridge, and printing its axioms, respectively. The changed
import boundaries mean success or failure of a stage will not by itself prove
the exact cause of the original memory exception. This prelaunch review is not
Lean elaboration and establishes no new iPRA endpoint. The earlier provider
point-observation and inherited-ancestry limitations apply. Lean may run only
on the assigned exclusive slot after the runner's own resource checks.
