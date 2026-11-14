Shared-grammar mixed-integer experiment
=======================================

This optional experiment requires Python, NumPy and SciPy with HiGHS.
The main machine reconstruction and universal audits do not require these
dependencies. All inputs used here are included under inputs/; the compiler
and physical support routines are taken from ../../construction/vendor/.

From this directory, on a separate working copy if keeping original logs:

  python3 min_grammar.py 180
  python3 sample_milp.py

The first program writes milp_result.json. The second reads that file and
samples binary associations for 120 seconds, writing improved trees under
samples/. Both overwrite corresponding result files. Wall-clock limits and
the solver environment can change the exact number of iterations and result.
The random association stream has fixed seed 1428.

The model prices a repeated-substring straight-line grammar for a fixed
190-token emitter, with the existing two- and four-increment subtrees free.
It has 226 candidate word rules (including the root), 5,708 binary variables
and 5,565 constraints. The retained 180-second run found objective 67 with
solver dual bound 61 and an unresolved gap of about 8.955 percent. Thirty
rules were selected. This is a restricted optimization result, not a proved
minimum for the model and not a lower bound for physical machines.

The retained 15,482 sampled associations reached best projected count 198
(201 raw controls and three compatible folds). No candidate at or below
193 entered the later whole-machine validation stage. A discovery score is
not a verified machine. The result illustrates the need to optimize grammar
sharing and fold compatibility together.

Portability edits replace the original scratch paths by the paths above.
They do not alter the objective, input data, seed, stopping time, or search
logic. The actual historical outputs and logs are preserved separately.
