# Verification interface and certificate generators

Run `python3 verification/reproduce.py` from the package root for the combined
check. It does not regenerate invariants or rerun the exploratory searches.
The exact input hashes and output receipts bind the finite certificate checks
to the bundled source program and literal machine.

`core.py` implements the original symbolic frame with one register-file effect.
`flexible_core.py` installs a different box oracle and should be imported only
after ordinary checks, or in a separate Python process. It uses full numerical
intervals from the reduced joint invariant, tracks repeated register updates,
and permits additional spare registers and a larger final gap. Both are Python
verification components, not Lean proof objects. The generalized executor's
soundness is not inherited automatically from the upstream Lean executor.

The three independent certificate checkers check seed inclusion and closure
under every abstract source transfer. They do not rely on the C++ discovery
algorithms. The numerical infinity marker in the C++ files is converted to
genuine infinity in the independent Python difference-bound checks.

To reproduce discovery of the difference-bound and reduced-product invariants,
use a copy of the package if preserving the delivered receipts, then run from
the `verification` directory:

```sh
cd verification
g++ -O3 -std=c++17 dbm.cpp -o dbm_generator
./dbm_generator
python3 check_dbm_invariant.py
g++ -O3 -std=c++17 reduced_product.cpp -o reduced_generator
./reduced_generator
python3 check_reduced_invariant.py
```

The first generator reads `dbm_input.txt`. The second reads `reduced_input.txt`,
which contains the frozen source operations and initial mask/DBM product used
for narrowing. These input records are bundled so the generators require no
external paths. Whatever discovery procedure is used, the final certificate
must pass its independent check against the parsed pinned source.

The general theorem and its PA-formalization requirements are described in
`generalized_physical_contracts.tex` and the main report. A positive Python
receipt proves only what the stated executable model and its retained engine
lemmas justify; it is not a substitute for the missing sub-196 construction.
