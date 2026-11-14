# Other new experiments

Run the following commands from this `experiments` directory. These scripts
use the sibling `verification` modules and bundled pinned source extracts.
Outputs overwrite the corresponding experiment receipts.

## Classical-equivalent head and gate presentations

```sh
python3 classical_variants.py > classical.log
```

The 6,912 variants keep the first quantifier head and restricted implicational
bootstrap unchanged. They vary selected contrapositives, implication argument
orders, and gate associations. The dictionary-based parse score did not drop
below 68 raw AX grammar nodes. This cost is a heuristic compilation measure,
not a lower bound on binary TM states. `classical_results.json` preserves the
actual run and selected equal-cost candidates; none is a sub-196 machine.

## Register-engine mergers with a flexible spare tail

```sh
g++ -O3 -std=c++17 tail_search.cpp -o tail_search
./tail_search > tail_search.log
python3 tail_filter.py > tail_filter.log
```

The numerical screen reads `tail_input.txt` and checks engine operations on
900 finite sample cases. It examines 17,940 pair/row choices and leaves 4,901
finite-sample candidates. The subsequent symbolic external-path screen finds
no survivor. This is a restricted candidate screen, not a universal proof of
any modified engine: its box contracts would need to be proved separately
for every changed engine. The table, frame, and ordinary semantics cannot be
certified just by reusing the original oracle after changing protected rows.

## Same-row quotients and the isolated fixed-falsity experiment

`flex_result.json` records the 312 same-row quotient cases screened with the
generalized executor. Run `python3 ../verification/flexible_core.py` here to
repeat that family using the supplied final invariant. It preserves the engine
rows used by the oracle. This family overlaps the larger quotient searches.

`fixed_false_matrix.py` searches small logical matrices for a restricted
implicational basis in which the fourth variable of the rho8 schema is fixed
to the falsity value. Run it with `python3 fixed_false_matrix.py`. Its
counterexample concerns that isolated basis plus explosion and modus ponens.
It does not validate a change to the full PA196 calculus, whose other heads
and gate may add strength. No machine is accepted on its basis.

The report's separate, all-instance countervaluation for the shorter first
quantifier head is in `../verification/t_replacement_countermodel.py` and
`../verification/audit.md`.
