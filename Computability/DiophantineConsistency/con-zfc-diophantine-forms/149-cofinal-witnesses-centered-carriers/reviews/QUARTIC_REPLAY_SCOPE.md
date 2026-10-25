# Independent exact transformation replay

The full ordinary source composition is reviewed in odd_common_review.md. In addition to the newly supplied source and endpoint checkers, the preceding round's independent universal polynomial checker was run unchanged against the final new quartet, both normally and under optimized Python.

It verified every source hash, coordinate inverse, elementary row inverse, unit affine substitution, zero row before deletion, absence of eliminated coordinates, complete original-row restoration identity, collected SOS coefficient, metric and coordinate liveness claim. All five deliberate corruption controls were rejected. Fresh rebuilds reproduced every equation, expansion and metric file byte for byte. Receipts are quartic_inherited_checker.json and quartic_inherited_checker_optimized.json.

The new source-specific checker separately verifies the exact odd-square replacement, deletion of precisely three private guard coordinates, the two retained ceiling guards, and every untouched parent row. The degree-three multiplier rank certificate is a separate finite row-span obstruction; it does not assert ideal-theoretic or global minimality. These checks supplement, rather than replace, the ordinary unbounded source/calibration proofs.
