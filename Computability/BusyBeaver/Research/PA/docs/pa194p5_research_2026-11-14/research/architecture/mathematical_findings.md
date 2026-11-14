# Architectural investigations at ProveIt 4be5c6e3a10292a7466f5d3687e3b39615ff049b

## Rejected guard deletion

The pointed-separation component alone is sound in the collision c=a!=b, since an empty-or-singleton separator works. However the actual combined gate G=not(V implies Q) also asserts V=M(a,b) implies forall c M(a,b). That assertion is unsound for c=a. At c=a=0,b=1, assignment x0=1,x1=0 under finite binary membership makes Bit(1,0) true and forall x0 Bit(x0,0) false. Deleting this comparison in the existing emitter is therefore invalid.

## Gamma(H)

Replacing the separate diagonal head Gamma(A)=A implies U(A,A) by Gamma(H) gives the same schema set. From a clean store choose A=0, D-offset=0, H-offset=B to generate Gamma(B). This is already proposed in pa194j_pa194d_conpa_2026-11-13/research/logical_variants/separateH.* and separate_D_H_calibration.txt; do not call it new. The independently replayed candidate grammars both require 197 states: 134 fixed +70 raw reader -7 compatible folds.

## Head order and bounded search

The six independent logical heads and Gamma can be permuted after the parameter-reading prologue without changing the available axiom families. Their stack positions change and require revised selector words. A correct literal implementation must replay its revised source-control graph; a word multiset is insufficient.

We moved Gamma(A) before each of the six logical heads and ran two bounded V8 searches with 13,353 and 7,798 iterations (21,151 total). No candidate at or below 194 was found. The saved data records exact grammars and scores; these narrow negative results are not lower bounds. The first search used temperature 0.06+0.6*(1-j/2500); the second used 0.06+1.6*(1-j/10000). Both ran 22 seconds. Random seeds 71478 and4198 respectively. Timing-dependent stopping is stated explicitly.

The compiler/fold evaluator is a JavaScript port of construction/compiler.py and search/screen.cpp from pa194_conpa_2026-11-13. Its baseline check recovers 134+67-7=194 and verifies all 28 local fold cases. Run node audit_scores.mjs to reproduce this and the Gamma(H) scores.


## Correct startup obstruction and bounded helper limits

The incoming 193-state runtime core is not a blank-start consistency machine. Its start-74 failure persists under every permutation of the instruction-router targets: a fixed 78-step prefix reaches the sole variable router edge, followed by one of nine short scanner prefixes and a provable outward ray. The accompanying TeX proof and JSON traces certify this without relying on a simulation timeout. The earlier incoming QN6 work already screens permutations; this theorem explains that negative behavior and is not a new empirical coverage claim.

Changing only the scanner-51 zero row, and requiring exact recovery of the original marking endpoint on all 64 radius-4 neighborhoods within 40 steps, leaves only the old helper 16 and the published helper 122. This is a bounded search, not an impossibility theorem for arbitrary helpers.

Changing only 74/0 among all 772 actions from existing controls yields no new candidate in a finite marked-file increment screen, even when the spare tail may be any valid nonempty tail. The original 1R0 is the only passing row. The scan uses 76 concrete marked files, a 3000-step bound, and explicit spatial cutoffs; a second version permits bounded left excursions. These limits are part of the result.

The increment row 74/0 recognizes the erased first 1 of the marked register, so its right context is generally an arbitrary remaining register suffix. An argument restricted to an all-zero exterior would not prove the needed runtime identity.
