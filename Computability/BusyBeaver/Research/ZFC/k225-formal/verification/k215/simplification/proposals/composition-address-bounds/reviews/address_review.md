# Independent review of the address-run reduction section

Reviewed `report_section.tex`, `source_capacity.py`, `check_capacity.py`, `verify.py`, and the two CFG resolvers in `source_language.py`. No solver, allocation search, or large build was rerun.

## Assessment

**No mathematical correction is required in the stated capacity theorem, the five-zero obstruction, or the source-versus-machine boundary.** The exactness claim is properly restricted to arbitrary occurrence-wise rotations of three closed factors. It does not imply optimal source DAG size, physical-state optimality, or correctness of the shortened scanner.

### Capacity theorem

The `n = 1` case is correctly separated: feasibility is exactly `r <= c1`; the empty proper-prefix minimum is never used. Invalid atoms of capacity -1 are handled separately. For `n >= 2`, the proper-prefix conditions are both necessary and sufficient. The preorder encoding uses `n-1` internal nodes and maintains a positive pending-slot count after every proper leaf prefix. The final leaf has entering run zero. Greedily allocating at most `c1-r, c2, ...` internal-node openings gives the required prefix inequalities and total budget. “Linear time” is accurate in the ordinary unit-cost arithmetic model for the capacity list; no exceptional one-atom construction is hidden.

The recursive application to the entire specified rewrite class is also justified. Whether a node has two closed children is invariant under the permitted rewrites. The maximal free association therefore has a fixed ordered atom sequence, with independent permitted changes inside those atoms. This is stronger than the bounded global-rotation search, but does not broaden the allowed grammar.

### Five-zero lower bound

I independently parsed the baseline source and reconstructed the displayed A,B,C,D,E,F fragment. It is exactly the subtree at `1101001001111`, contains 13 leaves, and spans ordinal indices 4578 through 4590 inclusive. The displayed five-left-edge path ends at CD(5). The recorded child-boundary condition at each binary node is the right obstruction to a permitted rotation.

For maximal clarity, the sentence about ancestor rotations could explicitly say: “Such a node also cannot be split as the binary child of a rotation at its parent, because that would require both of its children to be closed.” This supplies the small implicit step showing that ancestor rotations only move the indivisible fragment. The argument already supports that step; this is a suggested clarification, not a missing hypothesis.

### Source-versus-machine distinction

The section clearly says that the delivered object is a 206-node source with unchanged primitive word and complete guarded CFG, not a 214-state binary machine. The maximal zero-run bound is proved optimal only within the stated closed-associativity class. The two unsuccessful allocation models are explicitly restricted. The altered scanner is a conditional synthesis assumption that still needs a complete runtime proof. These qualifications are appropriate and should remain in the final report.

## Lightweight checks performed

- Reconstructed the exact 13-leaf fragment and verified its source ordinals.
- Checked capacity/constructive behavior on `(-1)`, `(0)`, `(3)`, `(1,0)`, `(0,3)`, `(1,1,0)`, `(2,0,0)`, and `(1,0,3)`, including every feasible entering run for those examples.
- Inspected rather than reran the exhaustive 97,655-vector result and full rotation/CFG replay.

## Minor documentation correction

`check_capacity.py` currently says that the mathematical proof is in `capacity_theorem.md`, which is not present in the packet. Change that docstring reference to `report_section.tex` (and/or the final report). This does not affect execution or the theorem.
