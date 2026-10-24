# Branch-local shared scratch certificates

These are complete **local** ordinary polynomial relations, not complete
Con(ZFC) equations. The best current stack relation has **17 nonnegative
local witnesses**, two exposed state coordinates, and total degree52.
The padded-Horn variant has17 witnesses, three exposed formula labels,
and degree50. The previous local quartic used89 witnesses.

Recommended artifacts:
- `branch_scratch_output_independent.json`: stack transition source;
- `horn_output_independent.json`: padded-Horn inference source;
- `build_branch_scratch.py`: authored independent branch generator;
- `independent_scratch.py`: exact constructor-wire elimination;
- `check_branch_scratch.py`: separate JSON reader and replay/checker;
- `branch_scratch.tex`: mathematical section, with refinement below.

The construction uses three ideas:
1. Flatten each logical alternative separately and use a PRODUCT of branch
   sums of squares. Unselected branches impose no scratch equations.
2. Assign whole constructor outputs to wires, rather than only nonlinear
   products. This stops affine tails from densifying the dependency graph.
3. Substitute14 independent bundle constructor wires away simultaneously.
   Every residual still has degree≤4, so its SOS has degree≤8. All other
   branch SOS factors have degree4 (truth has degree2 in the Horn variant).

The removed bundle output-wire indices are
1,3,4,5,7,9,12,15,17,19,21,22,24,26.
Thirteen of27 constructor output wires remain. There are four shared base
parameters a,b,c,d. Thus13+4=17 local witnesses. Every surviving wire is
still nonnegative: it denotes a composition of the original nonnegative
integer constructor, even if the expanded residual has signed coefficients.
The literal guard is ((c-a)(c-b))²=(d+1)², equivalent over natural d to
c≠a and c≠b. It requires no additional wire.

Each JSON lists explicit residual polynomials, expanded branch SOS
polynomials, and the fixed outer product instruction. A fixed product of
12 literal polynomials is a literal ordinary polynomial description, not
a variable-length product. The count17 excludes the exposed variables.

Reproduce from this directory:
  python build_branch_scratch.py
  python build_branch_scratch.py --split-gate
  python independent_scratch.py
  python independent_scratch.py --output-wires
  python independent_scratch.py --output-wires --horn
  python check_branch_scratch.py

The independent checker reconstructs each SOS expansion exactly from JSON
residuals and compares sparse coefficients. It then evaluates residuals
at independently produced valid integer transitions, followed by endpoint
mutations. This avoids expensive redundant evaluations of a large expanded
SOS at million-bit constructor values. Passing these tests is not a formal
kernel proof; algebraic equivalence follows from the branch-wise circuit
argument in the report.
