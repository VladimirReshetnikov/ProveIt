# Independent review of multiplier-dependent root absorption

**PASS; no correction requested.** I read the complete new proof and 337-line
helper, all84 literal source rows, the strong-root predecessor proof, and the
signed-quotient proof's direct rank and exterior-bound argument. The fresh
reviewer independently authenticates the three author files and all nine
direct dependency files. No frozen helper, including the author helper, was
executed or imported.

| Reviewed author file | SHA-256 |
|---|---|
| complete84_multiplier_dependent_root_absorption.py | `4fbb8595e4956f43829f91e42a57836bc726c3261bc5f9abf0b473d2493e80c4` |
| complete84_multiplier_dependent_root_absorption.json | `720c602d9d82d456fd50fb9b5c4f66132e6b4ca1222c9832694ddf0d9b92a46b` |
| complete84_multiplier_dependent_root_absorption.md | `045a1147a09d3d70550c9f5c6dcf398d8c9686dbfa957f00d263fb868a485d75` |

The dependency pass reproduces exactly 66 computed and22 supplied values
independent of f,T,y, with18 excluded computed values. Compared with the old
85-value boundary, only i, `aux_coefficient_root`, and `R16` are added. The
literal c² and Delta*c² producers are expanded, giving S=Delta*c²*z and
S²=Delta²*c⁴*z². Thus their coefficient-size and z-degree weights are
(3,1),(6,2), while i has (0,1). All85 old arguments retain (4,0). This
accounts for every argument, including supplied input and fixed numerals;
the added computed values are not treated as independently supplied ports.

The exact source audit retains all84 rows and25 supplied ports, checks SSA,
topology, liveness and the unchanged47M37A ledger, and compares the complete
arrays across both inherited receipts. Eight actual exterior cuts expose
24 output ancestors. Independent expansion reproduces the full17-term
polynomial, simultaneous f/T sign invariance, and the four-term zero-f
contraction. The latter excludes G=0 before native recovery because Delta>1
and the factored bracket is1 modulo Delta. No positive-T restoration is
assumed for negative G.

The quantified argument is sound. After fixing the old85 values pointwise,
the dependent substitution defines an integer polynomial g(z); it does not
assume that source equations hold for other z. The monomial weights give
`||g||_1<=L*c^(6t)` despite coefficient collisions or cancellations. The
polynomial `H=g²−Delta*c⁴*z²−1` cannot vanish identically: constant and
degree-at-least-two g are immediate, and linear g would require the nonsquare
Delta*c⁴ to be a square. Integer Cauchy bounds consequently give
`i<=(L²+2)c^max(12t,5)`.

The required lower bound uses the signed theorem's full Rc|m, not merely
R|m or c|m. The composition identity yields
`i>=psi_c(D)/c>=D^(c−1)>c^(c−1)` for every strong completion, because D>c.
Comparing these estimates gives the strict stated cutoff

    2d*x+b_source < R < c < max(12t,5)+1+ceil(log2(L²+2)).

This remains valid for constant G, identically zero G under the declared
convention, and specializations that lower g's degree. G's integer
coefficients and degree are fixed while input and witnesses vary.

The fresh reviewer uses closed even/odd binomial formulas instead of the
author's Pell-polynomial recurrence, and binary powering of Pell pairs
instead of its integer recurrence. It independently reproduces all36 formal
psi composition records,120 growth records,495 monomial-weight patterns and
108 cutoff records at both endpoints. It reconstructs all nine small
main/strong components and27 root polynomials, checks their exact integer
roots and Cauchy inequalities, and additionally checks the intermediate bound
i>=D^(c−1). These are bounded arithmetic corroboration, not compiled histories
or a substitute for the quantified proof.

The reviewer writer and fresh normal and optimized replays from `/` passed:

```text
python3 /tmp/review_complete84_multiplier_dependent_root_absorption.py --root ABS_WIP --author-root /tmp --expect /tmp/review_complete84_multiplier_dependent_root_absorption.json
python3 -O /tmp/review_complete84_multiplier_dependent_root_absorption.py --root ABS_WIP --author-root /tmp --expect /tmp/review_complete84_multiplier_dependent_root_absorption.json
```

After installation, omit `--author-root` when all files share `--root`.
The reviewer preserves checks under optimization, rejects duplicate keys and
noninteger JSON encodings, binds its own bytes, and compares type-sensitive
canonical receipts. Its helper SHA-256 is
`2a9d903f1130846acef27b64c865ccc8b569e2b9f7043c721dd93a62e720e864`;
its receipt SHA-256 is
`84fe77c1be8e7a2d55a6c51edea8cb97814fff96ba93c090953ffff982cca8fb`.

The accepted conclusion is finite ordinary-positive-input projection for
this exact fixed integer-polynomial substitution class on each valid compiler
slice. No new circuit, generic G implementation, complete native zero,
global minimum, or source-degree improvement is claimed or checked here.
