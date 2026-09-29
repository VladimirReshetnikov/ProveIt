# Research status

Date: 28 September 2026.

## Theorem-by-theorem boundary

1. **Exact three-output optimum, all n >= 7.**
   Complete analytic upper proof for n >= 32; exact computer-assisted upper
   step for 7 <= n <= 31. Attainment imports the established two-generated
   U_(a,b) witness and Davies output construction. Two local implementations
   agree on all 3,717 finite structural inequalities.

2. **Necessary structure of every three-output optimizer.**
   Follows from the strict inequalities and the unique minimizing graph
   parameters in the finite certificate. It includes the permutation cycle
   lengths, blockwise injectivity of the singular letter, and the output
   coloring's form and period. It is not a classification of all singular
   generators: an improper-coloring reachability condition remains.

3. **Sharp deficit asymptotics for every fixed k >= 3.**
   Mathematical proof, with no computational range assumption. The leading
   constant is explicit, including the odd-k dependence on n modulo four.
   Fixed k is essential; no uniform growing-k claim.

4. **Eventual exact formula for every fixed odd k.**
   Mathematical strict-separation proof plus the established lower witnesses.
   No numerical N(k) for odd k >= 5 has been derived here.

5. **Near-optimal rigidity.**
   Mathematical consequence of the uniform graph and constant gaps. Necessary
   structure is not asserted sufficient for arbitrary generators.

6. **Even-output interval criterion.**
   Mathematical if-and-only-if criterion for first-order optimality within the
   established U_(a,b) witness family. It is not an exact even-output optimum.

## Independent implementation means

`independent_check.py` does not import `verify.py`. It uses a different
recurrence to enumerate permutation orders, inclusion-exclusion instead of
the three-color closed form, a different enumeration order for graph types,
and direct coprime-split optimization instead of the nearest-split formula.
It reconstructs and compares every candidate record. Both were produced in
the same AI-assisted investigation; this is not external referee validation.

## External dependencies

Davies's reversal-orbit interpretation and lower-witness theorem; the latter
uses Holzer–König's two-generation theorem. The collision-graph framework is
credited to the inspected ProveIt report and rederived in the article. No
maximal-two-generated-monoid conjecture or unproved repository theorem is
used as an assumption in the new upper bounds.

## Not claimed

- Independent refereeing, machine-checked formalization, or worldwide priority.
- Exact optimality for every even k and every n.
- Uniform asymptotics with k depending on n.
- A numerical cutoff for fixed odd k >= 5.
- A complete classification of all singular generators realizing the optimum.
- That the finite sanity-check BFS searches prove an infinite statement.

The targeted literature search did not locate a later solution, but that is
not an exhaustive novelty determination.
