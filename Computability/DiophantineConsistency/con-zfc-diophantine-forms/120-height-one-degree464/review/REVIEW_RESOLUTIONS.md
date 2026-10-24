# Release review resolutions

The retained `HEIGHT_ONE_REVIEW.md` records the construction at the time
of its review. Its requested refinements were completed before release:

1. The generic exact-degree theorem now assumes at least one nonzero
   monomial occurrence. The supplied system satisfies this condition.
2. Binary constant normalization now explicitly starts from the literal
   integer 1; no separate C_1 wire is counted.
3. The verifier now runs its full artifact verification against two actual
   modified polynomial files, changing one nonconstant coefficient and
   deleting the constant term. Both calls must reject. These results are
   recorded in `height_one/output/VERIFY.json` and its optimized companion,
   and the release replay repeats them.

The separate direct-source review and reading order are retained in
`height_one/source/reading/AUDIT_AND_READING_ORDER.md`. This preserves its
scope, including the distinction between natural-coordinate formal Pell
interfaces and the ordinary signed comparison theorem. It does not claim
a full ancestor compiler replay or a transitive Lean build.

A final read-only release usability review checked the documented Python
entry points, relative paths, all eleven-variable source pins, all six
coefficient payloads and recipe dependencies, and the main LaTeX file with
its four companion sections. No blocking usability problem was found.
The plaintext quartic is supplied and independently compared with its JSON;
the builder regenerates the three JSON artifacts, not the plaintext file.

These reviews were conducted by separate agents in this AI-assisted
workflow. They are not external human endorsements or formal certificates.
