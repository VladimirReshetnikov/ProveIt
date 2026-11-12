# Current 14-variable coherent-plan source line count

The pinned retry05 plan selects 529 distinct project, helper and intermediate
audit source files. Their current bytes match the plan's source hashes, and
they contain **57,208 physical lines** in total. This is a count of the
selected source files, including comments, blank lines, shared infrastructure,
and intermediate audit clients. It is not a count of proof terms, newly
written lines, or a minimal proof of the endpoint.

The plan also relies on an authenticated 1,000-module base and external
package infrastructure; those modules are not included in this count. The
selected plan is a proposed coherent rebuild, not a completed build: its
attempt stopped at the disk guard after 239 completed stages. A historical
normalized-quote endpoint passed separately; raw TeX/PDF binding and the
other ancestry limitations recorded in the runner remain open. The estimate
does not establish how many additional lines the missing bindings or a full
coherent rebuild will require.

From the repository root, `python3 -I -S -B
Computability/DiophantineConsistency/reviews/current14-coherent-plan-line-count/check.py`
checks the pinned plan, verifies every selected source hash, and prints the
count. It does not execute Lean or inspect the base modules.
