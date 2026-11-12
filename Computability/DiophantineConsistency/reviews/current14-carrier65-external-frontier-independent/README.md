# Independent review: Carrier65 recorded external frontier

The [external-frontier audit](../../research/current14-carrier65-external-frontier-audit/README.md) is supported within its explicitly bounded, point-in-time scope. Its original receipt reproduces. The independent checker below reconstructs the recorded graph with a separate stack traversal and rechecks the selected retained evidence; it does not run Lean or mutate the preserved build trees.

From the 239 recorded successful prefix rows, the independent traversal recovers 343 recorded external edges, 55 names, 39 base seeds and 2,145 distinct external guard slots. Following the saved base records' project edges from those seeds reaches 172 base records through 240 project edges and 208 additional external edges; the combined recorded frontier has 65 Mathlib names, three Foundation names and `Init`. These are counts and classifications of the *recorded* routes. They are not a proof of actual Lean namespace resolution or complete runtime dependencies.

The independent checker rehashes the retained Foundation archive and artifact sets (477 and 1,540 files), all 140 target objects and 14,764 recorded external guards, and confirms the three reached Foundation object hashes and the saved provider status. The separate historical review still records the Foundation wrapper's outer exit as unobserved. Both checks use the same historical receipts, which are not independent authentication that every inherited provider or dynamic load was correct.

For all 65 selected Mathlib modules, the checker compares actual source bytes directly with `git show` of the pinned revision, checks the 650 recorded package companion slots and saved trace hashes, and independently strips comments and reads the source's simple initial import headers. The resulting 634 header edges, 546 distinct next names, and two `import all` edges match the audit; each next name currently has an `.olean` candidate in one of the two sampled roots. This per-file candidate test is not Lean's namespace-first selection and does not traverse the next layer. Matching source bytes and trace hashes does not prove that compiled objects came from those sources or that their recorded output identifiers are valid.

All filesystem observations are non-atomic and may change. The review does not inspect compiled import headers, establish required private/server or runtime files, authenticate source-to-object provenance, trace dynamic loading, protect inputs against concurrent mutation, or establish provider compatibility. The audit's stated limits and the need for separately guarded future investigation are appropriate; neither packet proves an iPRA endpoint or makes a continuation build-ready.

Run from the repository root while the retained temporary paths and Git checkout remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current14-carrier65-external-frontier-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/current14-carrier65-external-frontier-independent/result.json
```
