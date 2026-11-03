# Corrected author-only marked suffix runner

This runner selects the 22-source corrected source plan, whose only change is the separately compiled no-`#check` graph-halt client at position 21. It pins the independently reviewed corrected closure CHECK, audit and terminal bytes and reruns that no-Lean audit before and after any full build. It also retains the three exact historical full-warning rules from the preceding reviewed runner; all other warnings remain rejected.

The final no-Lean preflight session 38778 exited 0 with 22 sources and 740 guarded slots. The final synthetic 36-case wrapper test passed three fake paths and rejected 33 injections; helper and warning controls passed. Synthetic controls replace compiler, providers, monitor and closure callback and do not establish a Lean result or resource limit. The real compiler has not been launched by this corrected runner. The earlier fail-closed draft observation remains in `observations/`.

A new independent exact-byte runner review and coordinated Lean slot are required before any full retry. This remains an author-only exploration with inherited transitive/package and dynamic ancestry unauthenticated; it does not claim a paired build, retained tuple/K binding, converse or internal iPRA result.
