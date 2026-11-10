# Positive74 register circuit: count and liveness

Proposed explicit 74-gate register DAG. Terminals are 14 variable inputs, four fixed integer ports, and integer literals; arithmetic operations are binary addition, subtraction, and multiplication. Intended kernel results: exact operation histogram, topological ordering, and inductive output reachability of each gate. Circuit evaluation and equality to the existing expression are separate stages. The source comparison with the external JSON graph is independently checked outside Lean, not a kernel-checked file binding. Provider and captured point-survey ancestry qualifications persist. No Lean attempt yet.

Independent source review: `reviews/nine-sharing-sign14-positive74-circuit-source-independent/`.

Attempt01 failed, outer session 44246 exit 1: `omega` did not identify the two forms of the Fin-coerced parent index. Clean reports printed from the failed module do not constitute an object. Independent failure audit: `reviews/nine-sharing-sign14-positive74-circuit-failure-independent/`.
