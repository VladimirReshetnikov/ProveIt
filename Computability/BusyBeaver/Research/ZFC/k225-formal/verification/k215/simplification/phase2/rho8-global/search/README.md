# Bounded global proof search

The retained candidate has **629 theorem nodes / 735 compact instructions**, with 939 input terms. The previous proof had 674 / 780. Kernel results belong to the sibling Lean and Rocq records; these files record discovery and independent finite syntax checks.

| Run | Offered family / objective | Total time | Solver report |
| --- | --- | ---: | --- |
| 1 | All earlier exact strict-schema alternatives; minimum nodes | 18.65 s | 674, matching primal/dual bounds |
| 2 | All earlier exact normalized alternatives, including `Imp(T,T)=T`; minimum nodes | 30.35 s | 674, matching bounds |
| 3 | Same normalized rules; minimum instructions under the 674-node cap | 3.24 s | 780, matching bounds |
| 4 | Earlier and later normalized schema alternatives; acyclic ranks; minimum nodes | 117.46 s | 629, matching bounds |

Each solver invocation had a 120-second solver limit and an external 175-second process cap. Run 4 built 14,947 valid rule choices after considering every nonself ordered pair of original nodes. Binary inclusion/rule variables ensure that each included node has one rule and includes every prerequisite. Continuous ranks with a strict unit gap prevent circular proofs. The known 674-node proof supplied a feasibility cap; SciPy did not receive a warm start. A later warm-start draft was never executed.

The selected graph was independently cycle-checked and topologically renumbered. A separate standard-library checker then checked every emitted rule and the exact original root. The first checker draft omitted the input format’s injective consequent renaming after `mp_substitution`; it rejected the original and previously checked 674-node controls too. That checker history is retained, and the corrected checker passed all three certificates. The 629-node candidate was never changed during this correction.

[results.json](results.json) records exact solver outcomes and scope. [finite-check.json](finite-check.json), [original-control.json](original-control.json) and [earlier674-control.json](earlier674-control.json) record the independent finite checks. [replay-result.json](replay-result.json) binds the solver-free deterministic replay.

[discovery-evidence.tar.gz](discovery-evidence.tar.gz) preserves both prior local searches, the four global scripts/runs, full offered-rule streams, output certificates, logs, validator history, and the unexecuted warm-start draft. [evidence-index.json](evidence-index.json) pins every archived byte. Discovery scripts retain their exact historical workspace paths and used the existing SciPy 1.18.1 / HiGHS 1.12.0 environment. They invoke no Lean or Rocq compiler. The maintained [plan/replay](../../../../../../rho8plan/README.md) is portable, uses only Python’s standard library, and requires no optimization run.

Matching numerical bounds are not a formal minimum-size theorem, and the finite offered rule family does not encompass arbitrary mathematical proofs. The useful mathematical change is moving original lemma 1013, `A → ((A → B) → B)`, before five of its instances and sharing its proof.
