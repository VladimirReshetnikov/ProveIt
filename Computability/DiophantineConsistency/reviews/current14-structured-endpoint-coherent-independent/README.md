# Independent source review of the structured-endpoint runner

The revised supervisor, two-client runner and owned-session helper were reviewed without launching the supervisor, coordinator, Lean clients or any child process. Pinned hashes and independent report-parser controls are recorded in [result.json](result.json). The positive extension/client path has not run, and this review does not observe a supervisor outer-session exit or independently audit the live base.

The supervisor authenticates its coordinator pins and preflight, starts one `Popen` child and waits for that exact child; it records the actual exit, interruptions, log and coordinator state digest. A wait interruption prevents its receipt from being `PASS` even if a later wait succeeds. The supervisor's own outer exit still needs separate observation.

The client runner reauthenticates the supervisor receipt, coordinator and extension terminal state, base/provider context, the 61-row verifier and direct guards before staging either source. Its private client object root precedes exactly one authenticated extension overlay and the guarded package root. It rejects competing client namespaces, checks compiler-reported direct imports against the specified names and producer guards, hashes the dependency and compiler logs, and checks five named port reports and one endpoint report with the permitted Lean metatheory axiom set. It rechecks terminal providers, direct/output guards, source hashes and final client inventory before `PASS`. Full transitive/dynamic ancestry and changes between observations remain inherited; receipt process fields are not independently traced.

The endpoint draft states in Lean that there **exists a port tuple** with the four structured recipes and a standard-iPRA derivability statement for its no-zero formula. The tuple existential is outside iPRA. The draft is not yet a checked client theorem and does not formalize TeX/PDF semantics.

Review identified a late-timeout edge: the helper previously accepted a terminal child before checking whether its elapsed bound had passed. The author now checks elapsed time even at terminal/drained observation, retries interrupted final reaping, and records a passing late-finish refusal control. The author also made optimized-Python controls refuse rather than silently remove assertions. The helper signals only after checking the unreaped child's PID, parent, group, session and start identity; monitoring failures cause passive drain and may wait indefinitely. Process escape, forced Python death, kernel/`/proc` faults and between-sample resource peaks remain outside its guarantee. The compiler monitor's RSS and host-memory limits are sampled, not reservations.

Our checker verifies the pinned source and recorded no-Lean control hashes, client source and exact import/report lists, and independently checks report parsing for allowed/no-axiom reports and rejection of warning, error, wrong name, duplicate report, `sorryAx` and an unapproved axiom. The author's controls include a successful non-Lean child fixture, wait retry, late-timeout rejection and refusal while the base was live. Neither set exercises successful real base/extension authentication, actual Lean client execution, or the full positive dependency-routing path.

No additional blocker was found in this scoped source review. The prerequisite base completion and independent base audit, independently observed supervisor exit, successful extension and its independent audit, client run and terminal audit remain separate work. A source elaboration or memory failure is still possible.

Read-only reproduction from any directory:

```
python3 -I -S -B path/to/current14-structured-endpoint-coherent-independent/check.py
```

The deterministic output is frozen in `result.json`.
