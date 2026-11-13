# Independent review of three slot00 attempts

The first author-recorded outer session **70936 exited 1** after Lean could not
infer the dependent family for `Fin.cons_succ`. The second **99410 exited 1**:
an explicit constant family resolved that mismatch, but Lean still did not
identify `(14 : Fin 38).succ` with `(15 : Fin 39)` under the attempted
`simpa`. Both dependency scans succeeded; neither compile produced an object.

The third author-recorded session **76831 exited 0**. It explicitly proves
that finite-index equality by `decide` before applying `Fin.cons_succ`, and
the retained dependency and compile records both have exit 0 without monitor
stops. Its object SHA-256 under `/tmp/nine-sharing-norm38-slot00-retry02-20261105/`
is `8cb455659834533a63352914a2d7d7ad2db302b11d67d1a30adfdc4737c45df0`.
The compile log records five linter warnings: one unnecessary `simpa`, two
unused simp arguments, an unreachable tactic and a tactic that did nothing.
No axiom report was requested.

The **unchanged** theorem statement is the first literal residual-evaluation
identity, for an IΣ₁ model, natural witness vector and explicit four-port cast
equalities: slot 0 evaluates to the static q² gate's positive component
residual. It does not assert that this residual is zero. The remaining 28 slot
identities, static extraction theorem, graph bridge and iPRA endpoint are not
established by this isolated check.

`check.py` verifies the exact statement against the original full draft, the
two narrow proof changes, retained states/logs and source snapshots, the
successful object, both direct provider object hashes, 150 guard slots and
1,065 overlay links for each attempt. Failed attempts stopped before a
success-path final guard audit; this review separately checked those recorded
guards against current files. The outer exits are post-hoc author records, not
raw transcripts or independently witnessed exits. No Lean process was run by
this review. Inherited provider ancestry, between-observation changes and
sampled resource limits remain as documented in the experiment packets.
