# One-step reopening with explicit proof code

For every PRA model with IΣ₁ arithmetic reduct and any internal theory, a singleton proof of the one-variable closure `closeOne p` of an arbitrary internally valid open formula p is transformed into a singleton proof of p. The construction explicitly shifts and specializes the proof, avoiding the proof choice in the earlier reopening implementation. Its exact code is `reopenOneCode`; `reopenOneGraph` is a fixed Σ₁ graph defining this code, and the source binder itself now has a fixed Σ₁ graph.

This covers one binding only. Reopening the nonstandard model-length closure used by full separation still needs a definable iteration/history construction; the supplied one-closure proof is an explicit premise. It does not by itself prove native iPRA equivalence. The checker recompiles the source with selected byte-checked repository-built dependencies; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-reopen-one-code.sh "$PWD" /dev/shm/pa194-reopen-one-code-repo
```

Choose a fresh output for another run.
