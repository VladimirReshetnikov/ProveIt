# Model-length reopening with explicit proof codes

For every PRA model whose arithmetic reduct satisfies IΣ₁, any internal theory, arbitrary valid source formula p, and arbitrary model-valued length n, a supplied singleton proof of `modelClose n p` is transformed into a singleton proof of p. The construction uses a fixed primitive-recursion blueprint to iterate the explicit one-step reopening code, including for nonstandard n. An IΣ₁ induction proves that every intermediate computed code is a derivation of the appropriate remaining closure. `reopenIterGraph` is a fixed Σ₁ graph defining the result at any intermediate index; the final proof value is exactly the result at n.

The initial closed-formula proof remains an input. In particular, this does not yet build the fully closed separation axiom proof or establish native iPRA machine equivalence. The checker recompiles the source with selected byte-checked repository-built dependencies; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-reopen-iter-code.sh "$PWD" /dev/shm/pa194-reopen-iter-code-repo
```

Choose a fresh output for another run.
