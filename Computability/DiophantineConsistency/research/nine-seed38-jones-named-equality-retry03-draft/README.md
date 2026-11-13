# Named-evaluator reflexivity retry source

These sources preserve retry02's statements and equality stage. The sole tuple-proof change applies `rfl` to any goals left by the existing simplifier. The guarded check accepted both statements; the [independent terminal audit](../../reviews/nine-seed38-jones-named-equality-retry03-terminal-frontier-independent/) passed. The resulting Lean equality does not bind external JSON, a parser, or human prose. See the [guarded check](../nine-seed38-jones-named-equality-retry03/README.md).
