# Bounded fixed85 omega source-context triage

This packet inspects 63 selected lines containing `omega` in 26 local source
modules from the nine-alternative fixed85 selection. **No additional
abstract-model omega hazard was identified at those individually inspected
sites.** This is a source-context assessment, not Lean elaboration or a
claim that any module or proof compiles.

The inspected lines fall into these categories:

* Eight `ArithmeticAdaptive*` sites and ten lines in
  `ArithmeticAdaptiveRankWindow2011` are standard `ℕ` bounds for the fixed
  radix, beta, support, or digit positions. Their enclosing files also have
  model-valued theorems; those surrounding declarations do not make these
  particular local `omega` goals model-valued.
* `ModelArithmetic` uses `omega` for standard natural residue witnesses after
  bounding model elements by a standard numeral. `ArithmeticRunTrace` and
  `ArithmeticWangTable` use it for finite table indices extracted through
  `standard_of_lt` before casting back to the model.
* `ArithmeticExpression`, `ArithmeticRepresentation`, byte-recipe and
  retained-beta sites concern ordinary natural indices, assignments, powers,
  or byte-list arithmetic. The particular compact word parity sites prove
  bounds on an explicit `u : ℕ` before `exact_mod_cast`.
* The inspected induction, formula and syntax sites concern standard natural
  hierarchy levels, `Fin` arities, or standard natural syntax-code bounds;
  they do not directly ask `omega` to solve inequalities over the abstract
  arithmetic model.

`receipt.json` records each inspected logical module, its selected source
hash, exact line number and line text, and the local classification. The
checker verifies those anchors and pins the entire source-selection JSON.
It does **not** infer goal types from Lean, execute the tactic, establish that
any referenced source has a matching compiled provider, or inspect axioms.
Even standard-natural `omega` use may fail for another reason.

The earlier lexical inventory counted 143 non-research local modules with
potential `omega` lines. This packet samples 26 such modules, and in several
of them only selected sites. The other modules and sites remain unaudited;
lexical counts can include comments or examples. The nine isolated research
source alternatives are also still unelaborated, and the 93 external/frontier
module names remain out of this packet's scope. No conclusion about the
fixed85 endpoint, provider graph, or physical PDF follows.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-fixed85-model-omega-triage/check.py
```

The command reads only pinned local sources and the source-selection record;
it performs no Lean build, staging, object inspection or mutation.
