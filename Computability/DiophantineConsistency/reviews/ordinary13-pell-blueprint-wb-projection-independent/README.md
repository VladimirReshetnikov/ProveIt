# Independent source review of the Pell-blueprint WB drafts

The two drafts' intended binder positions and projection inequalities agree with the inspected recursion, graph and witness-calculus source. No concrete source-level index or direction error was found. Their quotations, `change`, `simp`, `wb_auto`, model instances and prospective imported provider have **not** been elaborated, so the proposed extraction and witness-bound theorems are not yet checked Lean results.

The literal successor quote has free context `[out,previous,index,b]` and introduces x then y. Thus before x is introduced `previous` is `#1`; before y is introduced, with context `[x,out,previous,index,b]`, it is `#2`; inside the six-slot body `[y,x,out,previous,index,b]`, it is slot 3. The inner source uses x at slot 1, y at slot 0, output at slot 2 and b at slot 5. Its pair coordinates match the literal Pell successor; the index argument is indeed unused by that equation. The proposed `wb_exs_term` calls therefore use the right bounds **if** the quotation-generated body and the `change` are accepted as the same formula.

The inspected `wb_exs_term` expects a bound on the introduced witness from evaluation of the existential body, and the earlier WB draft keeps `FirstBound` and `SecondBound` as explicit premises. The later projection draft proposes to discharge them by evaluating the two graph conjuncts. For the first, the source `eval_ex` has the direction needed to introduce y into `[y,x,out,previous,index,b]`; the first conjunct yields `x=π₁(e 1)`. For the second, the second conjunct yields `y=π₂(e 2)`. Foundation's represented projection graphs and the `π₁,π₂≤source` lemmas have the expected orientations. The `.1` and `.2.1` selections correspond to the displayed right-associated conjunction.

The existing source supplies the `WB` rules for both projection graphs and pairing. Its `wb_auto` is a repeated structural tactic; it has no general rule that automatically bounds an arbitrary unbounded existential, so the drafts appropriately handle the two outer witnesses explicitly. Whether `wb_auto` recognizes these exact quotation substitutions, whether `simp [succInner, Semiformula.eval_substs]` extracts the intended conjunction, and whether the local `IOpen`/`PA⁻` instances resolve remain real compilation questions rather than proved facts.

Even a successful coherent check of both drafts would provide only these blueprint clause premises for the generic model-level `WB` interface. It would not on its own yield a uniform primitive-recursive bound for every nested period-formula witness, prove the period evaluation bridge, or construct an iPRA derivation.

The independent checker pins both drafts and their source interfaces, checks the quotation and extraction text against the actual definitions and `eval_ex` direction, and runs 3,000 natural pairing/transition controls with independently constructed contexts. These controls do not inspect Lean's generated AST or validate tactics. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-blueprint-wb-projection-independent/check.py | cmp - reviews/ordinary13-pell-blueprint-wb-projection-independent/receipt.json
```

No Lean, build, staging, provider audit or axiom report was run.
