# A readable fourteen-variable candidate

Let the fourteen independent natural-number unknowns be

`judgeInput, boundInput, slackInput, divisorInput, factorInput, indexInput, clockInput, heightInput, widthInput, countInput, leftInput, rightInput, targetInput, extraInput`.

Each corresponding shorter name in the formulas is its positive shift: for
example, `judge = judgeInput + 1`, `bound = boundInput + 1`, and
`extra = extraInput + 1`. The same rule applies to the other eleven names. The
shorter names are abbreviations, not additional unknowns.

Use the four fixed integers β, K, μ and ω with the same fixed recipe displayed
in [equation.tex](../../equation.tex). The correspondence of that recipe's
bytes to every symbolic current port has not all been proved inside Lean, so
this is a research presentation rather than a replacement for equation.pdf.
Define the following polynomial abbreviations, all using decimal notation:

```text
base       = β·judge
unit       = base + 1
window     = unit − bound − slack
horizontal = width·unit
vertical   = height·unit³
product    = horizontal·vertical
gap        = left + right
length     = product·gap·vertical
center     = gap·vertical + left
sum        = product + vertical
weight     = 4·sum + 3
delta      = sum² + weight
root       = horizontal + sum·center + extra·weight
rank       = (base·(unit − bound) + slack)·(unit² − 1)
             + (μ + unit·ω)·judge
carry      = product·count + gap − rank
inner      = factor²·(center·clock − rank) − center
scale      = index·(root² − 1)
```

With those same positive abbreviations, set

```text
first  = root² − delta·center² − 1
second = carry² − length·(length + gap) − 1
third  = (K + width)·window + (unit − bound) − divisor·base − 1
fourth = target² − scale²·(target² − inner²) − 1
fifth  = delta·factor² − scale² − delta
```

The candidate single equation is

```text
first² + second² + third² + fourth² + fifth² = 0.
```

This is a sum of squares over fourteen natural unknowns. The separately
audited symbolic Lean fragment-DAG expression has exact degree 124 and audited
native, standard and translated iPRA endpoints. The [exact structural and
transformation checker](check.py) compares this named formula against all five
pinned external AST residuals using a small exact sparse-polynomial ring and
explicitly records the two local identities that use `unit = base + 1`.
The relation of those external AST bytes and the displayed fixed-constant
recipe to the Lean embedded fragment DAG is not a theorem in Lean. A separate
independent review of this presentation is required before treating it as a
reviewed equation, and it does not replace the existing PDF.
