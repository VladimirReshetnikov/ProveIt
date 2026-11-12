# Base-10 display of the 17/104/20 natural candidate

The [PDF](equation.pdf) and [TeX source](equation.tex) present the
[17-natural-input, 104-operation, degree-20 candidate](../adaptive-aq17-natural-forced104/).
All inputs are nonnegative and have distinct readable names; numbered `G` names
are abbreviations, not additional variables. The four fixed integers use the
existing base-10 recipe copied byte for byte from the maintained main
`equation.tex`. This separate presentation does not replace the main equation.

The external mixed-shift argument assumes the second fixed port is represented
by a nonnegative natural, as it is for the selected current tuple; the earlier
positive-zero chain also assumes positive beta. **This expression and its
model transfer have not been elaborated in Lean**, and the historical parent
endpoint retains its documented provenance limitations.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/adaptive-aq17-natural-forced104-decimal-display/generate.py --write
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=research/adaptive-aq17-natural-forced104-decimal-display research/adaptive-aq17-natural-forced104-decimal-display/equation.tex
python3 -I -S -B research/adaptive-aq17-natural-forced104-decimal-display/verify_display.py
```

The generator pins the graph and fixed-constant recipe. The separate checker
matches all 104 rows in TeX and extracted PDF text, all 17 input names, the
fixed constant section and decimal seed, two-page layout and absence of
overfull boxes. Its output is [render-result.json](render-result.json). These
are finite display checks, not Lean elaboration or formal PDF semantics.
