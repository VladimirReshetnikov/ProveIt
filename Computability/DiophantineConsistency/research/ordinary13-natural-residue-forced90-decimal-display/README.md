# Base-10 display: compact-port 13/90/56 natural candidate

The [PDF](equation.pdf) and [TeX](equation.tex) show the
[13-natural-input, 90-operation candidate](../ordinary13-natural-residue-forced90-degree56/)
with 13 distinct descriptive input names and its complete compact-port
base-10 recipe. This is a separate four-page candidate; its fixed ports are
**not** the current-2011 ports in the maintained root equation.

The 15,086-digit decimal seed and all four fixed-integer formulas are copied
byte for byte from the independently reviewed
[compact decimal presentation](../ordinary14-natural79-decimal-render-candidate/).
The checker reruns that [independent port-formula/byte comparison](../../reviews/ordinary14-natural79-decimal-render-independent/),
then reruns the 13/90 checker, which authenticates the same four raw/gzip
hashes against both P72 and P115 bindings. Consequently the displayed beta,
K, mu and omega correspond to those retained compact bytes; the shift in omega
is included exactly once. This is an external source/byte comparison, not a
formal Lean theorem about PDF rendering or file semantics.

The graph's new mixed-shift transfer and iPRA endpoint remain unelaborated in
Lean. The positive parent's independent review establishes standard-integer
mathematics with stated calibration and provenance limitations, not a new
arbitrary-model proof or current-2011 binding.

From `Computability/DiophantineConsistency` reproduce with:

```
python3 -I -S -B research/ordinary13-natural-residue-forced90-decimal-display/generate.py --write
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=research/ordinary13-natural-residue-forced90-decimal-display research/ordinary13-natural-residue-forced90-decimal-display/equation.tex
python3 -I -S -B research/ordinary13-natural-residue-forced90-decimal-display/verify_display.py
```

The display checker compares all 90 source rows with TeX and extracted PDF
text, all 13 names, the entire fixed-constant section, every decimal seed
digit, four-page layout and absence of overfull boxes. Its deterministic
output is [render-result.json](render-result.json). The complete seed is long
and uses small type; this is not a claim of an optimally compact layout.
