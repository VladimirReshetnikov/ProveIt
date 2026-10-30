# Separate 86-operation equation presentation

[`equation86.tex`](../../equation86.tex) and [`equation86.pdf`](../../equation86.pdf) present the 13-variable positive-integer equation separately from the maintained 14-variable `equation.tex/pdf`. They use distinct unknown names `J,F,alpha,f,g,T,X,Y,xi,eta,zeta,upsilon,gamma`; `g`, `xi` and `upsilon` correspond respectively to the candidate JSON's `i`, `r` and `y`. The 942-tile constant definition is carried over byte-for-byte from the maintained page, including the complete encoded integer in base 10. The second page lists every gate in order, with ASCII names explicitly identified and intermediate gate names distinct from the unknowns. No degree or minimality claim is made.

The page states the scope accurately: Lean's `HAAdaptiveDirectOrdinate86.ha_equivalence` proves the existence of an HA derivation of both directions for the exact formalized no-zero and ordinary ZFC consistency sentences. The independently replayed fresh-parent proof is a pre-merge source snapshot with inherited historical HA/ZF/Foundation/Mathlib/package and unlisted boundaries, as detailed in [`ha86-fresh-parent-extension-independent.md`](../../reviews/ha86-fresh-parent-extension-independent.md). Subsequent source changes require a new current-source replay; this presentation does not claim that full refresh has happened.

## Faithfulness and rendering

From the repository root:

```sh
python3 Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/generate_equation86.py
python3 Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/verify_equation86.py
mkdir -p /tmp/equation86-build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory /tmp/equation86-build Computability/DiophantineConsistency/equation86.tex
```

The generator pins candidate JSON SHA-256 `e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f` and emits all 86 circuit rows. The separate checker independently evaluates the graph and a mathematical transcription of the display as exact sparse integer polynomials in the 13 unknowns and four symbolic ports: 24 abbreviation/factor identities pass, and the final product wiring is checked structurally. It also verifies the exact displayed TeX block, parses all 86 rendered circuit lines against the JSON with the declared name mapping, and checks the fixed-constant block against `equation.tex`. The TeX-to-mathematical-transcription correspondence is a review of the pinned display block, not an automated TeX parser. The literal Lean source was separately regenerated from the same JSON and matched the proof snapshot, as recorded in the HA receipt.

The checked source SHA-256 is `d4ab2dfb35744dc00af43835e2114397a5b5e1ded59e966f0cd81610ce6b12cd`, and the PDF is `6c0515b2656a5c2711687987a5e57f31bd8be87d0f0d0a61b475824c46e4b646`. Two independent local `pdflatex` runs produced the same PDF bytes. The output has two letter-size pages; both were visually inspected. The log has no overfull boxes, though it records font-size substitutions for small mathematical scripts.
