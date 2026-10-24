# Mixed-radix BFS seed: fewer bits, no shorter tested complete recipe

The three fully printed research siblings reduce the current436-character
BFS compact44 seed by37–39 base62 characters and221–233 bits. Their complete
printed coefficient recipes are26–35 nonwhite characters longer. The
measured result is negative for a canonical-page change. No canonical page,
coefficient payload, frozen packet, common document or Lean file changed.

| Complete recipe | Seed bits | Base62 symbols | Recipe nonwhite characters | Change |
|---|---:|---:|---:|---:|
| Current fixed216 |2594|436|2393|0|
| Generic old-target radix σ+2 |2373|399|2428|+35|
| Radix σ+1, literal halt at125 |2367|398|2419|+26|
| Radix σ+1, omit halt factor |2361|397|2423|+30|

All comparisons use `pdftotext -raw` on complete standalone one-page PDFs,
counting from “The four fixed integers.” through the final seed. The
existing explanatory text is retained; the new recipes additionally define
empty products. Body algebra, all other coefficient definitions, alphabet,
font sizes and proof-boundary text are unchanged. In particular this result
does not buy a shorter recipe by deleting an explanation. The corresponding
whole-page changes are identical. All three render on one Letter page with
no overfull box, and all397–399 seed characters extract exactly.

[PROOF.md](PROOF.md) specifies the mixed-radix identities, finite bounds and
unique early halt exception. Each variant directory contains its entire
`equation.tex`, PDF, extracted text, literal seed and decomposed fields.
The printed recipes need no external table, file, program or hash.
The [checker](check.py) uses the new literals to recover all430 actions,
all943 tiles including the corrected initializer, and every byte of all four
coherent compact44 coefficients. It separately authenticates the BFS action
list against all original transitions. The reconstructed K is the existing
592884-bit BFS K; it is not changed again by this compression experiment.

The previous `SEED_COMPRESSION54.md` and `SEED_PREDICTORS54.md` already noted
a variable-radix payload probe and its larger halt/offset decoder. They did
not retain this complete current compact44/base62 printed comparison. This
packet confirms that warning for the tested closed formulas, rather than
presenting their payload saving as a new complete-recipe improvement.
It does not rule out a more economical future arithmetic decoder.

From the repository root, replay normal and optimized modes sequentially:

```
python Computability/DiophantineConsistency/research/mixed-radix-bfs-seed/check.py --render --output /tmp/mixed-normal.json
python -O Computability/DiophantineConsistency/research/mixed-radix-bfs-seed/check.py --render --output /tmp/mixed-optimized.json
```

The checker executes the pinned, previously reviewed closed tuple verifier;
it executes no incoming archive program, emitter, optimizer or Lean. Its
finite audit repeats all66062 native overlap checks and the controller/carry
premises, but no new calibration theorem is needed for equal complete
coefficients. The current page is retained as the better tested display.
