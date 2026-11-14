# PA194N: no-push modus ponens, original Shift

This self-contained research construction has **194 working states** on the
blank two-way binary tape. The start is 0 and the separate halt label is 194.
Its dense table has 388 rows and SHA-256
`37f7e909724cab7fd667db28f89b9c81653d2576c033750e783b40b3289c04f9`.

The no-push MP rule already appeared in the supplied 196-state work and in
the ZFC zero-spare-transfer investigation. This package composes that rule
with the primary PA194 decoder and supplies its exact source splice and
ten-entry command compiler. It does not claim a new rule or a state count
below 194. Unlike PA194C/CS, the top remains the successful conclusion, the
offset remains the conclusion, and Shift still tests `t+h=1`.

Run with Python 3 and assertions enabled:

```sh
python3 build_nopush.py
python3 mathematics/check_emitter_and_words.py
```

The builder checks the one native-row change, every remaining relocated
source instruction, seven simultaneous folds, all 4,755 arbitrary-register
primitive outcomes, and complete 58,154-transition blank initialization.
The mathematical checker imports no compiler and checks the 190-token
emitter as a free-term computation and the proof-word identities
symbolically, including the zero stack aliases. The ordinary proof is
`mathematics/proof_nopush.tex`; earlier arguments are preserved beside it
with their original paths identified in the text.

The new command proof has a single-command Discard, `MP(0)`, and a uniform
Offset command including offset zero. Successful MP preserves the stack;
the proof compiler explicitly reserves the one zero needed below its
premises. The original Shift makes Pop total even at top code one.

The proposed PA biconditional composes this controller proof with the
inherited separated-head calculus calibration and the table certificates.
It is an ordinary mathematical PA-provability argument; there is no new
end-to-end kernel-checked Lean or Rocq endpoint.

All inputs are from ProveIt commit
`17f92105e2bc4317feae6c219cb2143437b482ff`. The copied compiler, runtimes,
reference source, and proof fragments retain the supplied license notices.
