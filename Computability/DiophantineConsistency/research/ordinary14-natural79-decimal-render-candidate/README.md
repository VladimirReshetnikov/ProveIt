# Natural-79 base-10 standalone equation: candidate and binding route

This separate [TeX candidate](equation.tex) and [four-page PDF](equation.pdf)
render the 14-natural-input, 79-operation graph with distinct input names and a
complete **15,086-digit decimal integer**. They do not modify the maintained
`Computability/DiophantineConsistency/equation.tex` or its PDF. The PDF is a
source-mapping draft, not a claim that this equation's iPRA endpoint is proved.
Its seed is long and the decimal section uses small type; it is not presented
as a one-page optimum or globally simplest equation.

The inputs `J,F,A,f,i,T,w,s,r,e,z,y,g,h` are nonnegative. Monospaced names
are abbreviations, including potentially negative integer intermediates; only
`vout=0` is imposed. The generator translates the 79 source rows and all
four port and 14 variable positions from the pinned `P79NaturalForcedW`
source and candidate JSON. The symbolic expression in the proposed natural-79
endpoint is exactly that graph applied to `CompactSymbolicModelIff.p` at the
source-text level; this observation is not a Lean elaboration.

The four fixed port formulas are based on the Lean symbolic tuple
`[betaNat, paramKernel rho, lowNat, betaNat + highNat]`, with `rho=2^67`.
The 943 selector values are encoded, in their actual source order, as 16-digit
base-10 blocks of the single decimal integer P; the displayed floor/modulo
formula recovers each value. The kernel uses the pinned 41-position list.
The low mask uses its finite support formula, and the shifted-high mask uses
its run-length formula. `generate.py` evaluates the formulas exactly as
integers, verifies all four resulting values against the raw bytes and gzip
hashes in the retained P72 binding, and asserts MF has its beta shift exactly
once. This is an external source transcription and byte comparison; it is not
a Lean theorem about those files, TeX, or PDF bytes. The raw values themselves
would take roughly 178,000 decimal digits per port if printed directly.

`Natural79DecimalPortBridge.lean.src` is an inert proposal reducing the native
endpoint to **four explicit natural-number port equalities**. It assumes these
identities and imports the unelaborated 79 endpoint. An actual formal link
requires:

1. Define a finite Lean decimal seed and recover its 943 16-digit blocks;
   prove they agree with the selected `Compact943Data` selector values.
2. Define the displayed K, μ and ω formulas and prove, respectively, their
   equality to `paramKernel rho`, `lowNat`, and `betaNat + highNat`; also
   prove the displayed beta identity. The checked symbolic byte-recipe
   prototypes and the independently checked `concrete_recipe` are possible
   ingredients, but Python/gzip/file equality alone does not discharge these
   Lean identities. The MF shift must not be added twice.
3. Define the displayed 79-abbreviation equation as Lean `Expr` syntax and
   prove its equality with `P79NaturalForcedW.graph` at those four ports.
   Transfer the unelaborated native endpoint through the equalities and prove
   the natural split-zero semantics for the chosen encoding. Finally compile
   the endpoint, binding and axiom-report clients in one checked compatible
   provider context.
4. For a formal claim about the actual TeX/PDF bytes, separately define and
   verify a parser/representation and its rendering semantics. The current
   external PDF checks and source hashes do not do this.

`result.json` records the external source/byte calculation. `render-result.json`
records a separate PDF text-extraction check: all 15,086 seed digits survive in
order, the PDF has four letter-sized pages, and the current LaTeX log contains
no overfull boxes. These checks do not independently verify every rendered
formula or establish formal document semantics. No Lean or staging was run.

Independent reviews check the [graph and PDF transcription](../../reviews/ordinary14-natural79-decimal-render-independent/README.md)
and the [decimal port formulas](../../reviews/ordinary14-natural79-decimal-port-math-independent/README.md).
They do not establish Lean elaboration or formal document semantics.

To reproduce the generated files and render observations from this directory
(the generator overwrites only files in this candidate directory):

```sh
python3 -I -S -B generate.py | cmp - result.json
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error equation.tex
python3 -I -S -B verify_render.py | cmp - render-result.json
```
