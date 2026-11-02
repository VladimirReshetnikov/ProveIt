# Compact44 controller data: exploratory specialization

`ArithmeticControllerDataCompact44.lean` adapts the existing 2011 controller
data proof to block width `590069` and auxiliary modulus `581197`. Its
single-side exploratory Lean run actually exited 0. In particular, it proves
the stated modular residue and, in an arbitrary model of IΣ₁, the corresponding
coordinate surjectivity and injectivity theorems `zc_surj` and `zc_inj`.
The computed residue is

```
2^(590069*581196) % (590069*581197*581197) = 172304811153038026
172304811153038026 = 1 + 590069*581197*502425
(502425*134409) % 581197 = 1
```

The run reported one unused-section-variable linter warning in `fun1_of_rel`;
the exact observation and command are recorded in `observation.txt`. It used
the historical `/tmp/pell-class-simp-188/final` provider and package overlay,
not a freshly verified source-current dependency closure. This is exploratory,
not a paired replay or independent artifact audit. It does not establish the
rest of the controller-choice construction, any binding to the retained K
coefficient, a graph-to-computation equivalence, or an iPRA endpoint.

The source is a mechanical constant and namespace adaptation of the existing
`ArithmeticControllerData.lean`; its declarations state the exact checked
model assumptions. Its original section comments should be read as background
for this specialization, not as a claim that the remaining 2011 controller
files have already been transferred.
