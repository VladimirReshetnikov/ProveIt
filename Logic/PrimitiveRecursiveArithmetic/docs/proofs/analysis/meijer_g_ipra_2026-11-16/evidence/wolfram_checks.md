# Independent Wolfram regression checks

Wolfram Language was used only as an independent transcription check. It returned the following simplifications under positive-real assumptions:

```text
MeijerG[{{1,1},{}},{{1},{0}},z]       -> Log[1+z]
MeijerG[{{1,1},{}},{{1},{1}},z]       -> z/(1+z)
MeijerG[{{},{}},{{0},{1/2}},z/2]      -> Cos[Sqrt[2] Sqrt[z]]/Sqrt[Pi]
MeijerG[{{1-a},{}},{{},{}},z]         -> z^(-a) Exp[-1/z]
MeijerG[{{},{}},{{0},{}},z]           -> Exp[-z]
```

It also gave the standard Meijer-G reduction of `HypergeometricU[a,b,z]`, and numerical checks were made for the generalized-r cosine. The companion `mpmath` script independently checks the printed six-term identity and the Whittaker forward/inverse kernels. These computations do not substitute for the proofs in the report.
