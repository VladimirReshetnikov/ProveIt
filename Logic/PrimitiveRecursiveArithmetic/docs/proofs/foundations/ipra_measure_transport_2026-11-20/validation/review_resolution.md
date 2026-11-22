# Resolution of independent review findings

The two independent mathematical reviews are included in this directory.
Their statements are reviews, not kernel proofs. The following corrections
were applied before the final PDF was compiled:

| Finding | Resolution |
|---|---|
| Decidable does not imply primitive recursive | Core Booleanization now requires a fixed PR test and its proved Boolean specification. |
| Sample points may coincide | Distance-table Rips complexes now use labelled vertices and a pseudometric; no equality test identifies represented points. |
| Rational sensitivities versus integer shifts | Formula weights are rounded to an integer upper bound before use of the integer shift. |
| Different input bounds in bilinear extension | The proof compares constructors through common enlarged bounds and finer stages, then eliminates rational slack. |
| Disk-boundary differentiation and represented inputs | The analytic construction uses the larger rational guard r'=(1+r)/2 for arbitrary small increments and input approximations. |
| Implicit pointwise domination in L1 | Domination is positive-part norm zero; a finite residual inequality transfers the envelope tail bound. |
| Density continuity needs a cap | The energy-tail modulus itself produces the cap H(R(0))+1. |
| Boolean-algebra density extension precision | The report states the explicit doubled-precision reindexing and corresponding tail conversion. |
| Name normalization | The relation between regular and stronger rapid names and the monotone-hull convention are stated explicitly. |

The source-level correction is confined to the unsafe separate-tail shortcut.
The valid existing common-envelope object-iPRA theorem remains credited.
