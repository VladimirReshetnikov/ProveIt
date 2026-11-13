# Independent review: ordinary 67/94 source-to-DAG binding

The read-only `check.py` independently parses the pinned `Carrier94Syntax.expressionAt94` source and all rows of the pinned candidate graph into a hash-consed arithmetic representation. It checks the complete output, 21 corresponding intermediate cuts (including `U` and `Z`), 14 witness indices, four port positions, all 67 live rows, and the 37 multiplication / 17 addition / 13 subtraction count. The author's original checker was also rerun with byte-identical output.

The independent canonicalizer flattens multiplication modulo associativity and commutativity, and normalizes signed additive trees without distributing multiplication. This checks the strong factor's precise rearrangement `(1 + I²) − Aaux = 1 + (I² − Aaux)` as an ordinary commutative-ring identity, without manually substituting the graph's strong node into the source. Both an `X := f*q` witness mutation and changing the strong-factor subtraction to addition were rejected against the complete graph output. The four graph-referenced compressed and raw port payload hashes and lengths were checked.

This is an **external syntactic/source comparison** under the stated ring identities. It does not compile `Carrier94Syntax.lean`, tie any built Lean object to that source, prove port-payload identity with the Lean constants, establish the graph's exact degree, or prove a no-zero / iPRA endpoint. No Lean process was run.

SHA-256: `check.py` `cf240534b38a96d49e0072058423ea84a9613f723638ec6f3e128fc7a7e5bc1d`; `result.json` `daa64004d2704824d0b54d62f3eb9d1cad1fc2a109adc2c3590cf4a0a69d1158`.
