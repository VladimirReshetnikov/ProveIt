# Independent review of the printed-port computation

The pinned printed formulas, interpreted in the usual integer sense, reconstruct all four displayed-graph coefficient payloads exactly. An independently written calculation agrees on the decimal seed, all 430 decoded actions, all 942 tile assignments, all 941 non-start ranks and physical rows, and the four full integer values. No concrete formula-translation error was found. This is a finite external Python/source comparison; it is not a Lean evaluation or proof of TeX/PDF semantics, endpoint-provider provenance, or any consistency equivalence.

The independent decoder uses sequential Euclidean divisions of the seed payload by each mixed radix, instead of the reviewed checker's growing prefix products. Its base-16 flag digits are likewise consumed sequentially only where the mask bit is one. This gives the same actual first action `(u,v,d)=(1,1,1)`. Although the printed formula requests mask positions through 644 while `N` has only 636 bits, the final nine requested bits are necessarily zero; both calculations implement that literal convention. The tile reconstruction checks each indexed table family for unique assignment and complete coverage, and the independent ordering computes descending weight ranks, then checks the printed floor expression at every non-start index. The equality follows because all selector weights are below `2^44` and the 941 non-start weights are distinct.

For `K`, each summand of the printed `2*Lambda*Phi(1/rho)` is expanded into its integer coefficient and rho exponent before Horner evaluation. For example, the two `G_8(2x)` contributions have rho exponents `1005-978-j` and `1005-969-j` with coefficients `2^(11+j)` and `2^(28+j)`; the two `G_9(2x)` contributions use `1005-960-j` and `1005-942-j` with coefficients `2^(19+j)` and `2^(36+j)`. All exponents are nonnegative. The computation independently checks the source recipe's control sums and the source-declared physical row order.

For the masks, independent rho-digit/Horner evaluations implement the printed low-support complement and the high-digit formula, including the added beta in the fourth port. The checker compares complete big-endian integers to the gzip payloads, including their declared compressed/raw hashes, lengths and bit counts. The mapping is `beta ↔ beta`, `K ↔ K0`, `mu ↔ MC`, and `omega ↔ MF`.

The page fragment is byte-for-byte pinned, but its formulas are **manually interpreted** in both calculations. The checker does not prove that TeX macro expansion or the PDF renders those formulas, nor that every referenced source theorem was re-elaborated with authenticated dependencies. The matching source definitions and recorded endpoint theorems are evidence with their own provider limitations. Those boundaries remain essential even though the finite integer comparisons pass.

From `Computability/DiophantineConsistency`, reproduce the independent checks with:

```sh
python3 -I -S -B reviews/current14-printed-port-recipe-independent/check.py | cmp - reviews/current14-printed-port-recipe-independent/receipt.json
```

No Lean, build, staging, PDF interpretation or model transfer was run.
