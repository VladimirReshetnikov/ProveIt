# Trace75 first Pell index residue

For an IΣ₁ model satisfying β≥31, `MC<β` and `MF<2β`, a positive trace75
zero yields a positive first Pell index `n` with
`2*ycoord n (2*(XY²−1)+1)=k` and
`2*n % q⁴ = (rankNat+1) % q⁴`. The port `K0` is arbitrary. The proof uses
the unscaled first parameter `P=XY²`, verifies `q⁴ ∣ 2P` from the actual
graph definitions, applies the Pell residue theorem, then joins the natural
offset congruence. It does not yet prove exact index equality or a halt/iPRA
equivalence.

`run-firstresidue.py`, `observations/firstresidue-attempt01/`: Lean exit 0,
no warning/error; object
`/tmp/trace75-firstresidue-9thrt5_j/Trace75FirstResidue.olean`, SHA-256
`048623caba4e3c2b20d9e7640793bdf8d37274650a92f85034fbb5c5fe9728a6`.
The source's draft comment predates this accepted check. Direct imports and
selected objects are pinned; historical transitive/package ancestry and
external graph/file binding are inherited limitations.
