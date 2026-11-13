# Odd-block Pell anti-period in arithmetic models

`Trace74PellOddAntiperiod.odd_blocks_antiperiod` proves in every `IΣ₁`
model, for arbitrary internal `a,t,r,s`,

```text
(ycoord (r+4t(2s+1)) a + ycoord r a) mod xcoord (2t) a = 0.
```

The represented coordinate functions and indices are internal. The proof
derives the first anti-period from Pell addition and doubling, then uses
the existing represented-induction `period_mod` for the remaining even
number of blocks. It does not assume a graph zero, positivity of an index,
or a particular value of any modulus. The abscissa modulus is positive
by the generic Pell bound.

This exact-sign lemma supports the proposed coupled-Pell construction; it
does not itself produce its strong Pell witness, CRT residues, positive
coordinates, an exact graph zero, or an iPRA theorem.

Lean 4.32.0 was run with:

```text
LEAN_PATH=/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-pell-odd-antiperiod \
  Computability/DiophantineConsistency/research/trace74-pell-odd-antiperiod/Trace74PellOddAntiperiod.lean \
  -o /tmp/Trace74PellOddAntiperiod.olean
```

Actual session 90791 exited 0 without warnings and reported only
`propext`, `Classical.choice` and `Quot.sound`. Source SHA-256:
`d24fa813232f2fe99a943aa3088dfd42575efbcd64b608e3f7f61e3e5e852d6f`.
Object SHA-256:
`da03fcc3c55f905487961e022aed28726b8b2741bb20cc033eed43e56a799e2e`.
Direct imported `ArithmeticPellResidueClasses.olean` SHA-256:
`015696afb3aafad5017e2f554f4e436662811154a10ee502ce3e4791ca7f061d`.
The captured providers, full transitive/package/dynamic ancestry and
search-path selection are not independently authenticated. This is not a
coherent current-source rebuild or independent replay.
