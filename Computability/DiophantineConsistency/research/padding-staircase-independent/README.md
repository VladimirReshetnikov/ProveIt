# Existing padding tests used before decoding: length2011

[PROOF.md](PROOF.md) gives the complete ordinary argument for the fixed
tuple with marker1004, doubled clause1005 and prime length2011. It keeps
every942 admissible tile, the exact full descending floor-rank permutation,
all3297 coefficient entries,978 physical positions and978 native tests.
The four whole constants occupy **47313 minimal unsigned bytes**,10812
fewer than the preserved phase-split2471 tuple. This is a raw-constant
measurement, not a global-minimum or rendered-page claim.

The complete990-line proof is frozen at SHA256
`69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8`.
It includes both directions of native recovery, fresh canonical words,
the actual binary rank, ordinary safe increments, the complete controller,
both positive P66 witness maps and the uniform Carrier65 corollary. Its
immediate complete predecessor is phase-split2471, proof SHA256
`934c7984038b578a68b1396fffdb8db71a9039b01a86455a74c8639264a1b966`.

## The preliminary count argument

The whole cyclic carry bound0..57 is obtained before decoding. Every
physical input is Boolean, so binary phase b produces temporal digits
0 or2^b without field spill. The sole clause has low residue2n+k+x1
plus that temporal digit. Treat three phase ranges:

- Phases0..6 have complete low part at most2006<2048. The tests at
  bits2..10 force it into0..3, hence n<=1.
- Phases11..46 have temporal term divisible by2048, leaving low part
  at most1942. The same tests again give n<=1.
- Phases7..10 first use the existing bit3 tests at all483 fields64..546.
  The complete coefficient suffix T459 gives zero incoming carry there,
  including the reset at their predecessor63. At field64+r the reflected
  residue is2*(x0+...+xr) modulo16. Other unit terms total at most2;
  the temporal digit is divisible by16. A first prefix count4 would
  therefore produce residue8,9 or10 and fail the mask. The first483
  selectors contain at most3 ones, and all942 contain at most462.
  The clause low part is consequently at most2006, yielding n<=1 here too.

No label equality, occupation, alignment or known marker value enters
that preliminary one-hot conclusion. For every output through1003,
the reflected selector-source part is now below2^45. Any nonselector
source has coefficient index at least944, and all such terms sum to at
most the full label coefficient sum2^45−2048. Adding a temporal digit
up to rho/2 and incoming carry57 still stays below rho. This supplies
every required low reset. Marker parity excludes all nonzero phases;
only then does the whole count lemma decode all34 labels. The two full
global Start-cycle arguments exclude offsets19 and20, retaining the
actual sorted south511 self-loop.

The padding tests thus serve twice: before decoding they bound partial
selector counts in the difficult phase range; after decoding their full
916-field residue proof establishes every canonical test. No test or
unknown is added.

## Exact tuple and changed geometry

With rho=2^47, L=2011, d=94517, B=rho^L and Lambda=rho^1005, the complete
sorted Phi and the full physical support are unchanged. The closed ports
are

```
beta = B-1
K = rho^18 + rho^1004 + rho^2020 + 2*Lambda*Phi(1/rho)
MC = beta - G951(rho) - rho^960*G26(rho) - rho^1004
MF_source = beta + 8*G917(rho)-4 + (2^45-4)*Lambda
            + rho^960*G9(rho) + rho^987*G8(rho) + rho^1004
```

The first reflected coefficient is at20, and the unique collision at1004
has coefficient1+c'_1=30099357829123. The clause has extra selector1.
Its predecessor1004 is also the marker test: its complete aligned raw
value includes the adjacency sum, selector0 and the temporal marker.
The last two Boolean contributions are both retained in its reset bound.
All916 padding reflections have selector inputs at most896. The complete
product ends at2009; the untested field2010 is zero. Ordinary safe-dummy
degree bounds are1982,986,977, with the explicit collision at1981.

| Whole port | Bits | Bytes | SHA256 |
|---|---:|---:|---|
|beta|94517|11815|`a22ea3808ae016284c057d90f1bf2b76db1be2d34d11c0856f3315f6577d4b27`|
|K|94941|11868|`64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7`|
|MC|94517|11815|`2b5c9296e32616260e64a051c92892645b9aa1bf0bf4c0d931e464080702ca9f`|
|MF_source|94518|11815|`5c15fc24e4978b878ed531abf30b2dcfe255083372034612b759b65eee1f0c25`|

The whole prime/controller data is:

| Prime | Exact order of2 and B | B | K | B² | 1+BK+B² |
|---:|---:|---:|---:|---:|---:|
|47|23|37|26|6|29|
|2011|402|1283|1995|1091|674|
|120199|not prescribed|37435|114787|99283|36379|

The spacing is9246=lcm(23,402), with402=2*3*67. The auxiliary prime
is120199=13*9246+1>d and its lift is
`7300767062=1+120199*60739 mod120199²`. The proof includes the complete
CRT orbit and Boolean subset construction; these residues alone do not
establish unbounded native calibration.

## Scope, development and authorship

The ordinary proof is authored by `/root/controller_certificate`, using
the padding-staircase idea and finite implementation of
`/root/circuit_reduction` and the full earlier sorted proof by
`/root/complemented47_review`. ROOT and the mathematical peer review the
whole new ordinary proof independently. The finite certifier is authored
separately and binds the exact proof. Its frozen SHA256 is
`56b3865237699c486bbd940a88e94387d26092ac2cf89cd7f9097206dd8fb975`;
the deterministic certificate is
`fae49c56a9c57d394335c8a47da395f000a0c25cb8267d1330104eddbbc7850f`.
The complete doubled3297 array remains
`43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93`,
and its unscaled half remains
`9b33c94814bcbed4a1f0f0e62cdf48d2a026e29c6550470397da7aa491cc0d45`.

From the repository root, reproduce the certificate read-only with:

    python3 -B Computability/DiophantineConsistency/research/padding-staircase-independent/certify.py
    python3 -B -O Computability/DiophantineConsistency/research/padding-staircase-independent/certify.py

Both modes pass. Only explicit `--write` regenerates the deterministic
JSON artifacts. Every gate uses explicit exceptions. The final certifier
authenticates and imports the previously reviewed2471 verifier; it reads
the frozen exploratory code and receipt as data for provenance and does
not execute that probe. It retains full `model()` and `constants()` APIs.

The proof author independently read all351 final certifier lines, ran
both modes, and rebuilt the whole language,885481 ranks,3297 coefficients,
all low/staircase/padding arrays, all47 count regimes, both512-state graphs,
the complete controller and all four full ports without importing project
code. Actual mixed-dummy mask/rank checks through four cells also pass.
This is an independent review of the finite agent's implementation, not
an independent review of the author's own ordinary proof. Both independent
mathematical reviewers handle that separate scope.

The isolated leading probe is preserved separately. The local phase10
value2*512+1024=2048 explains why the unqualified early low-count argument
fails. The staircase fixes that specific obstruction. With the same
canonical marker relation and unchanged masks, moving the clause to1004
would coincide with the marker: the forced Start gives reflectedM'+2,
bare selector0=1 and temporal marker1, totalingM'+4 and failing bit2.
That is a scoped obstruction to that unchanged recipe, not a lower bound
for all encodings. Every frozen2471/2501 predecessor is preserved.

The theorem retains explicit ordinary arithmetic, full syntactic-refutation
and foundational contracts. The finite certificate discharges this tuple's
finite premises, while the ordinary proof supplies its unbounded witness
maps. No actual unsolvability, consistency decision, global optimum or new
end-to-end proof-assistant/internal-ZFC replay is claimed. A complete
decimal page and its rendering, if materialized, require separate review.
