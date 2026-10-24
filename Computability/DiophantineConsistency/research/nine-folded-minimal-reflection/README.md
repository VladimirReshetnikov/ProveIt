# Share Fminus1: nine positive variables, 406 / 414 operations

This new sibling preserves the complete frozen reflected-parameter packet.
It uses the actual product already feeding `F=1+Fminus1` to define

    G=A*Fminus1+F=F*(A+1)-A.

The two displayed forms are universally identical. The previous parameter
was `F*(A+C+1)-A`; its polynomial is different, so the correspondence with
that parent is existential, with fresh positive auxiliary witnesses.

| Whole tuple | Positive variables | Live operations | Exact degree |
|---|---:|---:|---:|
| original31, boundary_simple.json | 9 | 406 = 238 mul + 150 add + 18 sub | 1,191,570 |
| compact54-sharp, compact_simple.json | 9 | 414 = 242 mul + 154 add + 18 sub | 1,316,546 |

The complete original and compact fixed tuples remain separate. All source
registers, nine positive domains and coefficient payloads are retained.
The new G needs two operations, using the existing Fminus1. Its strict
bounds and congruences are

    G-F=A*(F-1)>0, G=-A mod F, G=1 mod C.

The reflected signed-folding proof applies unchanged. Soundness uses no
auxiliary-index parity premise. Completeness uses the actual odd
`B1=2R+1`, so `psi_(-A)(B1)=psi_A(B1)=C`, then the same matrix periods
and positive n construction. PROOF.md includes the zero-margin and
negative-margin branches before root integrality and the complete index
and source boundary. The smaller G remains greater than F, which is all
those majorant arguments require.

The literal producer deletes three private parameter intermediates from
the frozen408/416 parent, replaces the G subtraction by an addition, and
inserts one multiplication. It certifies the exact stored Fminus1 product;
no extra subtraction, hidden operation, or unused Lambda is added. All
other parent nodes retain their literal operators and mapped operands.
The independent checker imports no producer or emitter. It verifies all
parent nodes, all new nodes, the complete norm, universal sharing identity,
whole fixed integer values, exact degree and five rejected corruptions.

Degree remains that of the preceding reflection. The centered norm has a
unique highest-degree term. Nonzero highest homogeneous values modulo
three primes with every actual coefficient certify attainment over Z.
The raw syntactic bounds1,599,032/1,766,808 are kept separately. Finite
recurrence/folding/period controls supplement the unbounded ordinary proof.

```sh
python -B Computability/DiophantineConsistency/research/nine-folded-minimal-reflection/build.py --check
python -B Computability/DiophantineConsistency/research/nine-folded-minimal-reflection/check.py
python -B -O Computability/DiophantineConsistency/research/nine-folded-minimal-reflection/build.py --check
python -B -O Computability/DiophantineConsistency/research/nine-folded-minimal-reflection/check.py
```

Both mode receipts and all four logs are included, with a closed SHA256
manifest. The source-to-refutation calibration remains the pinned whole
parent dependency. No new Lean, internal-ZFC theorem, or optimum claim is
supplied. All accepted parents, common documents and canonical pages remain
unchanged.
