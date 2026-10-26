# A lower bound within the fixed full-suffix reset method

This note concerns only the present doubled weights, fixed34 label
positions, Start at selector0, marker1004 and full-suffix carry envelope.
It does not bound all native equations, all carry arguments, or all
Diophantine representations. The sorted2501 construction meets the
bound within this particular family.

Let the941 non-Start doubled selector weights be the fixed multiset
reconstructed in COEFFICIENTS.json. All are positive. The fixed doubled
label weights sum to2^45-2048. For a clause center C, the present proof
bounds every reflected field h<=1003 by the complete coefficient suffix
beginning at C-1003. Its sufficient unconditional reset inequality is

    suffix_sum + rho/2 + 60 < rho,    rho=2^47.

At C=1492 that suffix starts at489. For any permutation fixing Start0,
positions489..941 contain453 non-Start weights. Their sum is at least
the sum of the453 smallest weights in the full fixed multiset. All label
weights also belong to this suffix. Descending order attains that minimum:

    min suffix489 = 71354583835530,
    rho/2-60      = 70368744177604.

The minimum exceeds the threshold by985839657926. Thus no permutation
can make the stated suffix inequality hold at C=1492. Moving C lower
only enlarges the suffix for each fixed ordering and cannot repair it.
This proves C>=1493 for this exact sufficient-bound method.

At C=1493 the suffix begins at490 and contains452 non-Start weights.
Descending order gives

    min suffix490 = 69992810240904,
    (rho/2-60)-min suffix490 = 375933936700 > 0.

The full sorted coefficient array therefore attains the smallest center
licensed by this method. This is an exchange argument about a finite
multiset: replacing any selected larger weight by an omitted smaller one
never increases the suffix, and repeated exchanges give the sorted tail.
It does not use a sampled search over permutations.

The existing top-zero-field interface also requires

    L >= C + 1004 + 2.

Consequently L>=2499 in this family. The complete controller template
requires L odd and squarefree:2499=3*7^2*17 fails squarefreeness and2500
is even. The accepted finite sorted tuple uses2501=41*61 and satisfies
every additional controller condition. Thus2501 is the shortest length
within these combined fixed reset and controller restrictions.

For this template the four port bit lengths are d,d+424,d,d+1, with
d=47L. Their total minimal unsigned size is monotone in L and equals
58829 bytes at2501. This gives the corresponding scoped lower bound;
it does not constrain a different coefficient packing or controller.

ROOT recomputed both full minima directly from all941 non-Start entries
and every label entry, checked equality with the actual sorted suffixes,
and checked the two exact threshold margins above. The full array hash is
`43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93`.
The earlier full probe and independent finite review authenticate that
array and its actual tile weights. Accepted proof and receipt files are
unchanged. Further reductions must alter at least one stated restriction;
this note supplies no global minimum claim.
