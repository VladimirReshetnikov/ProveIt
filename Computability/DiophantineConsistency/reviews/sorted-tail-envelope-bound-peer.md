# Independent review of the fixed full-suffix lower bound

Reviewer `/root/controller_certificate`; note author ROOT. I read the
whole `research/sorted-selectors-probe/TAIL_ENVELOPE_BOUND.md`, SHA256
`2d57c948c520f9443a960166b802fd2abc543b7bb4985537a7ba6b6d1bf1ef8a`,
and independently recomputed its finite bounds. **PASS within its stated
fixed-family restrictions.** No correction is requested.

The fixed sorted array has SHA256
`43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93`.
For the independent calculation I also loaded the previously authenticated
unpermuted admissible942 array, doubled its entire941 non-Start selector
multiset and all label entries, and checked their complete equality with
the corresponding sorted data. No project module was imported or executed.

All941 non-Start weights are positive and distinct. Their fixed label
sum is35184372086784=2^45-2048. At center1492 the suffix beginning489
has453 non-Start selector slots and includes every label. Selecting the
453 smallest weights minimizes that sum over every Start-fixing
permutation. At center1493 there are452 such slots. Independent whole
sums and exact margins are:

| Quantity | Exact value |
|---|---:|
| Minimum suffix489 |71354583835530|
| Reset threshold rho/2-60 |70368744177604|
| Failure margin at1492 |985839657926|
| Minimum suffix490 |69992810240904|
| Success margin at1493 |375933936700|

Descending order attains both minima. The exchange argument is valid
for the complete multiset, and decreasing the center only enlarges its
suffix for each fixed ordering. Thus no allowed permutation makes the
specified strict full-suffix reset inequality hold below1493. This is
a lower bound for that sufficient reset method, not proof that an actual
carry or native witness fails under a sharper argument.

With the marker fixed at1004 and at least one zero field above the last
product, L>=C+1004+2>=2499. Direct multiplication verifies
2499=3*7^2*17, so it is not squarefree;2500 is even. The next length2501
is41*61 and the separately reviewed full controller passes there. Hence
the claimed shortest length follows under precisely these combined
restrictions; stronger or different controllers are outside the claim.

The whole-port bit lengths d,d+424,d,d+1 also follow from the fixed
template: K's leading term is B*rho^9 with the remainder below B; MC
retains the top bits of beta; and beta<MF_source<2beta. Their minimal
unsigned byte lengths are monotone with L. At2501 they are respectively
14694,14747,14694,14694, totaling58829. I independently recomputed these
roundings. The note makes no lower-bound claim about a different packing,
marker, reset method, top-field interface or controller, and no global
minimum claim about Diophantine representations.

This review changes neither the bound note nor any accepted proof,
certificate, page or coefficient. No commit was made.
