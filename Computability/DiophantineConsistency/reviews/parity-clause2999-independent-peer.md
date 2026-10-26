# Independent review of the complete parity-clause2999 tuple

Reviewer `/root/controller_certificate`; proof author
`/root/complemented47_review`; finite probe/certificate author
`/root/circuit_reduction`; ROOT coordinates the candidate and promotion.
No reviewed artifact was changed by the reviewer.

**PASS.** I read the entire653-line proof,474-line probe,558-line final
verifier and probe note. Probe and final verifier each passed in normal
and optimized read-only modes. A separately authored, fully read,
stdlib-only script imported no project module and independently decoded
the whole language, reconstructed every coefficient, all low-field
arrays, complete geometry, phases, count cases, masks, controller and
four whole integers. No gap was found in the ordinary proof or new
finite premises. No page existed for this candidate during this review.

## Exact reviewed versions

Paths are relative to `Computability/DiophantineConsistency`.

| Artifact | SHA256 |
|---|---|
| `research/parity-clause-independent/PROOF.md` | `c4ce22beb76dc7d39d17d83fe8be2fc8f6a20057ee5fd576556f173c70400b22` |
| `research/parity-clause-independent/certify.py` | `16148288f5151540b365deae68624669b037fe96ac2023ea3969ed11ed61d210` |
| `research/parity-clause-independent/certificate.json` | `7a79628bc8ade1e82906ae2fe9c9c0324c9ab68f5032a46369326c3297c1157b` |
| `research/parity-clause-independent/coefficients.json` | `626c3a671efc045c6127991a2e636c7db64a9afb146a3402c6e6322e1fa9854f` |
| `research/parity-clause-probe/probe.py` | `ab6acf18cc8ab940a452052f08f11f9e06ee115a63e4934c5e30bc036065efda` |
| `research/parity-clause-probe/RESULTS.json` | `a843df450f4e07b76c797f8b3844818f6792a2a02270b9d0cb683ac8c95a3b87` |
| `research/parity-clause-probe/COEFFICIENTS.json` | `c3104cc804ba947619d6edf58495299919558917292e15609b8c28cc7fb2f181` |
| `research/parity-clause-probe/NOTE.md` | `7c04ebac2ed331d3f29673f26f0836a33bae0abdeb91d768bd16a77afcdacbe9` |

The proof's immediate source is the completely reviewed single-clause3037
proof `e8f84bfe49a1471ffc693b00b14a8400fe5e438fa0170f15f4444bc56cbf53c2`.
The final verifier pins the full new proof and preserved7309 verifier
`9e48fa6e071e279c271d4facc87aec2a7026369a2ab3b3056a68e33c41ae479d`
before import. That reviewed chain authenticates the full radix55 page
`440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`
and exact decoder. All executable gates use explicit exceptions and
remain active under `-O`; neither reviewer run used `--write`.

## The new low-field argument

The admissible942 language, all3297 coefficients and978 Boolean physical
positions are unchanged. This includes the zero-weight marker1005 and
Boolean dummy977. The actual first mask still forces selector0 at the
origin, allows new selector1, and rejects dummy digits2/3. The two bare
kernel terms are18 and1005, with the shared18 monomial occurring once;
spatial transport has residue9. Only the reflected center moves to1956.

The first reflected exponent is now971, so exact absence of reflection
at every low test would be false. The proof explicitly replaces that
condition by a complete parity and carry bound. At output h<=1005,
each reflected coefficient has index `1956+f-h>=951`. Such coefficients
are label weights, hence even. Distinct f give distinct coefficient
indices, so their entire sum is at most the label sum M−1024 without
any decoding premise. Combined with at most three bare/spatial units,
any fractional temporal digit at most rho/2, and incoming carry29,
the actual low total is below rho. Every low outgoing carry is zero.

I independently constructed all1006 complete arrays of triples
`(physical source, coefficient index, coefficient value)` and compared
their full serialized hash with the receipt. Each nonzero coefficient
is an even label weight. The actual maximum is34359737344, below the
uniform M−1024 bound. The complete temporal copy tests960..968 have no
reflected terms; every spatial-copy and marker reflection is included
and even. The independent parity maps agree with every intended source.

Thus the forced Start marker test has current contribution `1+E_1005`,
where E is even, and no incoming carry. Its mask forces an odd temporal
digit. Boolean source digits in fractional phases1..46 are all even
and cannot spill, so the fractional phase is zero before any count or
label conclusion. This argument remains valid with the new reflections.

Once the fractional phase is zero, every temporal digit is Boolean in
every cell. The sole clause is exactly the complete non-temporal count
value: the bare marker's possible input951 is absent, and the other
bare/spatial inputs are absent. A temporal contribution tau may occur;
the proof does not claim that this clause was already clean. It applies
the stronger count lemma with `k'=k+tau<=30` and
`n+k'<=942+30=972<1024`. The low tests force n+k' to0/1, so n<=1 and
occupied cells have both k=0 and tau=0. There is then no carry into the
34 label tests, and the complete old label-value argument gives either
the empty word or exactly one tile with all its labels.

My independent enumeration of all56580 triples `(n,k,tau)` finds exactly
`(0,0,0),(0,0,1),(0,1,0),(1,0,0)` passing the low count bits. This finite
enumeration checks the small-summand premise; the ordinary proof supplies
the full unbounded Q/label argument. It correctly keeps the marker
arbitrary at this stage.

## Alignment, complete masks and native equivalence

The marker's odd temporal bit restricts the global field offset to
`r=1005-f`, one of978 physical possibilities in0..1005. There are27
possible nonzero temporal clause sources: r951/source1005 and
r971..996/source985..960. The independent reconstruction reproduces
this complete list. They are Boolean, as required by the new count
lemma; their absence is not assumed.

After count decoding, the forced Start south bits1..8 impose targets
961..968 with zero reflected terms and zero incoming carry. Exhaustive
enumeration of all2999 offsets yields the same934 support candidates:
zero,932 multiple-selector contradictions and offset20. The last case
forces selector941 and its south bit0, contrary to that exact tile's
complemented south74. The full source table fixes this calibration.
The dependency order is therefore marker parity, Boolean count,
decoded Start labels, then complete field alignment.

After alignment the even low backgrounds preserve every one of the17
color equalities and the shifted marker relation. The latter follows
the temporal successor's Start indicator, not an all-one flag. Positive
colors propagate occupation around the spatial cycle, and Start's
north76 versus south510 excludes zero stride. The exact admissible
bijection recovers the retained full computation/refutation.

The sole predecessor1955 is exactly `Aadj+x950`, with the extra unit
coming from the bare marker times south-bit8. I independently computed
the entire convolution there and at clause1956. The one-tile bound
`Aadj<=2M-1024` makes `Aadj+x950+29<rho`, resetting its carry. After
alignment the clause has no temporal input and is exactly0 or M+1.
The complete Boolean convolution maximum remains3829914518400942,
at1956; the global29 envelope passes.

The last product2961 is exactly `c0*x1005`. Its outgoing carry is zero,
so every later field is actual zero. All19 full padding fields2962..2980
and23 low bits at2981 therefore pass. The positive padding sum equals
`2^23*rho^2981-rho^2962` and has916 bits. The core has62 bits, giving978
native tests and d−978 MC bits. I reconstructed the closed MC, exact
source shift by beta, scalar boxes, origin residues, whole populations
and all four integers.

Fresh canonical words and every allowed Boolean dummy subset retain
the low parity tests, resets, occupied clause and top zero band. Hence
the strict bounds `F<q/rho<q/7` and `2C+F<q/3` hold. Actual mask
populations remain `(d-978)N+1` and `978N+1`, yielding rank population3t+2
and residue3 modulo4. Besides the verifier's1/2/3-cell samples I checked
a four-cell mask-compatible word using new selector1 and a separate
Boolean dummy. These are rank-algebra tests, not canonical tilings.

Safe dummy exponents2933/986/977 have the required degree-plus-one
margins for the ordinary bound below q/rho². The exact ordinary F and
rank increments, safe subset controller and positive transport are
proved at the new tuple. Both full positive P66 witness maps are
restated, including the retained sign/positivity stages and integral
Pell bridges. The15-variable,66-operation, degree157 front is the
retained uniform symbolic construction evaluated at these new ports.

## Controller, whole costs and negative controls

The independent reconstruction decoded all436 seed characters,430
actions and942 direct table rows, and compared the exact admissible
index map before computing all3297 coefficients. The tile-list hash
is `8ac6dabe3485f8c29fe15fdb9f98a8f57823be532d01e12bcbdc43b04a95874c`;
the full coefficient hash is unchanged as recorded above.

Trial division independently verifies47,1499,2999 and965357 prime.
Every length2982..2998 is composite, so2999 is the first eligible prime
for this particular full-tail-padding layout. This is a local statement,
not a global minimum. Exact orders of2 andB are23 and1499 at the two
fixed primes, with all proper-order tests and coprimality to d140953.
Spacing is34477 and `lambda=965357=28*34477+1>d`.

| Modulus | B | K | B squared | H |
|---|---:|---:|---:|---:|
|47|42|15|25|45|
|2999|1159|753|2728|2747|
|965357|76520|20983|420195|650665|

Independent termwise and whole-integer modular routes agree with the
certificate, which also checks dense and direct-table routes. The lift
is636010979096=`1+965357*658835`, giving valuation exactly one. The full
new K satisfies all required units, discharging Pcpc.

| Port | Bytes | SHA256 |
|---|---:|---|
| beta |17620|`152ec27c6beb9059f5bd8fe947343bd08779f8283305c53a92a4b381f099517a`|
| K |17673|`a75e946ce65a72a343dfbc563dbbbfbcc05654fd24b2aea6863dc925a7e829f7`|
| MC |17620|`c1fef2fb9546003a6634e1c6eab8091af2932d6a47fdae60c6325b52a98fa7e7`|
| MF_source |17620|`61583bc9a76b479301acc6d540a48b596326fd3c7d830a6cc9cb721d9751fd7e`|

Total70533 is892 raw bytes below3037's71425. The independent whole
ports and arrays match both exploratory receipts and the final
proof-bound certificate. A page/rendering review remains separate.

The center1955 negative control computes the collided bare/reflected
coefficient correctly: it adds one to the south-bit8 contribution at950.
The forced Start has that bit one, so its canonical occupied clause is
M+2 and meets forbidden bit1. This is a scoped canonical obstruction
for that unchanged layout, not a global impossibility theorem. The
marker-omission test still rejects physical geometry and population
even though weighted coefficients are unchanged. The marker1004 local
phase-pattern control remains explicitly local.

This review does not decide consistency or actual unsolvability, claim
a global minimum, introduce a new native compiler, or report a fresh
end-to-end proof-assistant/internal-ZFC replay. The ordinary equivalence
uses the retained explicit arithmetic, syntactic-refutation and
foundational contracts; every new finite premise is discharged above.
