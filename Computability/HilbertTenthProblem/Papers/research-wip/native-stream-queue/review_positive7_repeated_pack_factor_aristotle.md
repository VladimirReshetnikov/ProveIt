# Independent proof and ledger for repeated-pack factorization

The three-pack replacement passes independent handwritten algebra and all-r count challenge. It preserves each packed integer polynomial for every integer assignment at the unchanged input cut. No selector, guard, positivity or AND property is used in that identity. Under a correct complete splice, the full polynomial and every supplied positive witness tuple consequently remain unchanged. This review derived its proof and grammar before emission and has now read the full frozen110-line primary. Literal successor-source certification remains a separate audit.

For r>=1, let m=8+2r, ell=62+6r and pc(t)=floor(log2 t)+popcount(t)-1. The independently derived full grammar ledger is

    (252+34r+pc(ell)+gM(m))M+(541+46r+gA(m))A
      =793+80r+pc(ell)+gM(m)+gA(m),                     (1)

with gM,gA defined and paid below. The witnesses96+6r, comparisons23, fixed roles6+18r and prescribed native exponent ell are unchanged. The r=0 branch remains the903-operation predecessor. These are symbolic family claims, with no numerical universal relator list or degree conclusion.

## 1. Actual lane grammar and unrestricted polynomial identities

The full guarded emitter was read inertly, and the quotient parent's retained-port metadata was inspected without evaluating any source rows. The eight paired slots have lengths6,6,6,6,7,7,7,7; each of the2r relator slots has length2. Their total is Nsel=52+4r. The exact lane order is m selectors, those slot blocks in increasing slot order, aggregate, height, giving ell=m+Nsel+2. The quotient successor keeps this grammar unchanged.

Write P for lane_scale, D for digit_height, B for cell_radix, J for the checksum and s_i for the raw selectors. The right selector lanes all contain J. The n_i selected right lanes of slot i all contain(B-1)s_i. Its two top lanes, in increasing order, are(D-1)J and D-1. Therefore their normalized high word is exactly

    A=(D-1)(J+P).

Appending n copies of q below any high word a gives P^n*a+q*R_n(P), where R_n=1+P+...+P^(n-1). This is a finite polynomial identity. Descending through the slot blocks with

    A <- P^(n_i)*A+(B-1)*R_(n_i)*s_i

then setting right=P^m*A+J*R_m restores every exponent in the old right pack. In particular the final two lanes appear at exponents ell-2 and ell-1, with no reversal of their order.

For left and output, retain all high Horner steps through lane index m. The left high word includes its height lane, whereas output starts at its aggregate lane because its highest height entry is literal zero. Call these retained high words Lhi and Ohi. Their low m selector lanes agree exactly, so with the single paid word

    Q=sum_(i=0)^(m-1)s_i*P^i,

the two packs are P^m*Lhi+Q and P^m*Ohi+Q. This shares an equal polynomial rather than deriving an equality from selector exclusivity. The argument does not even require J=sum s_i to establish the packing equalities; that producer remains unchanged in the complete source.

**Review remark 1 (division and the two selector polynomials).** The draft correctly retains both boundaries. R_n is built polynomially; a rational shorthand(P^n-1)/(P-1) would not justify an unpaid runtime division or the case P=1. The displayed recurrences hold for P=0,1 and arbitrary negative integers as well. Also Q is not J*R_m: at m=2,s0=1,s1=0 one has Q=1 and J*R2=1+P. That example refutes replacing the left/output prefix by the right prefix and asserts no complete compiler zero. No AND-linearity claim is used.

## 2. Every supporting operation and seed is charged

The prepared powers P2,P3,P6,P7 cost4M. R2=P+1, R3=R2+P2, U3=P3+1, R6=R3*U3 and R7=R6+P6 add1M4A. The three coefficients C2,C6,C7=(B-1)R2,(B-1)R6,(B-1)R7 cost3M. The support total is thus8M4A, with all three block sizes present for r>=1. P2 is the same existing scale_square_0=P*P, moved rather than duplicated; the remaining native exponent chain pays pc(ell)-1 products.

For(P^m,R_m), a leading binary110 or111 uses the already paid seed6 or7. Every other m>=10 starts10 and uses seed2. The prepared P3 and R3 remain needed for P6 and R6 even though the seed selection uses2,6,7. If d bits remain and e of them are1, each consumed bit doubles its current pair at2M1A; each1 bit additionally appends one power at1M1A. Thus

    gM=2d+e, gA=d+e.

With l=floor(log2 m), the three-bit seed has d=l-2 and e=popcount(m)-popcount(seed); the two-bit seed has d=l-1 and e=popcount(m)-1. These cases cover all integer r>=1, not just the saved examples. The identities R_(2n)=R_n(1+P^n) and R_(2n+1)=R_(2n)+P^(2n) prove every extension without division. Any duplicates of other native powers remain charged; the only native-power sharing claimed here is the explicit P2 row.

The entire right pack costs support8M4A, extension gM/gA, top1M1A, m blocks2M1A each, and bottom2M1A. This totals(11+2m+gM)M+(6+m+gA)A. Against the old(ell-1)M+(ell-1)A right pack, also deleting m private letter-mask products, the one private aggregate-mask product and the old-position P2 row gives savings

    (44+4r-gM)M+(47+4r-gA)A.                            (2)

The two old left/output low prefixes cost2m of each operation. One Q Horner chain and the two joins cost(m-1)+2=m+1 of each, using the already paid P^m. Their additional saving is m-1=7+2r of each. Combining with(2) gives(51+6r-gM)M+(54+6r-gA)A, exactly the difference from the quotient parent to(1).

These savings are positive for every r>=1, without any monotonicity assumption about binary costs. Indeed e<=d and d<=m-2 give gM<=3m-6=18+6r and gA<=2m-4=12+4r. The two savings are therefore at least33M and(42+2r)A respectively. These loose inequalities prove positivity only; the displayed exact bit counts determine the accepted ledger.

## 3. A second independent full-stage tally

For a direct sum, deleting the m+1 private masks changes the old outer prefix to8M+(134+12r)A. The retained high left/output Horner chains cost2ell-3-2m=105+8r of each operation. Their shared low prefix and joins cost m+1=9+2r of each. Adding the full right construction gives the three-pack stage(141+14r+gM)M+(128+12r+gA)A. The moved P2 is counted in that stage only.

| Disjoint stage | M | A |
|---|---:|---:|
| Outer prefix without private masks | 8 | 134+12r |
| Two centered forms per relator | 8r | 8r |
| Three new packs and geometric supports | 141+14r+gM | 128+12r+gA |
| Remaining native scale chain | pc(ell)-1 | 0 |
| Complete native certificate | 33 | 31 |
| Paired action | 30 | 168 |
| Selected centers and quotient appends | 12r | 14r |
| Fused positive lift | 12 | 21 |
| Recurrence right sides | 6 | 14 |
| Certificate | 229+34r+pc(ell)+gM | 496+46r+gA |
| Residuals, squares and sum | 23 | 45 |

This independently reproduces(1). No prefix mask deletion also removes height_mask=D-1, cell_mask=B-1, or the supplied selectors; those still have live consumers. The old separate block masks are replaced by their defining expressions, not by new ports.

| r | m | ell | seed | d,e | gM,gA | Full M,A | Total | Witnesses |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|1|10|68|2|2,1|5,3|298,590|888|102|
|2|12|74|6|1,0|2,1|330,634|964|108|
|4|16|86|2|3,0|6,3|403,728|1131|120|

These are direct handwritten substitutions and sum to2983 predicted saved rows, matching the final primary's reported count. They are not numerical executions or a substitute for the all-r grammar argument or literal source audit. In particular the native exponent cost is still7,8,9 for these three cases; only its initial square is relocated and counted once.

## 4. Complete splice and domain obligations

The exact consumer audit must delete all old right Horner rows, the m letter_mask rows, aggregate_mask, the left/output lower-index Horner rows and the old-position scale_square_0. It must emit that same square earlier, preserve the remaining scale-chain operands, and retain the old high left/output exits at index m. The three native header pack references change; native padding constants and all other native rows must not change. Lane metadata may retain explicit defining expressions for omitted masks, but it must not list their removed names as uncomputed executable ports.

The guarded emitter's private-mask consumers agree with these obligations on inert read. Full successor row, topology, liveness and consumer authentication remains Riemann's separate task. The fixed coefficient recipe, ordinary input, positive supplied list, comparison endpoint pairs and finalizer must be unchanged. Once the three pack exits are authenticated, polynomial substitution proves that every native residual and hence the full final polynomial agrees for arbitrary integer runtime assignments. The inherited positive guard/domain and carry-recovery theorem then transfers on exactly the same tuples, with no new existential choices or positivity assumptions.

**Open question 1 (separate source completion and further sharing, credited to root).** At the initial challenge, the complete-source prediction still required emission and independent authentication. Root has now frozen the primary, original composer and first receipt, and this reviewer has read the final primary in full with no correction. Its all-integer identity, supporting-power schedule, exact savings, disjoint tally and unchanged-domain argument agree with the independent derivation above. Full literal2983-row authentication remains the separate Riemann audit at this review's freeze. Further repetition in high left-pack history/form blocks or additional shared powers is outside the present savings. The numerical universal presentation, source degree and arithmetic optimality also remain outside this proof. No earlier frozen source is silently assigned the new count.

## 5. Read and execution scope

The full initial82-line root factorization draft, full98-line quotient parent primary and full192-line guarded emitter were read inertly. The quotient parent's r=1,2,4 retained-slot and port metadata were inspected as data; no operation array was evaluated or degree propagated. The algebra and both operation tallies above were derived by hand before any new author emission. The full final110-line root primary has subsequently been read and challenged. The new composer is byte-bound only, and its JSON is byte-bound with only top-level key/emitter-pin metadata inspected; this reviewer does not claim its literal source audit.

| Frozen principal artifact | SHA256 |
|---|---|
| positive7_repeated_pack_compiler_root.md | 1040b7330d1a3228c4b30f986d200fc89442e6812a2ea21b95ff96c10c589ab2 |
| positive7_repeated_pack_compiler_root.py | 87208277efbd316332f2a9a0bb98b68ba1fe2cd3a416e63b98ff2982078d9e50 |
| positive7_repeated_pack_compiler_root.json | 2fd115c545d412be63b469023b8e13da68648dc79ead5086df2f0aaac6b6377a |
| positive7_quotient_pair_compose_root.md | 69ffed368538686732d8f40ffb8454d1c1f506904b5a272d8153d80a243f67f2 |
| positive7_quotient_pair_compose_root.json | eda474bec49c4a2e4fef729c1cae8ed01ee940a8b63a56bb1e1d4cf64684f674 |
| positive7_guarded_two_form_compiler_root.py | 68e7653195ec8805b8726a6d2e3b7236000e476206285277f111c6a7f48850f9 |

No supplied, archived, frozen or predecessor helper was run or imported. No scientific arithmetic source/coefficient array, scalar sampling program, emitter or build was executed by this reviewer. Fresh byte or structural metadata alone may be computed. New reviewer artifacts are confined to /tmp; repository/Git and frozen source files remain unchanged.
