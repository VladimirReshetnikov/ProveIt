# Independent proof review of the relator-plane action

The relator-plane factorization passes independent proof and count challenge. For each fixed P in SL2(Z), it appends the combined relator/inverse increment from the same eight raw selected words using21M+19A=40 operations, versus24M+24A=48 for the stated uniform coefficient-table append. The eight-operation saving is local. This review certifies no new complete wrapper, numerical universal bound, degree or optimality result.

I read the full author draft and the inherited paid sparse-action/inverse-pair interfaces. The proof below independently checks the invariant, integer lattice basis, all central/sign/permutation cases and complete runtime ledger. No source or coefficient array is evaluated, and no author/predecessor program is executed or imported.

## 1. The invariant covers both independent input slots

Write P=[[p,q],[s,t]] with pt-qs=1 and use the exact inherited symmetric-square representation

    S(P)=[[p^2,-2pq,q^2],[-ps,pt+qs,-qt],[s^2,-2st,t^2]].

For n0=(s,p-t,-q), the three components of n0*S(P) reduce respectively to s(pt-qs), (p-t)(pt-qs), and -q(pt-qs). Thus n0*S(P)=n0. The inverse matrix has parameters(t,-q,-s,p), whose normal is -n0. Hence the same normal fixes S(P^-1).

Both differences therefore have image in the same integer plane after composition with the fixed three-by-four decoder

    C=[[1,0,0,-1],[1,1,0,-2],[2,0,1,-4]].

In particular n0 annihilates every column of W=[(S(P)-I)C | (S(P^-1)-I)C]. The two four-word input slots are independent. No cancellation of equal inputs, one-hot selector assumption, positivity or native equation is used to obtain this exact linear-map identity.

The only zero-normal case is q=s=0,p=t,p^2=1, namely P=I or -I. Then both differences and W vanish. The author's uniform default n=(1,0,0) is valid and avoids taking a gcd or dividing by entries of a zero normal. Keeping the resulting zero coefficient products is a legitimate uniform upper schedule, even though this special action could be omitted more cheaply.

## 2. The integer basis, not only a rational rank factorization

In the nonzero case, divide n0 by its positive three-entry gcd and permute the output coordinates so the first entry n1 is nonzero. The same permutation is applied to W's rows. Let g=gcd(n1,n2)>0 and choose fixed integers a,b with a*n1+b*n2=g. Since n is primitive, gcd(g,n3)=1.

For any integral column (x,y,z) in this plane, n1*x+n2*y+n3*z=0 implies g divides n3*z and therefore g divides z. Thus

    beta=z/g, alpha=b*x-a*y

are integers. With

    u=(n2/g,-n1/g,0), v=(-n3*a,-n3*b,g),

the reconstructed first coordinate is

    [n2(b*x-a*y)-a*n3*z]/g
       =[b*n2*x+a*n1*x]/g=x,

and the second is

    [-n1(b*x-a*y)-b*n3*z]/g
       =[a*n1*y+b*n2*y]/g=y.

The third is g*beta=z. This proves a full integer-plane factorization for every column; no lattice index or unproved divisibility condition remains. The representation is unique: its third coordinate fixes beta, and u has nonzero second coordinate -n1/g, which then fixes alpha.

The proof covers negative entries, n2=0 and n3=0. In the central default one can take g=1,a=1,b=0; W=0 gives zero alpha and beta coefficient rows. The output permutation is inverted when the reconstructed values are added to the original(d,e,f) accumulators. The eight selected-input columns are never permuted or replaced. The required output wiring is a fixed alias, not a runtime test or arithmetic operation.

All quantities n,g,a,b,u,v and the eight pairs of alpha/beta coefficients are fixed compiler numerals prepared from the actual P. Their gcd, Bézout computation and exact divisions occur only in that finite preparation. They are not independent arbitrary coefficient ports, supplied witnesses or unpaid runtime operations. Signed fixed numerals and computed intermediates are allowed by the existing integer-polynomial model.

## 3. The complete append cut costs21M+19A

The two eight-term coefficient forms cost16 multiplications and14 additions, with products by zero, units and negative constants included. Reconstructing the first two coordinates uses two products and one sum each; the third uses the single product g*B. This is5M+2A. Adding the three reconstructed outputs, in the inverse fixed permutation, to the already existing accumulators costs3A. The complete total is therefore

    16M+14A +5M+2A +3A =21M+19A.

The zero third entry of u is the only omitted reconstruction term; it is identically zero by the basis formula, not zero only on a selected input. No conversion of raw selected words, selector extraction, inverse-slot sum or accumulator addition is silently supplied by this count. The raw inputs and existing signed accumulators are precisely the declared cut.

The uniform predecessor charges24 coefficient products and24 additions into the same existing accumulators. The new schedule saves3M+5A. It need not beat a separately optimized special relator, a pruned coefficient pattern or every alternative representation; no such optimality is asserted.

**Review remark 1 (retained missing-append count).** Root's preliminary18M+25A claim for decoding both triples before the two difference actions omitted three final accumulator additions. Each decoded triple can be obtained with5A: u=Z4-Z7, h=u-Z7, y=Z5+h, hh=h+h, z=Z6+hh. The two fixed three-by-three difference actions cost18M+12A; their three coordinate pair sums cost3A, and appending them costs another3A. The complete alternative is18M+28A=46, not18M+25A for the append cut. The author's numbered remark preserves the incorrect preliminary count and its repair. This review independently checks that repaired comparator as well as the new40-operation schedule.

## 4. Exact substitution and limits

For every integer assignment to the eight selected words and the existing accumulators, the new three appended values equal the old Wz contribution in the original output order. Thus each relator replacement preserves its boundary polynomials under the valid fixed coefficient recipe. It changes no selector, positive hat, input loader, native domain, history coordinate or lane. Signed temporary values create no new positive-witness requirement.

Appending r such pairs to the separately verified30M+168A paired-letter increment gives(30+21r)M+(168+19r)A at the six-increment cut. The inherited10M+21A unscaled postprocessor gives(40+21r)M+(189+19r)A; its12M+21A recurrence-fused form gives(42+21r)M+(189+19r)A. These remain local paid cuts. None of these formulas is a claim that the future complete source has already been emitted or audited.

The universal presentation, its numerical r and its actual relator matrices remain unmaterialized. Integrating this recipe requires an independent literal-source audit of coefficient roles, input/output permutation bindings, consumers and all complete-wrapper arithmetic. Existing frozen inverse-pair and complete-compiler packets are unchanged. The published complete source does not yet include this plane saving.

## 5. Exact bindings and execution scope

The final author proof is positive7_relator_plane_action_pascal.md, SHA256374736feae3677e61a7e7676847d199956cef7a5664d1f83f5f57dc739ea3819. Its proof-only metadata is positive7_relator_plane_action_pascal.json, SHA2567d8e86016f20f4c69764b15ce65ddba83f59a486d3233f8fc024e78417efa162. The full217-line proof and final metadata were read; its final change only records evidence and review scope. No mathematical correction was requested.

The full353-line paid sparse-action proof and322-line inverse-pair proof were read as inherited cut dependencies. Their exact immutable bytes, the final author pair and this review are bound in the companion metadata. All invariance, lattice and count checks above are handwritten derivations. Only fresh byte and metadata authentication ran; there is no reviewer scientific helper, source-array evaluation, coefficient propagation, numerical sampling, build, repository edit or Git mutation. The separate future source-composition review must bind this local result rather than infer a complete compiler count from it alone.
