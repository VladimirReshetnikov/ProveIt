# Partial decoding of the signed two-rotation transport

On the actual modified-compiler slice of shared-projection83, suppose a positive zero has dyadic q and W=0. The native-mask recovery theorem supplies the two actual masks. This note proves that the negative rotation does not destroy center-clause decoding, whole-cell alignment of the positive rotation, occupancy, or horizontal overlap. It does change the vertical tests. Consequently this is a partial decoding theorem, not recovery of a computation or a new universal bound.

Every predecessor is read inertly. No predecessor helper, builder, or supplied program is executed. The companion finite checks corroborate elementary borrow and parity lemmas; they do not construct a zero of the native source.

## 1. Source and layout premises

Write V=2^b, B=V^L=2^d, q=B^N, J=(q−1)/(B−1). The actual fixed constants have K=DC+B*DR and source MF=MF0+B−1. The previously proved dyadic W=0 theorem gives

```
C=Z>0, X=2^R−2^u, u=2dx+b,
(Z−1) AND (MC*J+1)=0,
F AND (MF0*J−1)=0,
0<F<q−1.
```

Thus C is a native typed word: the origin contains selector0 (Start); selector1 (End) is absent in every cell; other native digits are0 or1, except one ignored dummy digit may be0,1,2,3. Initially no selector/copy consistency is assumed. We use only these consequences of the Pell and binomial analysis.

The exact transport equation is equivalent to

```
F = (DC+B*DR+2^R−2^u)*C mod(q−1).                (1)
```

Indeed the source has `(K+w)C+q−F−transport*(q−1)=1`, while q=1 modulo q−1 and wq=X. The negative multiplier is exactly

```
2^u = V*B^(2x).
```

Use the complete78 layout with complete76's Start/End ordering and optional high monomial, and modified75's extra dummy bit. Let a0 denote the finite tile-alphabet size, avoiding confusion with the Pell parameter. All nonanchor native exponents are below M0, and the four anchors are

```
u1=M0, u2=3M0, v1=9M0, v2=27M0=Emax.
H=Emax+24M0+3a0+1,
T1=H+2Emax+a0+1, T2=T1+2Emax+1.
```

The selected L exceeds every coefficient support, including the optional high monomial. The unshifted field DC*C+DR*(B*C mod(q−1)) has V-digits at most V/4−2, and its degrees in each cell are below L. DC includes

```
V^(3a0), V^(H+a0), V^(8M0), V^(24M0),
sum_e c_e*(V^(T1−e)+V^(T2−e)),
```

and possibly one higher, positive monomial. DR=V^H. Each genuine variable coefficient c_e is positive; ignored dummy coefficients are zero. In particular c_Emax>0. In the auxiliary clause radix A (a power of two, at least4), the lowest clause is selector occupancy, with mask A−2. A divides V. The anchor coefficient c_Emax is divisible by A, because anchors do not enter the lowest occupancy clause.

All original MF tests remain unchanged away from the bottom few binary bits at cell0: MF0 is the old field mask plus4, and subtracting1 from MF0*J changes only its lowest three bits, clearing bit2 and setting bits0,1. In particular every clause-center, anchor, horizontal, and vertical parity test of the old layout remains present.

## 2. Exact cyclic borrows

Put

```
Rword = B*C mod(q−1),
Yword = 2^R*C mod(q−1),
Nword = V*B^(2x)*C mod(q−1),
Pword = DC*C+DR*Rword+Yword.
```

Use least nonnegative residues for the three rotations. The established modified75 coefficient bound applies to Pword before alignment: every V-digit is at most V−2, and 0<Pword<q−1. The negative word merely rotates whole cells and shifts their native exponents up by1. Its within-cell support is E+1, ending at Emax+1<L; its digits are at most3. Hence 0<Nword<q−1.

Equation(1) and 0<F<q−1 show Pword−Nword is nonzero. It lies strictly between −(q−1) and q−1. If it is positive, ordinary subtraction starts with borrow0 and ends with borrow0. If it is negative, subtracting Nword+1 from Pword starts with borrow1 and ends with borrow1; the resulting word is Pword−Nword+q−1=F. Thus there are cyclic binary borrows beta_j in{0,1} satisfying, at every V-digit,

```
F_j=P_j−N_j−beta_j+V*beta_(j+1).                 (2)
```

There are no positive carries: −4<=P_j−N_j−beta_j<=V−2 and V>=32. At a digit with N_j=0, a positive P_j terminates any incoming borrow. Once N_j is identically zero on a subsequent interval, a terminated borrow cannot restart there. These statements also hold across word boundaries using the cyclic borrows just constructed.

## 3. A clean clause center stops the borrow and decodes the cell

Write R modulo bLN as b*t+ell, 0<=ell<b. The possible support of Yword in each cell lies in E*+t modulo L, where E*=E union{e_*+1} is contained in[0,Emax]. As in modified75, the separation of T1,T2 ensures at least one center T_j receives no Yword contribution, uniformly in all cells.

Fix any cell and such a center. The negative support ends at Emax+1, strictly below T_j−Emax. At T_j the positive field digit is precisely

```
Mcell=sum_e c_e*Ccell_e,
```

with no contribution from the other clause band, lower shifts, DR, the optional high monomial, or Yword.

If Ccell has any nonzero digit at f<Emax, the product of that digit and c_Emax contributes positively at T_j−Emax+f. This digit is strictly below T_j and strictly above Emax+1. It terminates any borrow, and there is no negative digit between it and T_j. Thus the incoming borrow at T_j is zero.

Otherwise Ccell is zero or consists only of the highest anchor. Then Mcell is0 or c_Emax, hence divisible by A. If an incoming borrow reached T_j, its resulting digit would be Mcell−1 modulo V. Its lowest A-digit would be A−1, which intersects the retained occupancy mask A−2. This contradicts the field mask. Therefore the incoming borrow at T_j is zero in this case also.

Consequently the exact old center expression Mcell passes the old clause mask. The old local clause argument is purely finite: occupancy is0 or1, and the parity clauses force all copies and all four anchors to match the selected window. Each cell is empty or is one genuine allowed window, with only ignored dummy digits unrestricted. The origin is a genuine Start window because selector0 is present.

This argument also proves a useful stronger borrow statement. At T_j the incoming borrow is zero, and no negative digit occurs at or above T_j. Hence every borrow is zero at each cell boundary. This conclusion was proved after, rather than assumed before, clean-clause decoding.

## 4. The positive rotation is a nontrivial whole-cell rotation

At the origin, selector0 contributes a positive unshifted digit at8M0 and at24M0. The negative support E+1 meets neither interval[8M0,9M0] nor[24M0,27M0]. This follows from all lower exponents being below M0 and the four isolated anchor exponents M0,3M0,9M0,27M0. Thus each positive digit terminates the borrow before its following anchor test.

At v1 and v2 the unshifted contribution is exactly1, the negative contribution is zero, and the incoming borrow is zero. The retained tests say

```
1+Yword_digit(v_i) is even, i=1,2.
```

For 1<=ell<=b−2 every rotated digit is even. For ell=b−1 an odd digit can occur only at the single within-cell position supplied by the upper ignored dummy bit. Neither possibility can satisfy both anchor tests. Therefore ell=0. The even dummy contribution then has no effect on parity. Both anchor targets must receive original low bits from E+t. The unique representation of18M0 in E−E and L>2Emax force t=0 modulo L, exactly as in the original anchor proof. Therefore

```
Yword=B^h*C mod(q−1), 0<=h<N.                    (3)
```

One can exclude h=0 without using the now-changed vertical tests. By Section3 there is no borrow into the origin cell. DC and DR have strictly positive minimum exponent; Nword has no exponent0. If h=0, its unit V-digit is therefore the origin Start bit1. But MF0*J−1 has its binary bit0 set, so the field mask would fail. Hence0<h<N (in particular N>=2).

## 5. Horizontal occupancy and overlap survive

All negative digits are below H. In the horizontal band, the positive rotated word in(3) has no support. The old unshifted coefficient at H+e(r,c,s), c=0,1, is the sum of the center's(r,c+1,s) bit and the right cell's(r,c,s) bit, where the right cell is the one supplied by Rword.

Suppose the center is empty and the right cell is occupied. Its right selector at some exponent s<k contributes a positive digit through DR at H+s. This is after the entire negative support and strictly before every horizontal tile-copy target. It stops any incoming borrow. The parity tests thereafter see precisely the right one-hot tile bits, so at least one test fails.

Conversely suppose the center is occupied and the right cell is empty. Its anchor at v1 gives a positive DC contribution at24M0+v1=33M0. This lies strictly above Emax+1 and below H. It stops every incoming borrow before the horizontal band. The parity tests see precisely a center one-hot tile contribution and again fail.

Thus center and right occupancies agree. The whole-cell shift1 is a single cycle on N cells, and the origin is occupied. Every cell is therefore occupied. For an occupied center the same33M0 contribution always stops the borrow before H. Consequently all horizontal tests are exact, without subtraction or borrows, and enforce

```
center[r,c+1]=right[r,c], r=0,1,2; c=0,1.
```

This proves the announced partial decoding theorem.

## 6. The remaining vertical boundary

The result does not turn the signed transport into the old positive transport. At each low vertical target e(r,c,s), the tested digit still has the form

```
center[r+1,c,s] + temporal[r,c,s]
− negative_word_digit(e(r,c,s)) − incoming_borrow
           modulo V.                              (4)
```

Here the negative word is V*B^(2x)C. It shifts tile indices by one inner-radix position, including transitions between adjacent one-hot groups. Its borrow may persist through a sequence of low targets. For example a local raw tuple(positive digit,negative digit,incoming borrow)=(0,1,1) produces V−2 and an outgoing borrow1; this is even and passes a parity mask. Therefore the old vertical equality cannot be inferred merely by deleting the subtraction term or appealing to parity.

No old marker-bijection or Start-to-End theorem is invoked. Those theorems require both old overlap relations, whereas this note proves only horizontal overlap and the altered vertical relation(4). Although no End selector occurs in C, that fact alone is not a contradiction until the vertical boundary is resolved. This note supplies no valid-program false-input construction and no proof that the candidate83 source is universal.

## 7. Provenance and finite evidence

The exact dependency hashes and read scopes are recorded in the companion JSON. The source remains unchanged. Primary dependencies are the shared-projection83 source and offset note; the dyadic native-mask theorem; modified75 Sections1,2,4; complete76 Section1; and complete78 Sections1–4. The proof uses their exact finite layout and coefficient-margin facts, not an execution of their evidence scripts.

The fresh companion helper checks cyclic radix subtraction and stopping, the occupancy-mask residue obstruction, the two-anchor parity/support lemma on a small separated layout, and one-hot horizontal occupancy mismatch. These are bounded corroborations of the all-size arguments above; the small layout is not the universal compiler. It also records the passing but altered vertical tuple(0,1,1). No full native-zero fixture, operation saving, degree improvement, or exhaustive lower bound is claimed.
