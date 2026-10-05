# Independent review of the corrected short-period Lucas obstruction

**PASS with the separate v2 correction required.** The fixed-quotient
congruence, its exact base-prime criterion, the two high-carry exclusions,
and the short-period host's coprimality to33 are sound. The original opening
was false on its all-prime reading; the frozen correction preserves that
wording and supplies a sufficient counterexample. No additional mathematical
correction is requested.

## 1. Frozen artifacts and actual read scope

All files below are in `/tmp/`.

| File | SHA256 |
|---|---|
| `direct_X_short_period_lucas_obstruction_pascal.md` | 726c18d0d0fbba1d04bde35003093f25028e8556c299cf7e868e32d1dbc1f29b |
| `direct_X_short_period_lucas_obstruction_pascal.py` | 7e8f450d3a98f8b27f2dbd14ba61d32426e3c3ac1d353af58a213b5dc20a5667 |
| `direct_X_short_period_lucas_obstruction_pascal.json` | feb6155bca2a908b325e88cba27b52367e97a67e8ea80ce3d41633a5b4508ffa |
| `direct_X_short_period_lucas_obstruction_v2_pascal.md` | f8b4ac55b282857cfbcba25a53913f79aabec24ab704e63f87ce283be3c9916c |
| `direct_X_short_period_lucas_obstruction_v2_pascal.json` | 1e9899ea3934f1ac2abb9ccdf13d6cf2a942d64f2e9d79c0fff17dd8b1000f2a |

I read the full204-line original proof, full163-line helper inertly, full
50-line correction, and its30-line metadata. I inspected the original
receipt's metadata, record shapes and totals; its individual scalar results
were not recomputed or independently certified by replay. I also read the
entire168-line canonical-resonance repair note, compiler lines1--120, and
small-prime digit-rule lines1--240. Their full-file and exact span hashes
are reauthenticated in the companion JSON. The old general two-state Lucas
recurrence is inherited context, not a new result of this packet. Its earlier
finite certificates and complete compiler proof chain were not reaudited.

## 2. Independent proof challenge

Let p be odd, P=p^e>2j, r=hP-j and R=2r+1>=3. In F_p[t],

    (1+t)^(2r)=(1+t^P)^(2h-1)*(1+t)^(P-2j).

The low degree is strictly below P. Every block with high index<=h-1
ends below r, and every block with high index>=h begins above r. Thus the
upper-half binomial sum includes precisely the complete latter blocks;
there is no truncated boundary block or surviving central term. This gives

    2Y_R=X^j*(1+X)^(P-2j)*S_h(X^P) modulo p.

Frobenius gives X^P=X and P=1 modulo p-1 gives
X=2^(2h-2j+1)=xi modulo p, also for negative fixed exponents. This derives
the author's (3) for all permitted h,j,e, without a restriction h<p.

If xi=-1, the exponent P-2j is positive and the result is zero. In the
other case the power reduces to1-2j in the unit group. Writing xi=a/b,
where a,b are positive powers of2, clears only invertible denominators:
S_h(xi)=T_h(a,b)/b^(h-1). Therefore the exact equivalence is

    the designated base prime p divides Y_R iff p divides (a+b)T_h(a,b).

The latter integer is positive and depends only on h,j, so its prime set is
finite. This is not a restriction on unrelated prime divisors of Y_R.
Parity also checks: R=3 modulo4 iff h-j is odd, since P is odd.

For (h,j)=(1,2), the half-sum residue is1/27 away from3; for (2,1) it is
44/9 away from3. Thus the designated p is excluded away from3, respectively
away from3 and11. The exceptional cases establish only p-divisibility,
not the cubic prime-power divisibility required for the full scale.

For p>=5, doubling r=P-2 or r=2P-1 produces exactly e base-p carries.
In the second case the next digit totals3<p; in the first the final incoming
carry causes no further carry. Legendre's factorial valuation consequently
gives central-binomial valuation e. Choosing e>=3a in the first family
while Y_R stays a p-unit proves the retained central-carry shortcut false.
The p>=5 restriction is essential to that particular carry count.

## 3. Authentic-host consequence and retained correction

The cited fixed compiler has d=5^t with t>=1. Consequently B=2^d=-1
modulo both3 and11. For k=B-1 odd and Q=B^n, the k-term geometric sum
m is1 when Q=-1, while it is k when Q=1. Hence q=m+1 is2 when n is odd
and B=-1 when n is even, modulo these primes. It is therefore coprime to33.
Also q=2 modulo Q, Q>=32 and q>2, so v2(q)=1 and q is nondyadic.

For each odd p dividing this q, the indices R=2p^e-3 and R=4p^e-1 in
the respective permitted ranges cannot even satisfy p|Y_R. This is an
all-size obstruction to those designated index forms, independent of the
unresolved outer resonance and slack. It does not show that every possible
index has one of these forms, or that one fixed finite set controls all
unbounded quotients h. The distinction is preserved in the corrected bundle.

**Review remark 1 (required retained scope correction).** The frozen original
opening says that “the odd primes dividing the half-binomial scale belong
to an explicit finite set independent of e.” The correction's numbered
remark2 refutes that all-prime reading with h=1,j=2,p=5,e=1,R=7:

    Y_7=(20+15*128+6*128²+128³)/2=1098698=2*549349.

The odd part exceeds1 and is coprime to3, so it has an odd prime divisor
outside {3}. Factoring549349 is unnecessary. Meanwhile Y_7=3 modulo5,
exactly as the designated-base-prime theorem requires. The original files
must remain accompanied by v2; the original opening alone is not accepted.

## 4. Evidence and boundaries

The full helper correctly uses an exact integer binomial-coefficient recurrence
and computes the sum modulo2p before halving; this yields the residue of the
integer half-sum modulo p. Its special-carry factorial routine and modular
geometric recurrence match the stated scalar controls. The receipt has630
direct residue records (maximum R2365),72 carry records and48 host residue
records. This review verifies the stored counts and code/proof correspondence,
not those computations by scientific replay.

Only fresh read-only byte/span/JSON metadata checking was run for this review.
No frozen helper, predecessor, source array, compiler or builder was executed
or imported. No repository or Git mutation occurred. The corrected theorem
adds a necessary arithmetic screen; it proves neither a direct-X83 zero nor
its impossibility, a paid gate saving, or universality. The actual repaired
packed index, positive slack, and full q³|Y_R condition remain open.
