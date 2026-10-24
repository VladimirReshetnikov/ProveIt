# Independent audit: fixed-modulus orientation and separation

## Recommended theorem

Let A be a nonzero even integer divisible by3. Let B≡3 (mod4) with 1<B<|A|/2−1, and let C be odd with C≡−1 (mod3). For the modified Lucas certificate, xi≠0 and DFI square imply C=u_B(A), without any A−2 divisibility hypothesis.

Here is the complete change from Sun's argument. C is nonzero, so its positive, pairwise coprime certificate factors are separate squares. Obtain Lucas indices s,mu,t with C=u_s(A), 4E=u_mu(A), H=u_t(2G), n=|mu|>3 even, s,t odd. The unchanged index comparison gives s≡±t (mod2n); the rank-divisibility input gives C|n; the direct certificate congruence gives t≡B (modOmega). Hence s≡±B (mod2C). None of these conclusions used the removed congruence: its earlier role in Sun's proof was merely to ensure C odd and nonzero, which is now explicit.

For s=±1, C=±1 and D=A². Since u_n(A)=±4A²xi, writing n=2j and using u_(2j)(A)≡(−1)^(j−1)jA (modA²) proves A|j. Thus 2|A| divides both 2n and Omega=16A²xi. The two congruences for t force B≡±1 (mod2|A|), impossible in the stated range. This covers negative A and xi. The paired recurrence congruence follows by simultaneous induction with u_(2j+1)(A)≡(−1)^j (modA²).

Now |s|≥3, |C|≥|A|>B and |s|≤|C|. The index congruence therefore gives the equality s=±B. As A≡0 (mod3) and B≡3 (mod4), u_B(A)≡−1 (mod3). The sign s=−B contradicts C≡−1 (mod3). Thus s=B. This proves the theorem.

## Polynomial specialization and unconditional separation

Use C=6c0−1 and delta=9Delta−3. Put r=bQ, a=r+delta(rz)², d=DFI. The source gives 3|A and r≡1 (mod3) on every signed input, before positivity recovery. Therefore D≡0 (mod3), d≡0 (mod3), and a≡1 (mod3). In particular a≠d unconditionally. The norm finalizer's rational-square extraction and nonzero Sigma argument apply unchanged.

After a is known to be a square, its factorization r[1+delta r z²] has coprime nonzero factors. The residue r≡1 (mod3) rules out a negative square, and hence both factors are positive squares. Factoring r=bQ recovers positive square b and Q as before. For Delta≤0, delta≤−3 and 1+delta r z²<0 since r≥4 and z≠0; contradiction. Thus Delta>0. The remaining source-bound and reverse-bridge argument is unchanged; in particular the strengthened theorem recovers C=u_B(A), and only then is h=(C−B)/(A−2) introduced as a proof-only integer.

Completeness uses the same canonical C=u_B(A). It is odd and is −1 modulo3, so c0=(C+1)/6 is integral. Also delta=3(3Delta−1)>0 has 3-adic valuation exactly1. As r is a positive square, delta r is positive nonsquare. Pell's theorem supplies nonzero z making a square. The unchanged full-residue interpolation theorem then supplies xi and y; the intersective merger and final m complete the root.

There is no extra variable and no hidden division in the polynomial. Delta is integer throughout. The linear guard delta=9Delta−3 takes exactly the same multiplication-and-subtraction count as 3Delta−1. The final H1873 shared-source composition is independently checked at481 live operations and exact degree1,576,864. Its literal SHA256 is a53192c84497ece7ef3c8955e6b3ae63a62c748af16f89e41fa7f3ebb7e99315. All12 fixed payloads pass byte-hash verification. The actual diagonal leading coefficients are974311937,125416763,95373471 modulo1000000007,1000000009,998244353. The independent direct-formula tail check passes360 signed modular assignments; the source prefix is covered by a separate source audit. See integer10_DEGREE_AUDIT.json and integer10_TAIL_AUDIT.json.

## Scope and verdict

PASS as a mathematical reduction relative to the same explicit Lucas and source/compiler dependencies. No new Lean or Rocq certificate is claimed. The exact cited input is Sun, arXiv:2609.01594v1, Lemma2.2, Corollary2.1 and the full-residue interpolation Theorem4.1. The novel exceptional-index and orientation steps are supplied above rather than attributed to that paper.

The theorem cannot simply omit all slice conditions: A=12,B=3,C=0,xi=1,y=0 gives DFI=4 while u_3(12)=143.
