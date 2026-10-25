# Independent review of the parity-normalized product equations

## Disposition

**PASS at the stated ordinary-mathematical boundary.** Both new polynomials have eleven unrestricted integer variables and compose with the same inherited source34/native/refutation calibration as the authenticated incoming single-product parent. No consistency assumption, newly asserted absence of solutions, global optimum or fresh end-to-end proof-assistant endpoint is used. The new reductions are not pointwise identity rewrites of the incoming polynomials: the guard changes, and completeness chooses fresh Pell witnesses.

Audited final files:
- `scalar/product11_degree966.json`: 109 live operations, exact degree 966; SHA-256 `7a33ef54860b5bc07c3509928c87110fe4618f2b01aca0f43a8ee02fe71fc42e`.
- `scalar/product11_degree882.json`: 110 live operations, exact degree 882; SHA-256 `971ffd27189126dd8a7138a6a7e387b34bcd64d4c1a8b1cf1b857b3b4095be6b`.

This review fully read the producer, its checker/helper, the complete new `scalar/PROOF.md`, and the authenticated Shared Binomial lowops parent's full ordinary proof. Its inherited centered/signed/interpolation interfaces were cross-checked against the retained proof scopes from rounds14–15. It does not reprove every transitive native calibration or claim a new Lean/Rocq rebuild.

## 1. The new mod-sixteen lemma is unconditional

The fixed coefficient tuple is essential. Both cone coefficients are divisible by sixteen, while q is even. Set C1=cone_A F and C2=cone_B C. Exact expansion gives

Budget+(qk)^2 = k^2[2q(C1+C2)-C1^2-C2^2]-4q^2 eta^2.

Every term on the right is divisible by sixteen: the cone terms already have a factor sixteen, and 4q^2 does because q is even. Thus Budget is the negative of an even square modulo sixteen. It belongs to {0,12}. Consequently D=Budget-4 belongs to {12,8}; these are neither zero nor square residues modulo sixteen. In particular D is never zero or a square and is always divisible by four.

This proves more than needed. X is divisible by eight and Y by eight, so ell=XY^2 is divisible by 512. Hence Dt=1+ell(ell+1)k^2 is 1 modulo sixteen, and D Dt itself is always 8 or12 modulo sixteen. Completeness only needs the weaker statement that D is positive nonsquare and the canonical Dt is a positive square.

The checker exhausts the 2,048 possible residues of even q, k and eta modulo sixteen. This is an exhaustive finite residue check of the reduced identity, not the basis for the universal expansion argument above.

## 2. Soundness remains valid for every signed assignment

The changes D=Budget-4 and Dg=1+D Dt s^2 affect no unconditional affine restriction or native numerator. The inherited coefficient/affine facts still give Delta>1, A even and nonzero, H odd and nonzero, and Dt>=1. The new congruence proves Dg=1 modulo four and P=Dt Dg=1 modulo four, hence both are nonzero even before positivity is known.

Df=1+Delta U^2 P, delta=Delta^2 U^2 P-1 and Cy=Q V^2-1 cannot vanish: Delta is an integer greater than one. This argument permits U=0 and negative P. The homogenized quintic Ac is nonzero because H is nonzero and its defining quintic has no rational root. Therefore S=0 cannot satisfy the final equation; s and r are nonzero. c is deliberately not assumed nonzero yet.

The unchanged saturation U=r c^2 A Dm gives the three required coprimalities:
- Df is1 modulo P, and Da=(Q-1)(QV^2-1) is1 modulo P.
- Modulo Df, Q=-Delta, V=-c and Da=A^2 Dm.
- Df is1 modulo both A and Dm, because A Dm divides U.

Multiplying the final equation by delta yields a rational square equal to the nonzero integer P Df Da. The square is an integer square. Pairwise coprimality makes the absolute values of all three factors squares. P=1 mod4 rules out its being the negative of an odd square. Once P>0, Df>0 follows directly and Da>0 follows from their product. This reasoning does not assume the sign that it is trying to recover.

The further coprime split gcd(Dt,Dg)=1 gives positive square roots tau and g. As s is nonzero, Budget<=3 would make D<=-1 and Dg<=1-Dt<=0, a contradiction. Therefore Budget>=4; the new residue lemma strengthens this to Budget>=12. Hence the centered native inequalities and strict strip remain available. They exclude c=0, so U and I can now safely be divided into the later arguments.

## 3. Strong/auxiliary restoration and the small-modulus variant

With p0=sqrt(P), define I=U p0 and T_old=p0 T. Both are integers, I is nonzero, c^2 divides I, and the strong norm and auxiliary affine expression become exactly the retained parent's expressions. The rational auxiliary ordinate sqrt(Da)/delta is integral by the adjacent-coefficient descent, after Q>1 has been established. In detail, a reduced denominator d has d^2 dividing Q-1; the usual inverse Pell step keeps V integral, preserves that denominator, and strictly reduces |V| until |V|=1. No arbitrary rational Pell solution is silently treated as integral.

Canceling nonzero delta then makes Z/S an integer; thus S divides Ac and H divides K^5. This is not used as the generally false implication H divides K. Instead the inherited signed rank theorem first restores the main Pell index and the strict exponential gap. That gap makes the fifth power of the relevant projector difference smaller than |H| and therefore zero.

For the degree-882 form, the changed first-index modulus is 4q^4. It exceeds 3R+1 under the same already-recovered packing bounds, and divides 2XY^2 by the literal affine formula. The signed first-index congruence excludes its negative branch once the inherited main index p=R and p>n1 are proved. The positive branch gives 2n1=R+1 exactly. Reducing the canonical recurrence modulo XY afterward restores the old h coordinate. Completeness chooses the new h by the corresponding quotient modulo 4q^4. The proof does not assume that XY and4q^4 are equal or divide one another.

All these statements depend on the unchanged source34 coefficient tuple. The checker independently compared its full decompressed bytes to the authenticated incoming payloads, then embedded those trusted hashes for a portable future replay. MF remains the already-shifted mask.

## 4. Completeness and quantifier order

The canonical outer source witness still has Budget>=64 and Dt=tau^2. Thus D=Budget-4 is positive and nonsquare, so D Dt is positive and nonsquare. Ordinary Pell existence gives a positive solution of g^2-D Dt s^2=1 directly. No extra factor four and no even-ordinate requirement is needed.

Fix guard data s,g and p0=tau g. Next choose one strong pair I,f with 4s A Dm p0 c^2 dividing I, then set r=I/(A Dm p0 c^2). Every prime of p0 s r divides the now-fixed I. Choose an intersective root a0 modulo sr and request T_old=p0 a0 modulo p0 s r from the supported-modulus interpolation theorem for that same fixed pair. It yields integral T=T_old/p0 and T=a0 modulo sr. Hence Ac/S is integral and n=Ac/S+p0 f y completes the final equation.

The dependency order is outer witness, guard, fixed strong pair, intersective residue, auxiliary pair, then n. No modulus is requested and then invalidated by changing I. The older source condition R=3 mod4 and its parity hypotheses are inherited from the outer canonical witness and are not weakened by changing the guard.

## 5. Independent exact graph and degree verification

`audit_product.py` is newly written and imports neither the producer, the producer's checker nor its sparse polynomial helper. It parses the literal graphs and uses its own sparse integer-polynomial arithmetic and AST interpreter. Each graph is verified against 36 separately entered mathematical register identities, with every one of109/110 live arithmetic gates covered. It checks topology, exact variable and coefficient leaves, domain, counts and the complete six-port binding.

A multiplicative weighted graded-lexicographic order, treating the six fixed coefficient ports as degree zero, propagates an exact leading monomial through every live node. Every possible leading cancellation is explicitly rejected. The final leading monomials contain only the port beta, so their coefficient cannot vanish at the authentic positive beta. Together with the independent syntactic upper bound this proves exact degree, not merely a lower bound along a sampled line:

- Native: j^588 w^112 v^154 h^42 s^16 r^12 c^40 T^2, coefficient 2^988 3^700 beta^588, total degree966.
- Short: j^588 w^70 v^112 h^42 s^16 r^12 c^40 T^2, coefficient 2^946 3^658 beta^588, total degree882.

These also match the whole leading form in the written proof. The changes multiply the old leading coefficient by the correct factor from removing the guard's factor12; degree remains unchanged.

Each graph undergoes nine actual arithmetic corruptions (D,P,U,Df,Q,b,S,Ac,output), plus domain and operation-count mutations. All22 corruptions across the pair are rejected by the full independent audit. Normal Python and optimized Python produce identical complete receipts. Separately, the inspected producer's read-only `--check` rebuild passes in both modes and reproduces the shipped bytes. No source numeral recipe, incoming verifier or proof-search program was executed by this audit.

## 6. Final limitations and attribution

The square-root saturation, coprime product, short first-index modulus and interpolation schedule are inherited from the authenticated Shared Binomial Certificates package. This round's substantive local improvement is the fixed-coefficient mod16 lemma allowing D=Budget-4 and omission of the forced factor4. It saves two charged operations in each product equation while preserving the exact degrees. These109/966 and110/882 equations are genuine cost/degree tradeoffs against round15's lower-degree norm frontier, not replacements for its minimum degree or a global operation optimum.

The finite receipts establish exact syntax, local algebra, true degree, coefficient identity, mutation rejection and deterministic regeneration. The unbounded source theorem and native/calculus/refutation interpretation remain the explicitly named inherited ordinary mathematics. No new proof of Con(ZFC) or absence of integer zeros follows from these computations.
