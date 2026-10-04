# Fixed polynomial absorption of the strong root on its full independent source boundary

Every fixed integer-polynomial replacement of f using **all91 existing f-independent values** of the complete84 source has finite ordinary-input projection. These are67 computed values and24 supplied values, with their actual dependencies retained. The additional arguments beyond the established88-value boundary are precisely the supplied auxiliary quotient T, the supplied auxiliary ordinate y, and its computed square y².

This extends the fixed-substitution obstruction, not the circuit bound. The authenticated complete84 polynomial is unchanged, no arbitrary G circuit is emitted, and no new operation minimum is claimed. All remaining original supplied witnesses are positive at a substituted zero. Signed values of G are handled by an exact source symmetry; the proof uses the accepted signed-T theorem without assuming positive restoration of T, R=3 modulo4, or full compiler soundness for arbitrary signed-T tuples.

## 1. The theorem and its effective cutoff

Fix a valid inherited compiler-numeral slice. Let G be any fixed integer polynomial in the91 formal source values identified in Section2, and substitute f=G literally. Formal coefficients are fixed while the ordinary input and witnesses vary. Combine like monomials before measuring coefficient 1-norm, and put

    d=max(1,deg G), L=max(1,||G||_1),
    K=(2d+2)! * 20^(2d) * (L+1)²,
    C_res=32d+4+ceil(log2(K+1)).

For G=0 use degree0; its zero sector will be excluded outright. For each sign s∈{−1,1}, define

    G_s(E,T,y,v)=sG(E,sT,y,v),

where E is the88-value f/T/y-independent boundary, and v denotes the existing computed y² port. Write

    G_s(E,0,y,y²)=sum_(j=0)^(2d) g_(j,s)(E)y^j.

All missing coefficients are zero. In the polynomial ring on the formal E ports define

    D_strong=1+Delta*i²*c⁴,
    N=Q*(c+R*D_strong)²−1,  D_den=Q−1,
    B(E)=D_den^d,
    A_s(E)=sum_(k=0)^d g_(2k,s)(E) N^k D_den^(d−k).

Here c,R,Delta,i,Q are their specified actual E ports. In particular Q means the existing R16 register, not a new independent witness, and D_strong is a displayed polynomial expression, not a new port. Put

    t_s=max(1,deg A_s,deg B),
    L_As=||A_s||_1, L_B=||B||_1,
    C_rat,s=12t_s+9+ceil(log2(L_As²+2L_B²+1)),
    C_G=max(C_res,C_rat,+,C_rat,−).

Assign degree0 if A_s=0. B is a nonzero formal polynomial, so L_B≥1. These are effectively computable integers depending only on the fixed G and fixed slice. A_−=−A_+ at T=0, so the two rational cutoffs in fact coincide; retaining their maximum is harmless.

**Theorem.** Every zero after this literal substitution, with all other original supplied witnesses positive, satisfies

    G(actual)!=0,  2*d_native*x+b_source < R < C_G.

Here d_native and b_source are the fixed positive compiler parameters, not the degree parameter d above. Thus the entire ordinary-positive-input projection is finite. The theorem covers dependent-port cancellations, negative G, and the sector where G evaluates to zero; it does not require G to be nonconstant or algebraically independent of the retained source equations.

## 2. Exact source boundary and inherited signed-domain facts

The parent is the literal complete84 array in `complete84_scaled_strong_output.json`, SHA-256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`. Its supplied interface has25 values. Its unchanged ledger is84=47M+37A, with every source row and supplied value live.

Use the source meanings

    X=wq, Y=sq³, a=Y(X+1), A0=a+2,
    Delta=A0²−1, c=R10a, R=r_lhs,
    T=auxiliary_quotient, y=y_aux,
    S=aux_coefficient_root=Delta*i*c², Q=R16=S²,
    V=aux_u_rhs=c(Tf−1)−Rf².

The actual auxiliary and scaled strong factors are

    Na=Q*(V²−y²)+y²,
    Ns=Delta*f²−Q.

The full output is `P5*Na*Ns−Delta`, where P5 is the product of the unchanged first, main, input, index and transport factors. All symbols above are actual source definitions or explicit polynomial abbreviations.

Fresh dependency propagation through every row gives the all91 boundary:67 computed registers and24 supplied ports independent of f. The established E88 boundary is66 computed registers plus22 supplied ports independent of f,T,y. Their exact difference is `aux_y2=y_aux*y_aux`, `auxiliary_quotient`, and `y_aux`. All E88 values belong to the93 T/y-independent values bounded in the signed-T theorem. The receipt gives the complete lists and all free dependencies.

The accepted [signed-quotient theorem](complete84_signed_quotient_absorption.md), applied to the same source on a valid slice with f,i,y and all exterior supplied values positive but T any integer, proves directly:

    all seven normalized factors are1,
    c=psi_R(A0), D_main=chi_R(A0),
    f=chi_m(A0), psi_m(A0)=i*c², R*c divides m,
    u=2*d_native*x+b_source<R<c,
    Delta>1, Delta<c, c>=2, f>=2,
    |e_j|<c⁴ for the old85 auxiliary-independent values,
    |E_j|<=f³ for all E88 values,
    |T|>f^(R−4).

Its rank proof and exterior bounds do not use positive-T parent restoration or the historical R mod4 conclusion. The [multiplier-dependent root theorem](complete84_multiplier_dependent_root_absorption.md) additionally derives, from these same premises,

    i>c^(c−1).

For clarity, the latter bound holds for every strong completion: m≥R*c and Pell composition give psi_m(A0)≥c*psi_c(D_main). The first positive odd term in the binomial expansion gives psi_c(D_main)≥c*D_main^(c−1), while the main norm and Delta>1 give D_main>c. Divide by c². This is an estimate in the proof, not uncharged source exponentiation.

These are the only native-dynamics facts used below. In particular we do not assume X=2^R, a canonical auxiliary completion, or accepted-computation soundness on signed-T tuples.

## 3. Sign restoration, including the actual y² argument

The only direct f consumers are `L16=f*f` and `auxiliary_Tf=T*f`; T has no other direct consumer. Therefore simultaneous sign reversal gives the exact all-ring identity

    F84(...,f,T,...)=F84(...,−f,−T,...).

At a substituted zero with g=G(E,T,y,y²)≠0, put s=sign(g), f'=|g| and T'=sT. Then

    f'=sG(E,sT',y,y²)=G_s(E,T',y,y²).

The88 E ports, y, and computed y² are unchanged; the supplied T port changes sign and is explicitly accounted for inside G_s. Replacing the formal y² argument by the actual square is essential and is not a free independent witness. Formal degree and coefficient norm of G_s equal those of G. The new tuple lies in exactly the signed-domain theorem above.

If g=0, there is no need for a sign map or decoding. The actual rows at f=0 give V=−c and

    F84|f=0 = −Delta * (
      Delta*i²*c⁴*P5*(Delta²*i²*c⁴*(c²−y²)+y²)+1).

The retained positive supplied ports give a>0 and the integer Delta≥8 before any norm equation. The parentheses are1 modulo Delta and cannot vanish. This excludes identically zero G and values where a nonzero formal G cancels on its dependent source arguments. T disappears from this identity.

Henceforth rename f',T' as f,T. The signed-domain facts apply, and the restored tuple satisfies f=G_s(E,T,y,y²) with f>0.

## 4. The actual auxiliary conic and its irreducibility

Fix the actual integer values E,f of a putative restored zero and put b=c+Rf². Since Na=1, its two remaining formal coordinates T,y obey

    C(T,y)=Q*(cfT−b)²−(Q−1)y²−1=0.

Here Q=S²>1 and cf≠0. The affine change X=sqrt(Q)(cfT−b), Y=sqrt(Q−1)y, over the complex numbers, turns this into X²−Y²−1. Its homogenization X²−Y²−Z² has rank3, whereas a product of two homogeneous linear forms has rank at most2. Thus C is absolutely irreducible.

Equivalently, the determinant of the actual homogeneous coefficient matrix is

    Q*(Q−1)*c²*f² != 0.

In particular C is irreducible in Q[T,y] and in Q(T)[y]; its y-leading coefficient is the nonzero constant −(Q−1). No claim is being made about a generic resultant before specialization.

Define the specialized integer polynomial

    H(T,y)=G_s(E,T,y,y²)−f.

Its y-degree is at most2d. Its coefficient 1-norm, jointly in T,y, is at most `(L+1)f^(3d)`: substituting E values contributes at most f^(3d) to each original coefficient, substituting y² for the final port changes only exponents, and the extra constant f has size≤f^(3d). This remains valid under any coefficient cancellation or degree drop.

## 5. Nonzero specialized resultant bounds T

Let P(T)=Res_y(C,H), computed after specializing E,f to their actual values. If H=0, use P=0 and go to Section6. Otherwise let m be its actual y-degree, m≤2d.

The E88 bound gives Q,c,R≤f³. Hence cf≤f⁴ and b≤2f⁵. The coefficient norms of C's T², T, constant, and y² terms are respectively bounded by f¹¹,4f¹²,5f¹³,f³; consequently `||C||_1≤20f¹³`.

For m≥1 the Sylvester determinant has m rows from C and two rows from H. The coefficient 1-norm of a polynomial product is at most the product of the norms, and the determinant has at most (m+2)! terms. Thus

    ||P||_1 <= (m+2)! (20f¹³)^m ((L+1)f^(3d))²
             <= K f^(32d).

For m=0, P=H(T)², so the same bound holds. Common finite roots make the resultant vanish at the actual T, even if an additional leading coefficient specializes to zero there.

If P is not the zero polynomial, Cauchy's root bound for an integer polynomial, whose nonzero leading coefficient has absolute value≥1, gives

    |T|<=1+||P||_1<=(K+1)f^(32d).

One elementary proof is to compare the leading term at modulus r with the sum of lower terms: r>1+max|a_j/a_n| makes the lower geometric sum strictly smaller. A nonzero constant P has no root and contributes no solutions.

Combining the upper bound with `|T|>f^(R−4)` and f≥2 gives

    u<R<C_res.

Indeed R≥C_res would imply f^(R−4)≥(K+1)f^(32d), contrary to the strict lower bound. This branch never assumes that a nonzero generic resultant stays nonzero at all specialized source values.

## 6. Identically zero resultant yields a rational E88 expression

If P=0 in Q[T], irreducibility of C in Q(T)[y] makes C a divisor of H there. Since C is primitive in Q[T][y] with constant nonzero y-leading coefficient, Gauss's lemma gives divisibility in Q[T,y]. It also holds when H=0.

Specializing that polynomial divisibility at T=0 gives divisibility by

    C(0,y)=Q*b²−1−(Q−1)y².

This is polynomial specialization, not a claim that T=0 is a positive source zero or that this conic fiber has a rational point. The strong unit gives f²=D_strong, so its two coefficients are exactly the values of N and D_den defined in Section1, with D_den(actual)>0.

Divide `G_s(E,0,y,y²)−f` by the monic quadratic `y²−N/D_den`. The remainder has degree at most1. Divisibility forces its odd coefficient to vanish and its even coefficient to equal f before the subtraction. For y^(2k), the remainder is `(N/D_den)^k`; for y^(2k+1) it is that value times y. Since k≤d, multiplying the even remainder by D_den^d proves

    B(actual)*f=A_s(actual),  B(actual)>0,

for the fixed integer polynomials in Section1. All polynomials are constructed before specializing E. Algebraic dependencies or cancellations among E ports do not affect this evaluation identity. The denominator clearing follows, for example, from the geometric-sum identity

    (D_den*y²)^k−N^k
      =(D_den*y²−N) sum_(r=0)^(k−1)(D_den*y²)^(k−1−r) N^r.

The even/odd remainder argument therefore covers every degenerate H case and avoids assuming a generic nonzero specialization.

## 7. Rational E88 absorption has a uniform finite bound

For the particular putative zero, freeze the old85 integer exterior values. Substitute

    (i,S,Q)=(z,Delta*c²*z,Delta²*c⁴*z²)

in the fixed polynomials A_s,B to obtain integer polynomials a(z),b(z). These auxiliary polynomials are proof objects; varying z does not assert that the frozen exterior values continue to satisfy all source equations.

The coefficient weights are the same as in the accepted88 theorem: old85 values have absolute value<c⁴; S has coefficient Delta*c²<c³; Q has coefficient Delta²*c⁴<c⁶; i has coefficient1. Thus, with t=t_s,

    ||a||_1<=L_As*c^(6t),  ||b||_1<=L_B*c^(6t).

The specialized b is nonzero, since its value at the actual i is B(actual)>0. The strong equation now gives an integer root i of

    J(z)=a(z)²−(1+Delta*c⁴*z²)b(z)².

J is not the zero polynomial: the quadratic `1+Delta*c⁴*z²` has two distinct complex roots, hence is not a square in Q(z), whose squares have even zero/pole orders. If J=0 with b≠0 it would equal `(a/b)²`, a contradiction. This includes a=0 and every specialization that lowers the degree of a or b.

Using Delta<c⁴, a deliberate weakening of the available Delta<c, gives

    ||J||_1 <= (L_As²+2L_B²)c^(12t+8),
    i <= (L_As²+2L_B²+1)c^(12t+8).

Apply `i>c^(c−1)`. At or above C_rat,s, division by c^(12t+8), followed by c≥2, contradicts the two bounds. Therefore

    u<R<c<C_rat,s.

The source sign restoration gives at most two choices s. Combining this branch with Section5 proves the theorem's strict cutoff C_G and finite whole ordinary-input projection. Rational functions are used only to analyze this proof branch; the permitted substitution in the theorem remains a fixed integer polynomial G in the exact91 existing source values.

## 8. Fresh source evidence, scope and replay

The new standalone helper authenticates thirteen installed predecessor files as inert bytes: the actual84 trio, signed-quotient trio, strong-root trio, multiplier-dependent trio and its mathematical review. The root scout and its prior independent challenge are recorded separately as authoring provenance; they are not runtime or theorem dependencies. No supplied helper is imported or executed.

The receipt retains all84 actual instructions, all25 supplied names and the output identifier. A fresh graph walk verifies topology, complete liveness, the64+21,66+22 and67+24 boundary counts, the exact three newly admitted values, and containment of E88 in the signed theorem's bounded93 interface. It expands the complete output above eight actually computed auxiliary-independent cuts to verify the factor identity, simultaneous f/T sign identity and zero-f contraction. The actual V,Q,strong and auxiliary-conic producers are independently checked against their displayed formulas. This verifies source binding, not a circuit for arbitrary G.

Additional formal checks expand the projective conic determinant and radicand discriminant; verify cleared even/odd remainders over Z[N,D_den,y]; check the sign covariance with the actual y² substitution on a declared finite monomial basis; and record the squarefree quadratic underlying the rational-function nonsquare proof. A small division-free Sylvester determinant implementation checks bounded resultants, including zero H, constant-in-y H, a conic multiple, a linear-y formula and a further degree-drop case. Conservative coefficient bounds and cutoff endpoints are corroborated on explicit finite parameter lists.

These finite checks are evidence for the displayed identities and estimates. They do not establish the all-G theorem by sampling, realize native full zeros, test accepting computations, or supply a generic G/resultant compiler. The quantified proof is Sections3–7 relative to the pinned signed-domain facts in Section2. The original universal84 bound remains unchanged.

The helper uses only the standard library. JSON reading rejects duplicate keys, floats and nonfinite constants. Checks remain active under optimized Python; exact replay compares canonical JSON so Boolean and integer types differ. The receipt binds the helper's exact bytes. `--output` creates a new file exclusively; `--expect` only verifies an exact regenerated receipt.

Use absolute paths, for example:

```sh
python3 /absolute/path/complete84_full_independent_root_absorption.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/complete84_full_independent_root_absorption.json
python3 -O /absolute/path/complete84_full_independent_root_absorption.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/complete84_full_independent_root_absorption.json
```

Exact census, evidence counts, dependency pins and final replay status follow below.

### Exact91 interface

The67 computed names, in actual source order, are:

```text
tau_square repunit q Lbig n2 wn2 sn2
UM R10b ksn2 first_root_base first_next first_product norm_first
R10a R12 cam2 D1 gamma_sum a4 a4m5
gam R14 L15 a_square A c2 Ac2
norm_main norm_pair q_minus_F q_minus_FZ C_after_alpha scaled_t marked_rhs
W odd_index index_product index_rhs difference_multiple exponent_partial modulus_multiple
exponent_rhs mu2 kappa2 scaled_kappa2 norm_input norm_triple aux_y2
hpm1 index_difference gap_product gap Lm1 rproduct qMF
mask_factor mask r_lhs norm_index kinner innerC transport_partial
local_rhs norm_transport aux_coefficient_root R16
```

The24 supplied names, in actual interface order, are:

```text
Jrep F alpha transport_quotient h i auxiliary_quotient
s w tau_root eta zeta y_aux Z
delta rho sigma x Bm1 Kconstant twice_cell_bits
inner_bits MC MF
```

These include the ordinary positive input and fixed-numeral ports; they are not24 freely chosen auxiliary witnesses. Every listed computed value retains its actual source dependencies.

### Evidence totals and pins

The complete output expansion above the authenticated eight cuts has17 terms; the zero-f contraction has4 terms; the actual conic after substituting Q=(Delta*i*c²)² has9 terms. The fresh evidence includes48 denominator-clearing identities,140 signed-monomial cases with actual y² substitution,18 exact bounded resultant cases,9 coefficient-norm cases and32 cutoff records. None is presented as a native full zero. The original parent packet is checked for immutability across the source analysis.

All thirteen runtime dependency paths below are relative to the supplied `--root`:

| Dependency | SHA-256 |
|---|---|
| `complete84_multiplier_dependent_root_absorption.json` | `720c602d9d82d456fd50fb9b5c4f66132e6b4ca1222c9832694ddf0d9b92a46b` |
| `complete84_multiplier_dependent_root_absorption.md` | `045a1147a09d3d70550c9f5c6dcf398d8c9686dbfa957f00d263fb868a485d75` |
| `complete84_multiplier_dependent_root_absorption.py` | `4fbb8595e4956f43829f91e42a57836bc726c3261bc5f9abf0b473d2493e80c4` |
| `complete84_scaled_strong_output.json` | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| `complete84_scaled_strong_output.md` | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
| `complete84_scaled_strong_output.py` | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| `complete84_signed_quotient_absorption.json` | `c9522c55adb3e602c2d355cb98d4e313c5e258a66e93bf0bbca52d56fddd9a00` |
| `complete84_signed_quotient_absorption.md` | `79800010986c07674fb681a93e02f624ee7bc6e5d39b99a1e77daf5021fa77c9` |
| `complete84_signed_quotient_absorption.py` | `cc5ed27ffcffefbd76b85ea36efa05637e06a0eb7fa221c6d9e31af9ea4f9d5f` |
| `complete84_strong_root_absorption.json` | `424ba5aaa6e1ebc8525e4eaaaca7f7489282c7533d775dac86d10a659684986a` |
| `complete84_strong_root_absorption.md` | `b73fb50aebb8de23a282aff91c389d74b4bd96dadd355c43eb7e7783c1b6abc2` |
| `complete84_strong_root_absorption.py` | `3d17fb1bdf7e3942bedcc873ee87a244ef66aa1188eaafb732828965ebfc670c` |
| `review_complete84_multiplier_dependent_root_absorption.md` | `743d51a45fbd5d3fe99d182eaf5f22d0d916430ffcd0c75b87c7d4442452d34e` |

Authoring provenance only, not replay dependencies:

- `complete84_full_f_independent_root_scout.md`: `e1169534645f9f1455cc7d68b03e0e73c0ee63b8581d7010643f59a080e9cd24`.
- `review_complete84_full_f_independent_root_scout.md`: `1c64f6249c28e27472f0f2d8b4bfab808a6b918d5056ab560834c2040cfdd9e4`.

Fresh helper SHA-256: `02698613d648ab7db6a707471aed6346540725aa64bfe426f7b5d3dd36d16776`.

Fresh receipt SHA-256: `4b0eac23c21a9cf7cf177cd19fface8cccff2a1a8dc0cbc70d6af16fca115320`.

The fresh writer and exact normal/`python -O` replays all passed. Both replay processes ran from `/` with absolute helper/root/receipt paths. Final files are frozen pending independent review; no repository or predecessor was changed.
