# Independent audit: full symbolic first-index-deletion counterfamily

## Verdict and exact conclusion

**PASS.** I independently checked `FULL_COUNTERFAMILY.md` against the retained 81/82 source interfaces and found the construction valid. For every unchanged genuine compiler numeral tuple in its stated domain and every positive ordinary input `x`, it defines all 17 supplied coordinates as strictly positive integers and makes each of the six retained factors exactly +1. Its forced first-index inverse is positive rational but nonintegral, with exact remainder `25u−1`.

This is a symbolic existence proof, not a numerically materialized full tuple. No upstream program or saved source schedule was executed. It contradicts positive zero-set restoration and, for an empty-set compiler, ordinary-input soundness of the deleted candidates. It does not improve the operation bound. The earlier reduction audit remains valid; the new family realizes that reduction's previously unresolved nonzero-defect branch.

The checked draft SHA256 is recorded in `counterfamily_checks.json`. The newly authored checks are in `check_counterfamily.py`; they are supplementary to the proof below, never a substitute for it.

## 1. Actual fixed numerals: no replacement by toy masks

The construction fixes `B=2^d`, `K`, `ell=2d`, `b`, `MC`, and the shifted source `MF=MF0+B−1` before choosing any witnesses. It changes none of them. The inequalities and residues used are genuine necessary properties of the inherited compiler recipe, not an assertion that arbitrary masks are complete compiler instances.

In particular, the input argument really needs `b` odd. I verified this directly by read-only GitHub connector reads at the exact pinned commit `3f4a974a5ddf12c46302fc5d2edafc3730277923`:

- `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md`, lines 35–62, chooses `b,L` as powers of 5 and `d=bL`. Returned blob SHA: `d0712f0258a5fc0959980803d5b5a8a02b5889cb`
- `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md`, lines 35–62, explicitly retains `b,L,d` as powers of 5. Returned blob SHA: `90aa8895f38e2f9cb3a13c7ecff9f3f2a8d1fbf3`

The already reviewed actual mask contract supplies `MC≡2 mod4`, `MF0≡4 mod8`, and `0<MC,MF0<B−1`. There is no use of the incorrect inequality `MF<B−1` for the shifted port.

## 2. Factorial arithmetic and CRT

Choose the draft's `L≥max(1100d,16,K,W,ell*x)` and `t=L!`. Then `1100d|t`, `t≥64`, and `t=2^a m` has `a≥4`, `m` odd. `N=t/d` is an integer multiple of 1100, so `q=2^t=B^N` and `J=(q−1)/(B−1)` are positive integers.

For every odd prime power `r^v` exactly dividing `t`, both `r^(v−1)` and `r−1` divide `t`. They are coprime, so their product `phi(r^v)` divides `t`. Euler's theorem is applicable because `r` is odd. Therefore `q≡1 mod r^v` for every such factor, and `q≡1 mod m`. No assertion about `phi(t)|t` is made or needed.

The four integers `e0+jm`, `0≤j<4`, cover all residues modulo 4, since `m` is odd. Exactly one is 3 modulo 4. Thus `3≤e<4m≤t/4` and `e≡M mod m`, where `M=(MC+q MF)J` is the literal shifted mask contribution.

Since `q≡0 mod4` and `J≡1 mod4`, we have `M≡2 mod4`. The selected positive residue `Z≡e−M mod2^a` is consequently 1 modulo 4 and satisfies `1≤Z≤2^a≤t`.

For the literal packed expression

`R=(q²−Z−qF)(q²−1)+M`,

reduction modulo `m` gives `R≡M≡e`; reduction modulo `2^a` gives `R≡Z+M≡e`. Thus `R≡e mod t` by CRT. The latter computation correctly uses `q≡0 mod2^a`, justified by `t≥a`.

The factor 1100 is also correct: `2^20≡1 mod55`, hence `B^20≡1 mod55`. Grouping `J=Σ_{j=0}^{N−1}B^j` into blocks of 20 gives a number of identical-residue blocks divisible by 55. Therefore `55|J`, regardless of whether `B−1` is invertible modulo 55. This is not division of the congruence `q−1≡0 mod55`. Both `M` and `q²−1` are divisible by 55, so `55|R`.

Finally `R≡e≡3 mod4`, so `u=R/55` satisfies `u≡1 mod4`.

## 3. Outer positivity and scale margins

The fixed choices give `K,W,ell*x≤t`, while `Z≤t` and `e<t/4`. Hence `C=W+Z≤2t` and

`F=(K+2^e)C≤2t(t+2^(t/4))`.

The draft's elementary inequality

`2t²+2t·2^(t/4)+4t<2^t`

holds for every integer `t≥64`. Its proof via `t≤2^(t/8)` is sufficient: the polynomial and exponential summands are separately bounded by `2^(t/2)`, and `2^(t/2+1)<2^t`.

Consequently `alpha=q−F−2Z−W−ell*x>0`, and substitution into the actual source gives `marked_rhs=C`, `W=C−Z`, exactly. It follows that `F+Z<q` and hence the previously independently checked genuine shifted-mask estimates give

`(2q−1)(q²−1)<R<q⁴−q³`.

These bounds imply `p=R>5t+5`, in particular `p>t`. Thus `w=2^(p−t)` is a positive integer. Since `33u−1=3p/5−1>3t`, `s=2^(33u−1−3t)` is also a positive integer. Therefore the actual asymmetric source scales, `X=wq`, `Y=sq³`, hold with no substitution of the old symmetric scaling.

## 4. Exact first/main ratio family

For `p=55u`, `n=40u`, `X=2^p`, and `Y=2^(33u−1)`, let `L0=2XY=2^(88u)` and `M0=4XY²=2^(121u)`. Then

`L0^(p−1)/(2M0^(n−1))=2^(33u−1)=Y`

exactly. This is an identity of integers/rational powers with integral exponents, not asymptotics.

The lower Pell estimates and `p>n` make `c/k>Y`. For the upper estimate, `epsilon=1/X+2/(XY)<2/X` and `(p−1)epsilon<1/2`. The geometric-series bound on the binomial expression gives

`0<c/k−Y<4pY/X=110u·2^(−22u)<1`.

The final inequality holds at `u=1` and strictly improves thereafter. Thus both supplied ratio gaps `eta=c−kY` and `zeta=k−eta` are strictly positive integers. Their literal definitions recover `k` and `c` exactly.

The first and main norms are +1 by the independent Pell constructions. Their indices are not assumed to satisfy the deleted first-index equation; indeed they deliberately do not.

I also checked `SCALED_FAMILY.md`: its wider `r(2r+1)` family, dyadic balance, ratio bound, and scalar-range specialization are valid. That earlier subsystem result is distinct from the present full literal packed construction.

## 5. Shared input quotient and rho/sigma positivity

The genuine odd `b` makes `I=ell*x+b` odd. The standard discriminant expansion gives `psi_A(I)≡I A^(I−1)≡I mod Delta`. Since `I≥3`, `delta=(psi_A(I)−I)/Delta` is a positive integer.

Here is an independent short proof of all projection and split positivity, avoiding any need to compare unrelated enormous estimates. With `a0=A−2`, define

`g_j=(chi_A(j)−a0 psi_A(j)−2^j)/H`, `H=4A−5`.

The projection recurrence proves integrality. More explicitly,

`g_0=g_1=0`, `g_2=1`,
`g_(j+2)=2A g_(j+1)−g_j+2^j`.

It follows inductively that `g_j` is strictly increasing for `j≥1`. Because `I≥3` and `I<t<p`, the exact construction has

`rho=g_I>0`, `gamma=g_p>rho`, `sigma=g_p−g_I>0`.

This also proves the shared-coordinate identities

`D=X+a0c+(rho+sigma)H`,
`mu=W+a0 kappa+rho H`,
`kappa=I+delta Delta`.

Thus the actual input norm, not a replacement independent input factor, is +1 with the same `rho` used in the main root. The draft's direct growth proof gives the same result. In its last comparison, `z_(p−1)>2^(p−1)` follows immediately from `z_1=2` and `z_(j+1)>(2A−1)z_j≥3z_j`.

## 6. The literal transport quotient

Since `p≡e mod t` and `q=2^t`, the positive integer `w=2^(p−t)` satisfies `w≡2^e mod(q−1)`. Moreover `p−t>e`, so `w>2^e`. Hence

`transport_quotient=1+C(w−2^e)/(q−1)`

is a positive integer. Substitution using `F=(K+2^e)C` yields exactly

`(K+w)C+q−F−transport_quotient(q−1)=1`.

This is the actual sheared source with coefficient `K+w`; it is not an older `K+X` transport equation.

## 7. Both strong forms and the supplied auxiliary quotient

At `p=R≡3 mod4`, choose `m_aux=2cp`. The binomial expansion at the main Pell unit proves `c²|psi_A(m_aux)`, so normalized `iN` is integral. With `f=chi_A(m_aux)` and `S=Delta psi_A(m_aux)`, one has `S²=Delta(f²−1)`.

The odd auxiliary index `p` gives the integral quotient `V=chi_S(p)/S`. The two polynomial reductions, retaining their signs, give `V≡−c mod f` and `V≡−p mod c`. Consequently `o=(V+c)/f` and `j=(V+p)/c` are integers. They are positive by `V>c>p`.

Since `f²≡1 mod c` and `of+p=c(j+1)`, multiplication by `f` modulo `c` gives `c|(o+pf)`. Thus the actual supplied `T=(o+pf)/c` is positive integral and satisfies

`c(Tf−1)−Rf²=of−c=V`.

For normalized81, `i=iN` gives its exact normalized strong factor and coefficient `S²`. For ordinary82, `i=Delta iN` gives its exact ordinary strong factor and the same auxiliary coefficient `S²`. Both retain the same positive `f,T,y_aux`. No extra `o` or `j` witness is added; they are intermediates in the proof of the supplied `T`.

Therefore the auxiliary factor is +1 in both actual source modes. This construction does not invoke existence of a complete parent zero or require a missing `h`.

## 8. Nonintegral inverse and global implication

The 17 supplied coordinates listed in the draft agree with the inertly verified scout witness order. Every retained literal factor is +1. Thus their product minus 1 vanishes for each prescribed positive `x`, with all original fixed ports unchanged.

Since `P≡1 mod E`, `k≡2n mod E`. Here `2n−R=25u`, so the least nonnegative remainder is

`(k−R−1) mod E=25u−1>0`,

because `E=2^(88u−1)>25u`. Also `k>R+1`. Hence no integer `h` can restore this retained tuple. In particular this establishes more than non-bijectivity on a scaled subsystem.

The construction for every genuine compiler and every input implies a failure of universal ordinary-input soundness by choosing a compiler for the empty computably enumerable set. It does not challenge the normalized85/ordinary86 parent results, whose first-index equation excludes these constructed tuples.

## Supplementary checks and evidence boundary

Fresh normal and optimized runs of newly authored code passed:

- 162 factorial prime-power/totient checks
- 186 modular CRT/shifted-mask cases (toy necessary-residue constants only; no claim of complete compiler instances)
- 497 exact outer-margin checks
- three exact first/main/input subsystem examples with `u=1,5,9`, each checking three shared input splits
- three exact positive auxiliary/main/strong subsystem tuples, checking both source modes and the same supplied `T`

All source schedules remained inert. No full astronomical tuple was materialized. The proof above, not those bounded checks or their toy constants, establishes the full-source symbolic counterfamily.
