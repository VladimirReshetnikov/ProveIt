# Mathematical cross-read: the outer-slack 83 all-input collapse

Status: final mathematical PASS on the authenticated frozen author trio. Full companion-note cross-read found no remaining issue. The final clarification distinguishes four retained unit norms from the scaled strong factor Delta. This review concerns the new supplied coordinate `alpha_sum`, with `alpha_old=alpha_sum-Z`. It does not concern the separate free-coefficient 83 proposal. No repository file or author artifact was edited, and no archived or predecessor helper was executed.

## Scope and actual source

Final author pins:

| File | SHA-256 |
| --- | --- |
| complete83_outer_slack_collapse.py | `8e3c335f157e9a237791eeaceffec94415ba9ce8c2638d89d023213cfcbd0fd5` |
| complete83_outer_slack_collapse.json | `9b0b05ad969eec99ca761898149ec3798a803fbb591a7bf462bf82a15090c207` |
| complete83_outer_slack_collapse.md | `6623a525ab1b0376b1d6a452f8e5618f8e1f64f0a255fdcbcc97611dd3598259` |


The source read is the [author helper](complete83_outer_slack_collapse.py) and its [saved complete packet](complete83_outer_slack_collapse.json). The selected parent is the normalized 84 source, whose JSON SHA-256 is `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`. The child retains the normalized strong coefficient and Bezout auxiliary quotient. Its complete output is the product of seven factors minus the positive discriminant Delta. The proposed family has factors, in actual source order,

```
first, main, input, auxiliary, index, transport, scaled strong
  1,     1,     1,       1,      -1,      -1,       Delta.
```

Their product is Delta, so they give a full polynomial zero. There is no erroneous inference that every factor must be a unit merely because the final product is Delta. The all-value source identity is the signed coordinate substitution into the immediate 84 parent; positivity of the old alpha is precisely what is lost.

The following pinned proof notes were read as data:

| Note | SHA-256 |
| --- | --- |
| complete75_weakened86_all_input_collapse.md | `46f3e0f25fc4efeb3f8129b77c3df988283c7a818ee2af330e8e8f460dc8d017` |
| complete75_weakened86_auxiliary_sign_lift.md | `491ac3c3755efed1c6c89f7e07a752c25fb040859cac8c07d7db25e803c62c53` |
| complete75_weakened86_infinite_outer_family.md | `74b6c968500c5177440096bd3da3c9c07f9208f10aea79cad73554e9814bf1a2` |
| complete75_half_binomial_compiler.md | `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117` |

These inherited results provide the prime progression, Pell periods, and exact conjugate-error estimates. Their old final sign assignments are not imported unchanged.

## 1. Compiler and outer hypotheses

The actual modified compiler has d and b powers of five and an even native MC. Hence d is odd and coprime to three, and b is odd. Choosing a sufficiently large power-of-five N gives `q=2^(dN)>=16`, `q>2dx+2`, and `M=q^2-1=3m` with `3` not dividing m. In discussing the masks, the native mask must be distinguished from the literal source coefficient `MF_source=MF_native+B-1`.

Set `F=2`, `alpha_sum=q-2-2dx`, and transport quotient one. These are positive; the computed C is zero, and the actual sheared transport factor is -1 regardless of the positive program numeral Kconstant. Writing

```
K = q(q-2)M + (MC+q*MF_source)J,
R = K-MZ,
```

agrees with the child's actual packing. K is even. No mask typing or decoded history is being assumed. The negative computed input root and negative R used below are not supplied coordinates.

## 2. The changed wrap and rho congruences

For every odd M>=3 and even K, there are independent signs omega,t,sigma_sign and an even j satisfying

```
0<j<2M,
j = omega+t*(M*sigma_sign-K) modulo 3M.
```

Here j is a construction coefficient, not a supplied coordinate. To verify existence, put `r=M-K+1`. The available sign choices include `r,r-2M,-r,-r+2M` modulo 6M. Unless r is a multiple of 2M, one representative lies in `(0,2M)`. If it is a multiple, flip the omega choice and use the same four-element orbit starting at `r-2`, which is not a multiple of 2M. All representatives are even. Thus `2<=j<=2M-2`. This pays the fixed index sign -1 without reusing the old proof's adjustable epsilon.

Choose e in the inherited compatible classes `e=t mod 18M`, `e=t mod dN`, `e=3 mod 4`, with `e>=3dN`. Then `X=2^e` is divisible by q cubed, and hence by the child's required q; `w=X/q` is a positive integer. The prime-progression construction supplies `Y=q^3*s`, `A=Y(X+1)+2`, and `H=4A-5=3*ell` with prime `ell=2 mod 3`, `ell>3M`, and `A=-1 mod M`.

The inherited proof's coprimality still holds: `gcd(X+1,M)=3` and `v3(X+1)=1`; after fixing s modulo m and ell modulo three, the prime progression has coprime first term and difference. Dirichlet's theorem is an explicit existence dependency, not a conclusion of the diagnostic prime fixture.

Put `L=12M(ell-1)`. The Pell state returns modulo MH, powers of two return modulo H, `4|L`, and `gcd(L,MH)=3M`. The last equality follows from `gcd(4(ell-1),3ell)=1`. For p=e+Lz, `c=psi_A(p)` is fixed modulo MH and initially `c=t mod 3M`.

The input index is v=u for sign -1 and v=A*u for sign +1, where `u=2dx+b` is odd and at least three. Thus `kappa=psi_A(v)=u mod Delta`, `delta=(kappa-u)/Delta>0`, and `Fv=chi_A(v)+(A-2)kappa` has the prescribed sign modulo three.

The new numerator is exactly

```
N_rho = K-omega*p+j*c-M*Fv.
```

The wrap congruence makes it divisible by 3M at p=e. Changing z changes it by `-omega*L` modulo MH, so the gcd identity solves `N_rho=0 mod MH`. This gives an arithmetic progression with positive integral rho eventually. The resulting definitions

```
rho = N_rho/(MH), Z=rho*H+Fv, R=omega*p-j*c
```

contain no old `2*epsilon` displacement. That distinction is necessary for the new Bezout source.

## 3. First index, strict ratios, and positive supplied coordinates

Refining the progression by a Pell return modulo E=XY and by E freezes both p and c modulo E. Its residue satisfies

```
2n = R-1 modulo E.
```

The right side is even because p is odd, c is odd, and j is even. Thus a class modulo E/2 exists. With `k=2psi_P(n)` and `P=2XY^2+1=1 mod E`, the exact quotient `h=(k-R+1)/E` is integral and makes the actual index factor -1. Since R is eventually negative, h is positive.

The irrational-rotation argument survives this refinement. A is even, so `A^2-1` is odd, whereas `v2(P^2-1)=e+2v2(Y)+2` is odd. The two quadratic fields differ; hence the logarithmic ratio of their displayed positive Pell units is irrational. The integer progression step therefore still visits the required nonempty ratio interval modulo E/2 infinitely often. The inherited exact conjugate-error estimate gives `kY<c<k(Y+1)`, so eta and zeta are positive integers. The supplied first root is `chi_P(n)>0`; it is not the historical first-root gap coordinate.

For a sufficiently large tail, take `c>p+M*Fv+K+M*X+2`. Since `2<=j<=2M-2`, this makes rho positive and R negative. Also

```
M*gamma*H = M*(2c-psi_A(p-1)-X) > (2M-1)c-MX > N_rho,
```

using A>M and `psi_A(p-1)<c/(2A-1)`. Thus the supplied sigma=gamma-rho is positive. The actual main root is chi_A(p), and the actual input root is `-chi_A(v)` because C=0 and Z=rho*H+Fv. Its square gives the required positive input norm; no parent theorem requiring a positive input root has been invoked. In fact `R=K-MZ<0` already gives `Z>K/M>q(q-2)>q>alpha_sum`, proving negative restored parent slack directly.

## 4. Retained normalized strong and Bezout auxiliary block

For each selected p=3 modulo four, c is odd. Choose `m_aux=p*c`, `f=chi_A(m_aux)`, `t_strong=psi_A(m_aux)`, `i=t_strong/c^2`, and `S=Delta*t_strong`. The Pell binomial expansion proves `c^2|t_strong`; hence i is a positive integer, the normalized strong norm is one, and the actual scaled strong factor is Delta.

Start the auxiliary index at p for omega=+1 or at `p+2*m_aux` for omega=-1. The inherited odd-index quotient identities give

```
V = chi_S(index)/S, y=psi_S(index),
V=-c mod f, V=-omega*p=-R mod c.
```

Increasing the index by any nonnegative multiple of `4*m_aux` preserves these congruences and makes V unbounded. Choose it so `V>|R|f^2+c`. Since the strong norm gives `f^2=1 mod c`, the numerator

```
V+c+R*f^2
```

vanishes separately modulo f and c. Also `gcd(c,f)=1`, so it is divisible by their product. Therefore the actual supplied Bezout quotient

```
T=(V+c+R*f^2)/(c*f)
```

is a positive integer, and the literal child formula `c*(Tf-1)-R*f^2` recovers V. The auxiliary norm is exactly one. Enlarging this auxiliary index changes none of the first/main/input/index/transport coordinates. This proves the full positive extension, rather than only a residue compatibility statement.

## 5. Conclusion and finite evidence

For every positive ordinary input and every actual inherited compiler slice, the construction supplies infinitely many full positive 18-coordinate child zeros. Consequently the proposed 83 polynomial accepts all positive inputs on those slices; any proper compiled language, including the existing rejecting compiler, refutes its intended soundness. The sound 84 theorem is unaffected because restoring alpha gives `alpha_sum-Z<0` on the constructed tail.

As supplementary independent checks, a new scratch calculation used the explicit two-orbit wrap construction for 30,600 `(M,K)` pairs, independently of the author's sign-search routine. A separate modular Pell calculation checked 30 auxiliary CRT cases at A=2 through 6, both signs, and three index lifts. It evaluated the numerator modulo `S*c*f` before exact division by S, thereby verifying both target congruences and divisibility by `c*f` without materializing huge V. These bounded checks do not prove the prime or density theorems, and none is described as a materialized full compiler zero.

The review is mathematical/source-interface scope. It is not a separate audit of the author's complete receipt/API or a new execution of historical suites. The [separate source review](review_complete83_outer_slack_collapse_source.md) covers the independent complete paid-source comparison.
