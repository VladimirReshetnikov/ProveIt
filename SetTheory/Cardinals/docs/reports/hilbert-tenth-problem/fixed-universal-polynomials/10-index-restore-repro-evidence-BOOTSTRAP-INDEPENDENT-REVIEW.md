# Independent review of the provisional positive-index bootstrap

## Verdict and exact scope

**PASS for the four stated partial lemmas, on the intended strictly positive child domain with valid fixed compiler numerals.** No missing positivity hypothesis or circular use of `R>0` was found. The proof establishes `p` odd with `p>=13`, applicability of the generic strong-rank argument, `U>0`, `R=+/-p (mod c)`, and `(p+1)/2<=n<=p-1`.

It does **not** establish `R>0`, an exact representative `R=p`, an exact first index `2n=R+1`, a full counterexample, a positive-domain equivalence, or an improved universal bound. In particular, the whole positive half-binomial kernel theorem is not being invoked outside its hypotheses: only the elementary first-norm classification and separately verified rank/step-down subarguments are used.

Reviewed snapshot: `provisional_bootstrap.snapshot.md`, SHA256
`581e2192aa156dd82ad3450bd8ce85444cf4bf06c0a4814a88b867f964eeb033`.

All upstream material is pinned to `VladimirReshetnikov/ProveIt` commit
`2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff`. The exact retrieved UTF-8 bytes, Git blob hashes, SHA256 hashes, and public URLs are in `source_manifest.json`. Each Git blob hash was recomputed and matched the connector's returned hash. The JSON source receipt itself hashes to `7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28`; its field `source_sha256=7c4b10...` identifies the upstream Python source, not the JSON bytes. The provisional note accurately calls it the *recorded source* SHA256.

No upstream Python code, JSON arithmetic schedule, or historical module was executed. Independent local checks read the schedules as data and compare literal gates; their Pell computations are newly written and supplementary to the proof below. No upstream file was edited and nothing was published.

## 1. Literal source and domain audit

The exact child schedules in `complete74_nonlinear_index_projection_scout.json` were compared with all three parents in `complete74_factored_first_norm.json`. In every mode:

- `r1=r+1` and `R11=r1+hpm1` are removed; `hpm1=h*UM` remains
- `index_partial=actual_k-hpm1` and `restored_r=index_partial-1` are inserted
- both the packing comparison and `H17=jc-r` use the restored expression
- exactly the comparison `actual_k=R11` and the supplied coordinate `r` disappear
- all 72 common gates are retained with precisely this substitution, and the remaining comparisons and complete SOS finalizers have the advertised structure

Actual `k` is supplied `k` in raw30 and computed `R10b=eta+zeta` in the other modes. The raw comparison `k=R10b` is retained; it is not substituted on arbitrary off-zero tuples. Raw comparisons likewise identify supplied `a,c,d` with the triangular expressions. Source register `A` is mathematical `Delta=a^2+4a+3`, not mathematical `A=a+2`; source `ic2` is `Qaux=ic^2`, not restored `R`, outer `Jrep`, or input `rho`.

The literal factored first norm is `first_root_base=E*kY`, `first_next=first_root_base+k`, `L9=first_root_base*first_next`. Thus `L9=k^2*XY^2*(XY^2+1)` exactly. Its comparison with `tau^2-1` is retained. Every other common displayed equation is supported by its literal gates/comparisons. The check matches 40, 40, and 41 relevant gates respectively, in addition to the full structural transfer.

All *supplied* retained coordinates and ordinary input are strictly positive integers. The word `signed20` permits signed arithmetic intermediates, not signed supplied witnesses. Computed `k,c,a,D,Qaux` are positive in all modes; signed20 has `gamma=rho+sigma>0`. Computed `R`, `U`, `W`, or input root `mu` are not assumed positive merely because they are registers. SOS zero over the integers forces every retained residual to vanish. That reasoning is not asserted over arbitrary commutative rings.

Valid compiler numerals supply `B=2^d>=16`, `Bm1=B-1`, the mask ranges, and nonnegative `K0=DC+B*DR`. These are fixed source-contract conditions. The result is not a theorem for arbitrary assignments to free numeral ports.

## 2. Projection bootstrap without positive R

For integer `A>=2`, `Delta=A^2-1` is nonsquare and the least positive integer-coefficient norm-one unit is `A+sqrt(Delta)`: coefficient one already gives the solution with first coordinate `A`, and increasing positive coefficient cannot give a smaller unit. Since `D,c>0`, the main norm therefore gives unique `p>=1`, `D=chi_A(p)`, `c=psi_A(p)`.

The sequence `z_p=chi_A(p)-a*psi_A(p)` has initial values `1,2` and characteristic recurrence coefficient `2A`. For the sequence `2^p`, the recurrence discrepancy is

`2^(p+2)-2A*2^(p+1)+2^p=(5-4A)*2^p=-H*2^p`.

The projection equation gives `z_p=X+gamma*H`, so `2^p=X (mod H)`. Since `a=Y(X+1)>X>0` and `H=4a+3`, write `2^p=X+ell*H`. If `ell<=-1`, the right side would be negative; hence `ell>=0`. Thus `2^p>=X>=q^3>=4096`, giving `p>=12`. No packing estimate, auxiliary norm, first-index representative, or sign of `R` enters. In particular this proves a lower bound, not exponent no-wrap or `X=2^p`.

## 3. Strong-rank hypotheses, integrality, and U positivity

For `A>=2`, `psi_A(p)>=(2A-1)^(p-1)`. With `p>=12`, this exceeds `A*(A^2-1)^2`: indeed `2A-1>A`, and `A^(p-1)>=A^11>A^5>A*(A^2-1)^2`. It also exceeds `2p`, because `3^(p-1)>2p` for all `p>=12` (base case and induction). Thus the exact strict rank hypothesis `c>A*Delta^2` holds independently of `R`.

The generic argument in `PELL_RELAXED_AUXILIARY_PROOF.md`, under “The relaxed norm forces an integral Pell solution at A” and “Recovering the required divisibility of the auxiliary index,” needs only:

1. integer `A>=2`, `Delta=A^2-1`, positive `p`, and `c=psi_A(p)`
2. `c>A*Delta^2`
3. positive integers `Qaux=i*c^2` and `f`, with `Qaux^2=Delta*(f^2-1)`

Its historical preliminary use of `A=a+4` is solely a way to obtain these hypotheses; it is not a hypothesis of the subsequent rank calculation. To check the internal divisibility step, write `Delta=(F^2-1)S^2`, `A=chi_F(e)`, so `psi_F(ep)=S*c`. Write the auxiliary solution as `f=chi_F(t)` and `Qaux=(F^2-1)S*psi_F(t)`. Strong divisibility yields `h=psi_F(gcd(t,ep))>=c/Delta`. If the gcd is a proper divisor of `ep`, doubling and `S<A` imply `h^2<A*c/2`, contradicting `h^2>=c^2/Delta^2>A*c`. Hence `ep|t`, yielding `f=chi_A(m)`, `p|m`, and `Qaux=Delta*psi_A(m)`.

Writing `m=p*l`, the binomial congruence `psi_A(pl)/c=l*D^(l-1) (mod c)` and `gcd(D,c)=1` give `c|Delta*l`. Here `D` is the main root, not the discriminant. Separately `c=p*A^(p-1) (mod Delta)`, so `gcd(c,Delta)=gcd(p,Delta)|p`. Consequently `c|p*l=m`. All extracted Pell indices are positive; `f=1` is excluded by `Qaux>0`.

Therefore `m>=c>2p` and

`f=chi_A(m)>=chi_A(2p)=1+2Delta*c^2>2c`.

The *retained* equality `U=of-c`, with supplied `o>=1`, now gives `U>=f-c>c>0`. This does not use `U=jc-R` to infer positivity and does not assume `c>R` or `R>0`.

## 4. Odd index and rank congruence

We have `Qaux=ic^2>1` and positive `U,y`. The auxiliary norm is exactly

`(Qaux*U)^2-(Qaux^2-1)*y^2=1`.

Its positive Pell classification gives `s>=1`, `Qaux*U=chi_Qaux(s)`, `y=psi_Qaux(s)`. Even `s` would give `chi_Qaux(s)=+/-1 (mod Qaux)`, contradicting divisibility by `Qaux>1`; hence `s=2b+1` with integer `b>=0`.

The integer polynomial identities in `HALF_PARAMETER_PELL_92_PROOF.md` §3 apply exactly:

`U=Q_b(Qaux^2)`, `Q_b(0)=(-1)^b*s`, and `Q_b(1-A^2)=(-1)^b*psi_A(s)`.

Modulo `f`, the relaxed norm gives `Qaux^2=1-A^2`, while the linear equation gives `U=-c`. Squaring produces `psi_A(s)^2=psi_A(p)^2 (mod f)`, and the Pell doubling identity yields `chi_A(2s)=chi_A(2p) (mod f)`.

The stronger *plus-sign* step-down in `EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` §2 requires `A>=2`, `m>=1`, `n>=0`, `0<k<=m`, and `chi_A(n)=chi_A(k) (mod chi_A(m))`. Here take `n=2s`, `k=2p`, and use the already established strict `2p<m`. The result is `2s=+/-2p (mod 4m)`. Dividing an integer equality by two gives `s=+/-p (mod 2m)`; no nonunit division in a residue ring occurs. Since `s` is odd, `p` is odd, so `p>=13`.

Also `c|m` and `c|Qaux`; modulo `c`, the polynomial identity and `U=jc-R` give `-R=(-1)^b*s=+/-p`. Thus `R=+/-p (mod c)`. The full fixed-minus parity theorem is **not** applied: it would require the congruence involving `p` itself, rather than an unrestricted representative `R`. No conclusion `p=3 (mod 4)` follows from these common lemmas alone.

## 5. First/main index interval

Put `V=XY^2`, `P=2V+1`. For `V>=1`, `V(V+1)` is nonsquare; coefficient one gives no positive Pell solution, whereas coefficient two gives root `2V+1`. Thus the elementary classification in `pell_kernel_half_binomial42.md` §3 supplies `n>=1`, `k=2*psi_P(n)` with no scale/index assumptions beyond `X,Y>0`.

In this source `X,Y>=4096`, so

`P-A=XY(2Y-1)-Y-1>0`.

If `n>=p`, monotonicity in both the parameter and index would give `k=2psi_P(n)>psi_A(p)=c`, contradicting `c=kY+eta>k`. Hence `n<p`.

Set `P2=chi_A(2)=2A^2-1`. Direct expansion gives

`P2-P=2[Y^2(X^2+X+1)+4Y(X+1)+3]>0`,

and `A>Y+1`. If `p>=2n`, composition yields

`c>=psi_A(2n)=2A*psi_P2(n)>=2A*psi_P(n)=A*k>k(Y+1)`.

But `eta,zeta>0` and `k=eta+zeta` imply `0<eta<k`, hence `c=kY+eta<k(Y+1)`. This contradiction proves `p<2n`. With odd `p`, the exact interval is `(p+1)/2<=n<=p-1`.

Finally `P=1 (mod E)` implies `psi_P(n)=n (mod E)` by recurrence. The restored identity therefore gives only `2n=R+1 (mod E)`. A signed representative can wrap; replacing it by equality would be unjustified.

## 6. Remaining obstruction, masks, and optional auxiliary addendum

The literal source uses the *paid shifted* mask `MF_source=MF_native+B-1`. With `0<MC,MF_native<B-1`, `MC=2 (mod 4)`, `MF_native=4 (mod 8)`, define

`T'=MC*J+1+q*(MF_native*J-1)` and `S'=Z+qF-1`.

Then the literal packing expression is exactly `R=(q^2-S')(q^2-1)+T'`, with `0<T'<q^2-1`. Thus `R!=0`. Since `S'>=q`, it also gives `R<q^4` without assuming a lower bound. The lower bound `R>=3q+1`, the estimate `Z<q^2`, and consequent input-root positivity in the old signed proof are **not** available: each depended on first excluding the negative representative.

For raw30/positive22, supplied `W>0` and `C=Z+W<q` give `Z<q`. Transport gives `F<(K0+X)q`. If `R<0`, dropping the positive mask and the subtractive `q^2` term gives the safe estimate `-R<(Z+qF)q^2<q^3+(K0+X)q^4`. No bound `K0<B^2` is assumed or certified here. The asymmetric-scale source defines `C=q-F-Z-alpha-2dx`, whereas the present signed20 source defines `C=q-alpha-2dx`; its stronger `F+Z<q` cannot be imported.

The author's subsequent auxiliary-only observation is also valid. For any `A>=2` and `p=3 (mod 4)`, put `c=psi_A(p)`, `m=2cp`, `f=chi_A(m)`, and `Qaux=Delta*psi_A(m)`. The Pell binomial expansion gives `c^2|psi_A(m)`, so `i=Qaux/c^2` is a positive integer. For `s=p+4mt`, `t>=0`, the exact normalized root `U=chi_Qaux(s)/Qaux` has `U=-p (mod c)` and `U=-c (mod f)` and grows unbounded. For any integer `R=p (mod c)`, eventually `j=(U+R)/c>0`; also `o=(U+c)/f>0`. Thus the isolated auxiliary block permits either sign of such an `R`. This observation does not solve the other child equations. The accompanying finite fixture uses `A=2,p=3,c=15,R=-12,m=90`, explicitly outside the full scale/bootstrap hypotheses, solely to check this isolated algebra.

## 7. Reproducibility and evidence limit

Run `python positive-index-bootstrap-independent/audit_checks.py` from the shared workspace, or invoke that file by absolute path. `audit_results.json` records the snapshot/source/checker hashes, the three literal structural comparisons, and these independent finite checks:

- 1,312 projection congruences and 608 growth inequalities
- 480 odd-quotient identity triples
- 208,530 full plus-sign step-down equivalence cases, including its `k=m` boundary
- 640 first-norm identities and 1,440 composition/parameter comparisons
- 3,360 native/shifted mask cases and one exact auxiliary-only negative-R fixture

These checks passed. They supplement, rather than establish, the unbounded mathematical arguments above. The final determination is **a valid partial bootstrap with the original positive-inverse obligation still open**.
