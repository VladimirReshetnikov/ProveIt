# Independent review: guarded trace elimination in thirteen integers

**Decision: PASS for the two literal endpoints and the new ordinary zero-existence bridge**, relative to the retained signed even-strong/native/compiler/refutation calibration. This is not a new proof-assistant replay or a proof of consistency. `ROOTS13_INDEPENDENT.json` binds the reviewed proof and both DAG hashes; the separate CAS reviewer imports neither producer nor its checker.

## Signed and degenerate cases

1. The affine restrictions give even nonzero q, |W|≥4, |X|≥8, and a=(X+1)Y either zero or of absolute value≥7. Hence Delta=(a+2)²−1≥3 and U=2q³(4a+3) is nonzero. The integer ell=XY² is even; Dt=1+ell(ell+1)k²≥1, without a positivity convention on any input.
2. Both N and Hres are squares modulo4. Thus `(N+1)(Hres+1)=1` cannot take the negative-unit branch: N+1=−1 would force a square to be2 modulo4, as would Hres+1=−1. Every new zero has N=Hres=0.
3. Dividing the norm by U⁴ is legitimate. Dt≥1 excludes G<0. Consequently budget=G+1+p2²+p3(p3+1)>0 and Yk≠0. The strict inequality Dt>budget>G follows from |ell|≥8 and |X|≥4|q|. It excludes rho=Z/U=0 **before** dividing by rho. The displayed root formulas then give rational numbers p,tau with integral squares; reduced denominators prove they are integers. This includes G=0, repeated square classes and every sign of the roots.
4. The restored carrier and guard use the exact shift `n_old=n+sL−(2L+k)−p+tau`. The complete carrier identity verifies its vanishing. No root sign or polynomial coordinate-bijection claim is needed.
5. Crucially, the bound |c|>R is available **before** recovering f or invoking Pell classification. Positive budget gives the centered strip and authentic-mask bounds `0<R<|q|⁴−2`; it gives |Y|>|q|² (118 chart) or |Y|>|q|³ (120 chart). Therefore the chosen modulus d=ell or E satisfies |d|>3R+1. Since k=R+1+hd, either h=0 or the triangle inequality yields |k|>2R. Thus |k|≥R+1 and the centered strip gives |c|>|k|(|Y|−1/2)>R.
6. For every signed integer T, b=cT−R is nonzero: T=0 gives −R, while T≠0 gives |cT|≥|c|>R. Because |8r+4|≥4 and c≠0, `delta=Delta² I²−1≥144c⁴−1>|c|`. Consequently t=c+delta*y is nonzero for every integer y, including y=0. These arguments rule out both factors of the resultant denominator; they do not infer them from a later Pell lemma.
7. The exact identity `Hres=Ares²−Fs(2bt)²` now gives rational `f=Ares/(2bt)` with integral square Fs, hence integral f. The independently expanded identity
   `Ea−1=Ares−2bt*f+b²(f²−Fs)`
   gives Ea=1, and the strong equation is literal. Arbitrary signs of b,t,c,k,Y,f are covered. The degenerate resultant branch with Ares=bt=0 is genuinely dangerous without the guard, so omitting this step would not be sound.
8. Every new zero therefore restores a zero of the retained **even-strong fifteen-integer** kernel. Its fresh odd-scale witness construction, rather than reusing the new even trace in an old odd-scale theorem, supplies the inherited calibration. Conversely every even-kernel zero gives Hres=0 by the universal identity. Its carrier provides an integral tau; the stated reverse n shift gives N=0. Thus the reverse map is total on old zeros, not only canonical positive witnesses.

## Independent finite algebra

`check_roots13_independent.py` uses a separately written SymPy implementation and handwritten register formulas. It verifies every literal register, gate topology, output cone, free variable and fixed port. The complete resultant cancellation, signed linearization, four-factor norm, rational-root identities and carrier identity are expanded exactly.

| Variables | Degree | Live operations | Full highest-form terms |
|---:|---:|---:|---:|
|13 unrestricted|118|114 =66mul+27add+21sub|85|
|13 unrestricted|120|112 =65mul+26add+21sub|21|

The apparent degree38 of Ares cancels to22. Hres has degree60. The centered norm has degree58, the uncentered norm60. Their full leading products are independently expanded and have respective nonzero coefficients

- `[j^58 w^16 v^18 z^6 r^6 c^12 y²] P118 = −2^124 3^74 beta^58`;
- `[j^66 w^14 v^14 z^6 r^6 c^12 y²] P120 = −2^126 3^80 beta^66`.

The authentic beta=2^1064921−1 is positive. This certifies exact degree at the actual six-port slice, not merely at generic ports. All six payloads are decompressed and checked for hashes, byte counts and bit lengths with their declared **little-endian** encoding. Their total is615883 raw bytes; no2963 native port is substituted into these unrestricted-integer equations.

Additionally, exact modular automatic differentiation at the recorded integer tuple gives a nonzero partial derivative for **each of the13 inputs**, using the actual fixed numeral residues. This proves genuine input occurrence; syntactic DAG liveness alone would not.

The standard-library producer checker is a separate reproducibility route. The CAS implementation here is an additional independent audit, not a newly required dependency for using the delivered equations.

## Comparison

The118/114 point strictly improves both degree and operation count over the matched previous13-integer152/119 and156/117 endpoints. The120/112 point trades two degrees for two operations relative to118/114. Fourteen-integer85/110 and87/108 remain lower-degree, larger-dimension alternatives; eleven-integer points remain smaller-dimension, higher-degree alternatives. No global minimum is asserted.
