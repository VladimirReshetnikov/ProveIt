# A closed arithmetic specification of the whole compact54 tuple

This replaces the coefficient blobs by one literal 1,294-digit decimal
integer and fixed arithmetic definitions. It changes none of the four
coefficient values. It uses fixed finite sums, integer quotients and
remainders, and rational intermediate evaluation of a fixed polynomial.
The constant definitions contain no search, machine simulation, external
file reference, or consistency assumption.

Let `A` be the literal integer in `COMPACT54_SEED.txt`, printed in full in
the proposed page. For `0 <= j < 430` define

```
d_j = floor(A/1024^j) - 1024 floor(A/1024^(j+1)),
t_j = d_j mod 256,   v_j = floor(d_j/256) mod 2,
h_j = floor(d_j/512).
```

The original transition order was checked to be `j=2*state+read` before
forming `A = sum_j (next_j+256*write_j+512*[move_j=R])*1024^j`.
The source JSON SHA-256 is
`880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755`.
This is provenance for the supplied numeral, not an input to its arithmetic
definition.

Define the following 457 four-tuples `u_i=(w_i,n_i,e_i,s_i)`:

```
u_0=(2,3,3,1); u_1=(5,0,0,0);
u_(2+j)=((1-h_j)(512+t_j),512+j,h_j(256+t_j),v_j)  (0<=j<430);
u_(432+j)=(0,942+j,0,942+j)                         (0<=j<2);
u_(434+j)=(0,j,0,j)                                 (0<=j<2);
u_(436+j)=(0,(j mod 2)+942 floor(j/2),0,6)           (0<=j<4);
u_440=(2,2,2,0); u_441=(3,4,4,698); u_442=(4,4,4,0);
u_(443+j)=(1,6,1,2+j)                               (0<=j<3);
u_(446+3j+k)=(j^2,5,k,5)                            (0<=j,k<3);
u_455=(256,0,0,512); u_456=(0,0,512,512).
```

Put `Q=2^40` and define

```
k_i=2^30 w_i+2^20 n_i+2^10 e_i+s_i,
r_0=0, r_1=1,
r_i=2+sum_(j=2..456) floor((Q+k_i-k_j-1)/Q)  (2<=i<=456),
delta_ij=floor((Q-(i-j)^2)/Q),
lambda_i=2w_i+2^11 n_i+2^22 e_i+2^32 s_i.
```

Every field lies in `[0,1023]`; the keys are distinct and lie in `[0,Q)`.
The quotient in `r_i` is exactly one when `k_j<k_i` and zero otherwise.
Thus `r_i` is precisely the original lexicographic rank after the two
distinguished modes. Also `delta_ij` is exactly the equality indicator
on these indices. Neither definition invokes an unspecified sort routine.

Let `H=2^29`, `T=2^42`, `rho=2^89`, `B=rho^4831`,
`G_m(x)=sum_(j=0..m-1) x^j`, and

```
O=1+255*2^9+255*2^18+2^27+H,
c_i=O-255*2^9 delta_(i,455)-255*2^18 delta_(i,456)
      -2^27(delta_(i,455)+delta_(i,456))+H lambda_i,
Phi(x)=sum_(i=0..456)c_i*x^r_i
 +H*((x^539+2^21*x^517)*G_11(2x)
     +(2^11*x^528+2^32*x^495)*G_10(2x)
     +T*(x^539+x^1203+x^1807))
 +((2^9+H*(2+2^33))*x^567
    +(2^18+H*(2^22+2^33))*x^575)*G_8(2x)
 +(2^27+H*(2^11+2^32))*x^583.
```

Using inclusive integer intervals, set

```
E=[0,456] union [495,504] union {507,508} union [517,537]
   union [539,549] union [567,583] union {1203,1807},
mu=510+2^17+2^26+2^28+H*(4T-1).
```

The four coefficient ports are the following ordinary fixed integers:

```
beta=B-1,
K=rho^33+rho^68+rho^664+rho^1268
  +(rho^2409+rho^3015)*Phi(1/rho)+rho^4877,
MC=B-1-sum_(e in E except 1)rho^e-2rho^507,
MF=B-1+4+mu*(rho^2409+rho^3015)
   +rho^528*G_10(rho)+rho^585*G_11(rho)+rho^1203+rho^1807
   +(2^87-1)*rho^4823*G_4(rho)+(2^38-1)*rho^4827.
```

The `K` expression is integral: `Phi` has degree 1807, whereas both
2409 and 3015 exceed 1807. All negative powers cancel on expansion.
`MF` is the already shifted source port, so `B-1` occurs exactly once.
No auxiliary numeral is an existential unknown in the Diophantine equation.

The independent arithmetic replay expands this `Phi`, verifies every
coefficient against a second direct local-support construction, verifies
that the quotient ranks reproduce the authoritative sorted 457 modes,
and compares every decompressed byte of the four generated integers with
the original compact54 tuple. All 215,492 bytes agree. The right/left
receiver ranks are 374/4. Normal and optimized replay must preserve these
acceptance checks; the verifier uses explicit exceptions rather than
removable assertions. The saved receipt is `COMPACT54_ARITHMETIC.json`.

```
python3 Computability/DiophantineConsistency/tools/verify_one_page_tuple54.py
python3 -O Computability/DiophantineConsistency/tools/verify_one_page_tuple54.py
```

This is a complete finite numeral-identity result. The native window,
Pell, and syntactic-refutation calibration remains the inherited ordinary
mathematical interface, with its currently documented Lean/object-ZFC
boundary. Arithmetic compression of the constants does not itself prove
that calibration or the requested internal consistency equivalence.
