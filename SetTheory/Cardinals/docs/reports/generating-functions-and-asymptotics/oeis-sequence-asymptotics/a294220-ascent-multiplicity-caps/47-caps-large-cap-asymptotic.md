# Large-cap expansion of the growth constant

Ancillary result, 1 October 2026. This concerns the explicit integral established in `general-cap-proof.md`. It is separate from that fixed-cap theorem.

## Statement

As the integer b tends to infinity,

    T_b - pi^2/6 ~ (b+1)/2^{b+2}.

Consequently, with mu_b=1/T_b,

    6/pi^2 - mu_b ~ 9(b+1)/(pi^4 2^b).

## Proof

Let f(x)=log x/(x-1), continuously extended at x=1, and let

    R_b(v)=e^v-E_b(v)=sum_{k=b+1}^infinity v^k/k!,
    Delta_b(v)=f(E_b(v))-f(e^v).

Then T_b-pi^2/6=integral_0^infinity Delta_b(v)dv, and Delta_b>=0 because f is decreasing. Fix any c with 2/e<c<1. Split the integral at 2 and cb; we consider b large enough that cb>2.

### Small-v contribution

On 0<=v<=2, f' is uniformly bounded on [1,e^2]. The exponential-series remainder is bounded by

    R_b(v)<=e^2 2^{b+1}/(b+1)!.

Thus the integral of Delta_b on this interval is superexponentially small in b. The same is true for the linear approximation used below on this interval.

### Uniform linearization on 2<=v<=cb

Write x=e^v and p=R_b(v)/e^v. This p is the upper Poisson tail Pr(Poisson(v)>=b+1). Monotonicity in v and the Chernoff bound at parameter cb show

    0<=p<=exp[-b(c-1-log c)] =: epsilon_b.

The exponent c-1-log c is positive. Hence epsilon_b tends to zero exponentially, uniformly over the interval.

The integral representation

    f(x)=integral_0^1 [1+t(x-1)]^{-1}dt

shows f'<0 and f''>0. For x>=e^2 and x/2<=xi<=x, it also gives

    f''(xi)<=16[-f'(x)]/x.

Indeed 1+t(xi-1)>= [1+t(x-1)]/2, and t/[1+t(x-1)]<=1/x. Taylor's theorem, with x-R_b(v)>=x/2 for all sufficiently large b, now gives uniformly

    Delta_b(v)=L_b(v)(1+O(epsilon_b)),
    L_b(v)=-R_b(v)f'(e^v)>=0.

For v>=2 the exact derivative yields

    -f'(e^v)=[v-1+e^{-v}]/(e^v-1)^2
             =(v-1)e^{-2v}+O(v e^{-3v}).

The integrated error is bounded using the nonnegative series for R_b:

    integral_0^infinity v e^{-3v}R_b(v)dv
       =sum_{k=b+1}^infinity (k+1)/3^{k+2}
       =O(b 3^{-b}).

### Large-v tail

For v>=cb and b sufficiently large, E_b(v)>=v^b/b!>=2. Since E_b(v)<=e^v,

    0<=Delta_b(v)<=f(E_b(v))
       <=2 log E_b(v)/E_b(v)
       <=2b! v^{1-b}.

Consequently,

    integral_{cb}^infinity Delta_b(v)dv
      <=2b!(cb)^{2-b}/(b-2)
      =O(b^{3/2}(ec)^{-b})
      =o(b2^{-b}),

where the last two steps use Stirling's formula and ec>2. Convexity of f gives L_b(v)<=Delta_b(v), so this tail estimate also controls the omitted linear integral. For v>=2, (v-1)e^{-2v}R_b(v)<=L_b(v), so it controls the omitted main approximation as well.

### Evaluate the leading integral

Termwise integration, justified by absolute integrability, gives

    M_b = integral_0^infinity (v-1)e^{-2v}R_b(v)dv
        = sum_{k=b+1}^infinity (k-1)/2^{k+2}
        = (b+1)/2^{b+2}.

The preceding estimates therefore yield

    integral_0^infinity Delta_b(v)dv
      =M_b(1+O(epsilon_b))
        +O(b3^{-b})
        +O(b^{3/2}(ec)^{-b})
        +O(2^b/(b+1)!)
      ~M_b.

Finally, since T_b->pi^2/6,

    6/pi^2-1/T_b
       =(T_b-pi^2/6)/[(pi^2/6)T_b]
       ~ (36/pi^4)*(b+1)/2^{b+2},

which is the claimed formula.

## Numerical check

Direct high-precision quadrature gives the following ratios of T_b-pi^2/6 to (b+1)/2^{b+2}:

    b= 8: 1.45664438950221307
    b=12: 1.18302648638858560
    b=20: 1.04549582072938240
    b=30: 1.01055909023252658
    b=50: 1.00074833396526970

These are a check, not part of the proof. Independent audit of this ancillary argument is pending.
