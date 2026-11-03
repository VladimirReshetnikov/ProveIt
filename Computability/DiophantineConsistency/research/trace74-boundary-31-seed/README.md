# Arbitrary-port trace74 boundary source seed at R = 31

`check.py` verifies a finite partial seed at natural ports `(beta,K0,MC,MF)=(1,1,28,0)` with `J=F=C=1`, so `q=2` and the strict new-chart guard fails at equality `F+C=q`. Set `R=31`, `r=15`, `X=2^31`, `w=2^30`, `Y=8s`, with the exact positive 462-bit `s` given in the script. It uses exact integer Pell recurrences, not floating point.

Let `y_j(a)` be the ordinate for ordinary Pell base `a`, so `y_0=0`, `y_1=1`, `y_(j+2)=2a*y_(j+1)-y_j`. Put `P=XY²`, `k=2*y_16(2P+1)`, `c_source=y_31(Y(X+1)+2)` and `c_actual=y_31(Y(X+1)+1)`. The script checks both `0<c_source-kY<k` and `0<c_actual-kY<k`, the first root `1+P(P+1)k²=tau²`, `72r<X+1`, phase `R mod 4=3`, `XY | k-R-1`, and `H | X(3c_actual-2X)+2` with positive quotient for `H=4Y(X+1)-1`. It also evaluates all 74 candidate rows for the specific trial `i=T=n=1` and verifies that trial output is **nonzero**. The chosen ports violate the fixed symbolic tuple's `0<MC<beta` bound; this is not a fixed-port example.

## Proposed existential completion, not yet a checked 74 zero

The exact seed appears to satisfy the explicit hypotheses of the previously checked `Trace75UnscaledReverseData.reverse_data` with `b=1`, `t=w`, `eta=c_source-kY` and `zeta=k-eta`. Its conclusion supplies positive auxiliary witnesses, including `eta'`, `zeta'`, `i`, old trace coordinate `T0`, `n`, `tau`, `phi`, `u`, `y` and `I`, with `c_actual=kY+eta'`, `k=eta'+zeta'`, `E=tau²`, `F0=phi²`, `Q=I²`, squared-parent `oldV=u`, the signed carrier equation, and `I²u²+y²=1+I²y²`. The input and output are same-witness statements in the checked theorem, but **this concrete specialization and its application to the 74 graph have not yet been formally checked**.

The proposed algebraic binding is as follows. In the 74 graph, the above fixed coordinates give `rank=31`, `B=(K0+w)C-F=w=b*t`, and old-chart `alpha=q-F-C=0`. Write `a=Delta*(i*c_actual²)²*E`, `f=1+2a=1+c_actual*d`, where `d=2*Delta*i²*c_actual³*E`. The source witness equation is `f²(c_actual*T0-R)-c_actual=u>0`. Set `T1=f*T0-dR`; this identity implies `T1>0` and gives `f(c_actual*T1-R)-c_actual=u`. The carrier then has `Z=M*tau*phi*y`. Together with `M²*E*F0=M²*(tau*phi)²`, `Q=I²`, and the auxiliary Pell equation, the 74 output formula cancels to zero. The existing ring coordinate and trace-shift identities support this route, but the currently checked positive old-chart join requires old `alpha>0`, which fails here. A boundary-specific same-witness binding and its natural/model side conditions must be checked before calling this a full zero or a counterexample.

`observation.json` records the finite checks and a hash of the nonzero trial output. No Lean process was launched for this probe; it establishes no 74/75 inequivalence or iPRA result.

Subsequently, the first-source interval and its positive additive slacks have
been [certified in standard `ℕ` by Lean](../trace74-boundary-natural-seed-rebuild/README.md)
using ordinary kernel-checked `decide`, with an independent result audit.
That certificate alone does not discharge the other hypotheses of the
parametric graph theorem or construct a concrete trace74 zero.

Independent review of the finite seed passed: `reviews/trace74-boundary-31-seed-independent/`. It independently recomputed the Pell recurrences, indexing, intervals, rank, divisibilities and nonzero trial; the proposed existential binding remains uncompiled.
