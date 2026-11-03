# Independent review: coherent scaled reverse data

`TenPositiveScaledReverseData.reverse_data`, in `research/ten-positive-scaled-reverse-data-prototype/ScaledReverseData.lean`, is a conditional semantic theorem over an arbitrary `ORingStructure V` satisfying `IΣ₁`. It quantifies over `X,Y,mu,r,eta,zeta,b,t : V`. It assumes `1≤X,Y,mu`, `0<r`, `X=Exp.exp (2*r+1)`, `72*r<X+1`, the additional phase condition `(2*r+1)%4=3`, and positive input `eta,zeta`. It also assumes both unscaled interval equations

```text
ycoord (2*r+1) (Y*(X+1)) =
    2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y+eta
2*ycoord (r+1) (2*(X*Y*Y-1)+1) = eta+zeta.
```

In particular the input ordinate parameter is `Y*(X+1)`, while the new scaled parameter below has `-1`. The explicit phase hypothesis is not dropped; `b,t` are arbitrary natural-model inputs. No graph-zero or positivity assumption on them appears.

With `P=X*(mu*Y)*(mu*Y)`, `a=(mu*Y)*(X+1)-1`, `R=2*r+1`, `K=2*ycoord (r+1) (2*(P-1)+1)`, `C=ycoord R a`, `D=delta a`, `H=4*a+3`, and `Kpos=X*(3*C-2*X)+2`, the theorem gives **one** existential tuple `eta',zeta',i,T,n,tau,f,u,y,I,rho`. It asserts positivity of the first nine components through `y`, but not of `I` or `rho`. The same tuple satisfies

```text
C=K*Y+eta'                       K=eta'+zeta'
K=R+1+(mu*mu)*rho               1+(P*K)*(P*K+K)=tau*tau
f*f=1+A                         Q=I*I
I*I*u*u+y*y=1+I*I*y*y
```

where `U=i*C*C`, `A=D*U*U*tau*tau`, and `Q=D*(4*A*(1+A))`. The remaining two equations are in `DiffRing V`, with `ι` the natural embedding:

```text
ι(1+4*A*(1+A))*(ιC*ιT-ιR)-ιC = ιu
(ιb*ιmu*ιmu)*(ιH*(ιn-ιu*ιu*(ιb*ιt))+ιKpos)
  - ιH*((ιmu*ιmu)*(ιb*ιt)+ιb*ι(K-R-1))
= (ιb*ιmu*ιmu*ιH)*(ιtau*ιf*ιy).
```

The latter subtraction `K-R-1` is a natural-model subtraction inside the cast; the proof first derives its exact value `mu*mu*rho` from the offset equation. The proof uses κ returned by `scaled_start` as the arbitrary lower bound for `scaled_auxiliary`, so the same auxiliary `f` obeys `κ<f`; it feeds that tuple and κ to `positive_carrier`, preserving the same `tau,f,u,y`. It produces Q's square and the E/V/Z identities algebraically. The fresh `eta',zeta'` are not asserted equal to the input witnesses.

The theorem does **not** construct or bind a valuation for the selected 80 expression graph. Connecting its scalar identities to the exact graph nodes, deriving the explicit source and transport assumptions from a 90 zero, and establishing external coefficient binding and a syntactic iPRA proof remain separate. No 90-to-80 implication is asserted here.

`check.py` checks the accepted `observations/data-attempt04/terminal.json`, current and copied source, runner, output and logs, and exact first resolution of all three direct imports against the runner's hardcoded pins. The selected direct objects exactly match the already-reviewed scaled start, scaled auxiliary and reverse-carrier objects. All paths and hashes are in `check-output.txt`; accepted object `/tmp/scaled-reverse-data-a0dldod6/ScaledReverseData.olean` has SHA `43dcd0831c6b0c56a9d07ce543f6cc2139e08da25d0ff51c1700ac94b583da58`. The log reports `[propext, Classical.choice, Quot.sound]` and no error, warning or `sorryAx`. No Lean replay was performed; transitive provider selection, package/dynamic libraries and source-object ancestry remain inherited.
