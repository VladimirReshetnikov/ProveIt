# Independent review: fresh scaled reverse start

`TenPositiveScaledReverseStart.scaled_start`, in `research/ten-positive-scaled-reverse-start-prototype/ScaledReverseStart.lean`, is a conditional existence theorem in any `ORingStructure V` satisfying `IΣ₁`. Its inputs `X,Y,mu,r,eta,zeta : V` must satisfy `1≤X,Y,mu`, `0<r`, `X=Exp.exp (2*r+1)`, `72*r<X+1`, and positive `eta,zeta`. The unscaled source must also satisfy **both** exact equations

```text
ycoord (2*r+1) (Y*(X+1)) =
    2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y+eta
2*ycoord (r+1) (2*(X*Y*Y-1)+1) = eta+zeta.
```

The unscaled ordinate above uses parameter `Y*(X+1)` exactly; the new scaled parameter below includes `-1`. Neither hypothesis is derived in this theorem.

Set `P=X*(mu*Y)*(mu*Y)`, `B=2*(P-1)+1`, `a=(mu*Y)*(X+1)-1`, `K=2*ycoord (r+1) B`, and `C=ycoord (2*r+1) a`. There exists **one** tuple `eta',zeta',rho,kappa,tau` for those same `X,Y,mu,r` with positive `eta',zeta',kappa,tau` and

```text
C=K*Y+eta'                 K=eta'+zeta'
K=(2*r+1)+1+(mu*mu)*rho   X<C
X*(3*C-2*X)+2=(4*a+3)*kappa
tau*tau=1+P*(P+1)*K*K.
```

The output interval is in the same unscaled Y, and its fresh `eta',zeta'` need not equal the input `eta,zeta`. The same τ is the actual first Pell abscissa and the same κ arises after the scaled size bound. No positivity of ρ is claimed. The proof derives `X<C` using positivity and a lower bound on K, and instantiates the scaled offset and kappa lemmas; the theorem does not construct a graph valuation, prove graph zero, establish the source hypotheses, bind external coefficients, or give an iPRA derivation.

`check.py` verifies current source/runner hashes against the successful `observations/start-attempt02/terminal.json`, copied source, output/log hashes, source-direct imports and the first corresponding object on its recorded `LEAN_PATH`. Both the scaled offset and kappa object hashes match the separately reviewed ingredients packet. All exact selected paths and hashes appear in `check-output.txt`. The accepted object is `/tmp/scaled-reverse-start-g0m8bky1/ScaledReverseStart.olean`, SHA `6a726234ecf2ce8df7efacb9d4d2a0bd9f1dec1fb887543c09c05a83ed13b233`. The recorded axiom report is `[propext, Classical.choice, Quot.sound]`. No Lean replay was performed; full transitive source-object, project/package and dynamic-library ancestry remain inherited.
