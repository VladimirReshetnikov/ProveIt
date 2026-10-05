# Why the shared-projection W=0 family does not transfer to independent-gamma83

The new non-dyadic W=0 family does **not** transfer while retaining its outer data. The independent-gamma input norm has an elementary factor obstruction at W=0. This is a source-interface clarification using an inherited algebraic obstruction, not a new impossibility result for arbitrary83-operation circuits or a resolution of independent-gamma83.

## 1. Literal source comparison and pins

These files in `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/` were read as inert JSON/text:

| File | SHA256 |
|---|---|
| complete83_independent_gamma_scout.json | ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20 |
| complete83_shared_projection_scout.json | dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c |
| complete83_independent_gamma_scout.md | bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41 |
| complete83_shared_projection_math.md | 1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c |
| complete83_shared_projection_scout.md | e36f465f257836c972b0edf10b865580e14427360d37799433fa7f301a85a4b8 |

Both complete arrays have83 rows and18 positive witness ports. A fresh data-only comparison finds80 identical named rows, two changed rows, and one distinct producer in each. Independent gamma has `modulus_multiple=rho*a4m5`; shared projection instead has `shared_main_partial=D1+shared_projection`. The two changed consumers are `R14` and `exponent_rhs`. The finalizer is literal in both arrays. No array or predecessor helper was executed.

Write `a=R12`, `c=R10a`, `H=a4m5=4a+3` and `Delta=A=a²+H`. Put `kappa=index_rhs=u+delta*Delta`, `u=2dx+b`, and `W=marked_rhs−Z`. Distinguish the meanings of the port named sigma by writing s for its shared-source meaning and gamma for its independent-source meaning. The exact roots are

| Source | Main root D | Input root mu |
|---|---|---|
| shared projection | ac+X+U+sH | a*kappa+W+U |
| independent gamma | ac+X+gamma*H | a*kappa+W+rho*H |

Here U is the positive port `shared_projection`; it is not the source's different computed register UM.

## 2. Exact polynomial map and its integrality boundary

Over every commutative ring, the substitutions

```
U=rho*H,
s=gamma−rho
```

give the exact complete-polynomial identity

`P_shared(U=rho*H,s=gamma−rho)=P_gamma(rho,gamma)`.

The two roots agree by direct expansion, after which every common downstream producer and the full finalizer agree. Some earlier internal producers, including gam and the source-specific partial root, need not have the same individual values.

For fixed common coordinates with H nonzero, the inverse map over the rationals is

```
rho=U/H,
gamma=s+U/H.
```

At a positive shared zero these are positive rationals. They are integer witnesses precisely when H divides U. The accepted shared offset theorem identifies that sector with zero offset and restoration of a positive84 parent. Conversely a positive independent-gamma zero maps positively by the displayed polynomial substitution only when gamma>rho. Its other quotient range remains outside this positive chart. Thus rational agreement of the polynomials does not transfer arbitrary positive integer zeros.

## 3. A direct obstruction for every W=0 outer tuple

The normalized input factor in the independent-gamma source is

`Ninput=(a*kappa+W+rho*H)²−Delta*kappa²`.

Since Delta=a²+H, its reduction modulo H is

`Ninput=W*(W+2a*kappa) modulo H`.

At any full positive zero, the literal scaled strong factor is Delta times the integer normalized strong norm. The complete output therefore equals Delta times a product of seven integer factors minus Delta. Positive q,w,s give a>0, Delta>0 and H>1 before any native decoding. Cancelling Delta shows that the seven factors multiply to1; in particular Ninput is either1 or−1. It follows already that `gcd(W,H)=1`.

More explicitly, at W=0 the factor is

`Ninput=H*(2a*kappa*rho+rho²H−kappa²)`.

It cannot be an integer unit because H>1. This argument requires no main-root classification, exponent recovery, dyadicness, input-period theorem or compiler-mask decoding. It rules out a positive independent-gamma zero for **any** positive choices of its remaining witnesses while its computed W stays0. Merely changing gamma, rho, delta, or even the other native witnesses cannot repair that outer tuple.

For the newly completed shared family, U=E_u and `E_u=2^u modulo H`. Since H=4a+3 is odd and greater than1, H does not divide2^u. Hence H does not divide U, and the rational inverse above fails integrality exactly as the direct norm obstruction predicts. The same shared family also has `X=2^R−2^u` and non-dyadic q, in contrast to the inherited native conclusions for independent gamma; those stronger conclusions are not needed for the obstruction.

## 4. Remaining scope

The comparison blocks transfer of the entire new W=0 construction while preserving its outer data, not every conceivable construction at the same ordinary input. A different independent-gamma zero at that input could change the outer coordinates so that W is nonzero. No such zero is supplied or excluded here, and the independent-gamma ordinary-input language remains unresolved.

The shared source has46 multiplications and37 additions/subtractions; independent gamma has47 and36. Those ledgers describe different polynomials and are not used as evidence for the map or obstruction. Only direct source data and algebra were used; no tests, compiler invocation, repository mutation, or new gate claim accompanies this proof-only note.
