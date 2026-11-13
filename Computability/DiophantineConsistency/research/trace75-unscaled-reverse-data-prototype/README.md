# Unscaled same-tuple reverse data with XY carrier

`Trace75UnscaledReverseData.reverse_data` is Lean checked in every IΣ₁ model.
Under its explicit positive unscaled interval, power, size and phase
hypotheses it constructs one coherent tuple of positive `eta',zeta',i,T,n,
tau,f,u,y` and natural `I,rho`. Its equations include the first Pell root,
strong-root and Q-square identities, positive old squared-trace V, auxiliary
norm, and the signed carrier identity with factor `D=X*Y` and offset `D*rho`.
The theorem also exports `X<C` and the exact interval/offset equations. Its
root f is the root of F0; it is distinct from the doubled trace `1+2*A`.

The proof specializes the existing scaled start to μ=1, uses the existing
auxiliary seed, and applies the independently checked generic carrier and
first-seed XY-divisibility lemmas. The earlier μ=1 carrier with D=1 is not used.
This remains scalar conditional data: it does not bind the actual trace75
registers, discharge its assumptions from BFS halt, or prove an iPRA endpoint.
The accepted author check `observations/data-attempt02/` produced
`/tmp/trace75-unscaled-reverse-gsw8pp2_/Trace75UnscaledReverseData.olean`
SHA-256 `3ef7b82ef551100f48e1f932c0663f786eb4218f100ab8fa154890525baffc80`.
Attempt01 failed on parsing and is retained. The four direct imports are pinned
and rechecked; historical project, transitive, package and dynamic ancestry
remain inherited and have not been coherently rebuilt for this join.
Independent source and receipt audit passed in
`reviews/trace75-unscaled-reverse-data-independent/`; no Lean replay was done.
