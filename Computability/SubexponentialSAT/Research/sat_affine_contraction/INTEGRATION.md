# Suggested ProveIt integration

Suggested research directory:
`Computability/SubexponentialSAT/Research/sat_affine_contraction/`.

Suggested index entry:

> Affine-plane cached contraction. Reviews 29 refinement packets and the newly
> public Anthropic ETH formalization. Four affine partitions of F3^2 and a joint
> integer plan selector give local coefficients 1/sqrt(3) for time and
> sqrt(7/27) for storage. With an exact twelve-group support certificate and a
> paid 9 -> 12 -> 9 -> 7 -> 4 schedule, generic normalized-wire coefficients are
> 30.257035611496... time and 25.989067718690... space (eventually 30.26 and 26.00),
> improving the incoming 30.891018920366... / 30.753912832055... pair.
> Subexponential memory; SAT logarithmic order unchanged. Ordinary proofs and
> exact finite checks, with inherited contraction and matrix interfaces. No
> full solver or new formalization.

The project trust/status summary should separately update its older statement
that the Claude formalization is unavailable: the public source exists in
anthropics/formal-math at commit 1a6eee293b9e00cb432eef6018a21f523623a9af.
The paper and source scope differ from the OpenAI development; the new source
does not automatically formalize the ProveIt Cauchy refinements.

Keep the generic polynomial-space coefficient 46.184845586731... and existing
stronger-premise low-degree alternatives. The new cached time/space pair does
not supersede their resource or input-premise guarantees.
