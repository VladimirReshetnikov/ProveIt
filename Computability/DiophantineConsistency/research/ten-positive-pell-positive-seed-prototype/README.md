# Positive ordinary-factor coordinates from a Pell phase

`TenPositivePellPositiveSeed.positive_seed` takes a model of IΣ₁ and a
parameter a and phase `R % 4 = 3`. It refines the existing auxiliary Pell
seed to positive ordinary-graph coordinates `t=f-1` and
`n=delta(a)*i+(y-u)`, with `f=1+t`, `u+(y-u)=y`, the two required Pell
norms and the literal T identity. The theorem proves `f>1` from the strong
norm and uses the existing phase-ordinate bound and positive auxiliary
difference theorem to prove `u<y`. It makes no graph, p₁, halt or iPRA claim.

The accepted check `observations/seed-attempt04/` produced
`/tmp/pell-positive-seed-uy1kv11o/PellPositiveSeed.olean`, SHA-256
`ed078395b3fc150da0afcddc029c15e86e292eef9340955d60e82bba2c5fccfc`.
Earlier attempts are retained and failed with parsing or multiplication
association errors. The runner scans every direct `import` in the checked
source, resolves its selected object from the actual ordered LEAN_PATH,
checks a separately declared path and hash before and after Lean, and stores
the resolved path, real path and hash in the terminal receipt. The check
inherits all transitive project/package, historical source-object and dynamic
library limits; direct pinning is not a complete ancestry audit.
