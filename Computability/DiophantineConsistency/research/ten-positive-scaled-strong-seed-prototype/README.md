# Internal scaled strong Pell seed

`TenPositiveScaledStrongSeed.strong_seed` takes an arbitrary IΣ₁ model, a
Pell parameter a, and positive c and τ. It uses the model-internal
`ordinate_dvd` theorem at modulus `c²*τ` to construct positive m, i and f
with

    ycoord(m,a) = (i*c²)*τ,
    f = xcoord(m,a),
    f² = 1 + delta(a)*(i*c²)²*τ².

It also gives the exact x and y coordinates at `2m`, exposing the doubled
strong trace and ordinate. The construction does not assume an 80 or 90
graph zero, connect τ to a first Pell root, construct an adjacent auxiliary
witness or transport carrier, or establish a reverse graph implication.

Accepted guarded check `observations/strong-attempt02/` produced
`/tmp/scaled-strong-seed-3363ey7t/ScaledStrongSeed.olean`, SHA-256
`cf243b26592c5a56f5712ce2b60e0057a62fd96f531643fbdde944b244427ea1`.
Attempt01 failed on the orientation of a positivity lemma. The runner
resolves and checks both direct project imports in the ordered LEAN_PATH,
recording selected path, real path and digest before and after. Lean accepted
these selected providers together; this is not a complete transitive
source-object, package or dynamic-library audit.
