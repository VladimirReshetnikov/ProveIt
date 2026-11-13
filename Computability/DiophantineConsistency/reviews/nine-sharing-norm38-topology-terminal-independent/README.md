# Independent terminal audit of generic topology lemmas

The post-hoc author record reports outer session **81522, exit 0**. The
retained dependency and compile runs each exited 0 without monitor stops,
and the output object remains under
`/tmp/nine-sharing-norm38-topology-check-20261105/lib/DiophantineConsistency/`
with SHA-256 `90661b7bf1e7be709ad2d32e67447e6e05a3d698c975a3e5632566b91fdcca38`.

The compiled `ringRun_agrees_of_topological` theorem is generic: it assumes
topological ordering, initial agreement and reference gate equations, and
concludes replay agreement on completed nodes. Its Lean axiom report is
`[propext]`. The compiled `static_assignment_fixed` theorem assumes the
static `gatesHold` predicate and concludes the represented assignment is a
fixed point of the gate replay; its report is `[propext, Quot.sound]`. These
are Lean metatheoretic dependencies. Neither theorem proves concrete graph
topology, that a seed satisfies the gates, source-field correspondence or an
iPRA endpoint.

`check.py` verifies the exact snapshot against the independently reviewed
draft, both retained logs and axiom-report contents, the successful object,
the direct `NormAssignment38` provider route and hash, all 100 recorded direct
guard slots and 1,065 overlay links. The outer receipt is an author record,
not a raw transcript or an independently observed historical exit. No Lean
process was run by this review. Inherited package/dynamic ancestry, changes
between observations and sampled-resource limits remain outside its scope.
