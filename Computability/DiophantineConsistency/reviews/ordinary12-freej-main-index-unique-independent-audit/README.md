# Independent free-J main-ordinate index uniqueness review

This reviews source and paired replay `145e572eb1`. For any model `V` of IΣ₁,
any four natural-number ports `p`, and any 12 positive model coordinates `v`,
the Lean theorem assumes `p₀>0`, `p₂<p₀`, `p₃<2p₀`, and an `InternalZero`
of the exact free-J literal at `v`. It then applies to **every** model index
`m` satisfying

```
ycoord m (v₅v₆+v₆) = v₈+v₆(v₈+v₉).
```

With `q=1+v₀p₀`, the theorem concludes

```
m = ((q−1)(q−v₁)+v₂)(q²−1) + (p₂+q p₃)v₀.
```

The proof uses the separately audited exact-ordinary theorem to obtain an
index `π` with the same ordinate and `π=R`, then uses injectivity of the
strictly increasing Pell y-coordinate to show `m=π`. No `β≥46` premise is
used. The theorem does not identify an index unless its displayed ordinate
equation is known; it does not calibrate compact44 ports, verify its checker,
simulate a machine, or construct an iPRA derivation.

The read-only audit verifies all committed packet bytes, both child source,
object, compiler-log and seed hashes, complete paired parent overlays, exact
direct imports, and the rerun of the audited exact-ordinary parent. The
recorded outer wrapper session 55299, both compiler steps and both dependency
queries exited 0; sibling objects match. The exact named axiom report lists
Lean metatheory `propext`, `Classical.choice`, and `Quot.sound`, with no
warnings or `sorryAx`. The first exploratory attempt and its exit-1 namespace
failure remain in the packet, not as successful proof evidence.

The inherited graph source-manifest-at-read qualification remains: the
historic driver did not authenticate that manifest's bytes continuously at
its execution-time read. The Foundation outer-wrapper exit remains
unobserved; complete package-transitive and dynamic ancestry are not
authenticated. Sampled RSS is not a hard process-tree quota, and the
`--deps` timeout does not establish a whole-tree resource guarantee.

Run from the repository root:

```
python3 -I -S Computability/DiophantineConsistency/reviews/ordinary12-freej-main-index-unique-independent-audit/audit.py
```

Actual audit session 86436 exited 0. The script performs no Lean compile and
reads original `/tmp` artifacts; missing or changed pinned files fail closed.
Hash checks are point-in-time checks.
