# Independent ordinary population-facts review

This reviews source and paired replay `5d45113961`. The Lean theorem is a
conditional model statement, independent of any particular graph or port
tuple. For model variables `q,F,α,J,MC,MF,X,Y,u,v,h,R,j`, its explicit
hypotheses are:

- `q≥16`, `α>0`, `q=2^h`, and
  `R=((q−1)(q−F)+α)(q²−1)+(MC+q·MF)J`;
- `Y=q³s` for some model `s`, `X=2^R`, and `Y,u,v>0`;
- `j≥13`, `2j=R+1`,
  `2·ycoord(j, 2·(X·Y²−1)+1)=u+v`, and
  `ycoord(R, X·Y+Y)=u+Y·(u+v)`.

Under all of these assumptions it proves `3h+2 ≤ population(R)`, in every
IΣ₁ model. The proof reuses half-index and half-binomial results and the
radix rank/population lower bounds. It does not establish that any
free-J graph supplies the assumptions, identify compact44 ports, calibrate a
checker, simulate a machine, or produce a PRA derivation.

The artifact audit checks all eight committed packet files, both source,
object and log hashes, both complete endpoint provider overlays, exact direct
imports and exits, and reruns the audited 342-module parent. Outer session
93136, both Lean children and both dependency queries are recorded exit 0;
the objects match. The exact named axiom report lists Lean metatheory
`propext`, `Classical.choice`, and `Quot.sound`, and the successful logs have
no warnings or `sorryAx`. The source packet also retains its exploratory
success log; it is not substituted for the paired evidence.

Two initial **reviewer-script** attempts exited 1 before parent execution:
the first inherited an inapplicable minimum inventory count of 11 despite
this packet having exactly eight tracked files; the second expected the wrong
literal terminal prefix. The final script checks the exact eight files and
actual `Observed paired wrapper` prefix and then completed successfully.
Neither failure was a Lean compilation or a failure of the author's pair.

The inherited provider does not authenticate all package-transitive or dynamic
ancestry and lacks a complete printed axiom inventory. RSS monitoring is
sampled, not a hard process-tree quota; `--deps` timeout is not a whole-tree
resource guarantee. Original `/tmp` objects are needed for replay and hashes
are point-in-time checks.

Run from the repository root:

```
python3 -I -S Computability/DiophantineConsistency/reviews/ordinary12-freej-population-facts-independent-audit/audit.py
```

Actual audit session 11201 exited 0. It launched no Lean compilation.
