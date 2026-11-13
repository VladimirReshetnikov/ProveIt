# Independent review: witness-preserving 13/90 Pell source draft

The reviewed source preserves the first-index witness and connects the
oriented main root to the matching Pell abscissa using the same ordinate.
No mismatched witness, missing explicit premise, or incorrect imported
statement was found at the source-interface level. This is not a Lean
elaboration, a verification of imported theorem proofs, or an iPRA result.

The deterministic independent checker reverses the added conclusions and
namespace/import changes in each of the two copied modules, then compares
the result byte-for-byte with its pinned predecessor. It confirms that:

* the early-index witness `n` has the appended first ordinate equation and
  the **same** returned quotient `w` used in `k=2*n+4*m*w`;
* the graph witness carries that exact `n,w` forward and rewrites the
  independently classified main ordinate at its index to the actual rank;
* the final client destructures those same `n,w`, preserves `2*n=rank+1`,
  and uses the same `w` in `W=4*X*q*(v7+1)*w` for the balance.

The main abscissa is deliberately recovered again for the **oriented** main
root, rather than asserting it equals the earlier natural norm root. The
pinned `solution_index` requires the natural norm and returns both coordinates
at one index `t`; the pinned strict monotonicity of `ycoord` identifies that
`t` with rank because both ordinates equal `c`. Thus the intended argument
really uses the oriented main root and matching rank. The separate orientation
source returns the same positive `main`, its balance, and its norm. Its
premises include `U>0`, `Y≥8`, `k>0`, and the exact magnitude norm; these
are supplied in the source through other, also unelaborated graph clients.

The proposed balance uses the 13/90 carrier with its explicit `X*Y*q` term.
The pinned `q_balance` interface requires positive `q,Y`, the exact Y
factorization, the exact k-index equation, and the oriented root equation.
Its cancellation is of `q*Y`, not an assumed `q∣X` or Bézout fact. The
independent numerical controls verify the rearranged identity
`root_residual = q*Y*balance_residual` on bounded test inputs; they do not
prove it in the model or verify a graph root.

The final `graph_power` source retains graph zero, `J>0`, `beta>0`, `X>0`,
the positive gap and rank window, plus the explicit **model-natural**
`46≤q` premise. It obtains `q∣3X` from a separate graph draft and supplies
that exact premise to the power client. Graph-zero extraction, compact port
casts and bounds, the positivity and gap proofs, the numerous draft module
providers, Lean tactic success, and all iPRA translation remain open. This
is the shifted-eta 13/90 graph: no eta-zero extension follows from this
packet.

Run from this directory:

```
python3 -I -S -B check.py > /tmp/residue-witness-pell-independent.json
cmp result.json /tmp/residue-witness-pell-independent.json
```

The checker pins the source files and runs 300 exact finite balance controls
and 160 standard Pell-coordinate controls. Those tests and lexical/source
inspection do not replace Lean verification or establish theorem/provider
closure. No reviewed source is modified.
