# Independent audit of the K223 source and emitter

**Result: pass.** The proposed source has 4,581 primitive instruction occurrences,
209 source DAG nodes, maximum depth 38 and maximum consecutive-zero address run
6. Its two formula changes are exactly the changes described below. The audit
also proves that the complete changed source block implements an independently
assembled reference program for every natural register valuation.

This audit was developed separately from `construct_g226.py` and
`check_g_emitter.py`. The new checker imports neither script, neither script's
receipts, nor the grammar search. It uses the pinned upstream source utilities
and local register-program bisimulation checker, which remain explicit trusted
dependencies. The separate theory, transition-fold and binary-runtime
certificates establish the other parts of the construction.

## Exact changes

Let `I`, `R`, `Q` and `E` denote the numerical constructors

\[
 I(x,y)=4P(x,y),\quad R(x,y)=4P(x,y)+1,\quad
 Q(x,y)=4P(x,y)+2,\quad E(x,y)=4P(x,y)+3.
\]

Let \(N(x)=I(x,1)\),
\(A(x,y)=N(I(x,N(y)))\), and
\(XA(v,x,y)=N(Q(v,I(x,N(y))))\).
Here the parameters \(a,b,c\) are arbitrary natural numbers. In particular, the
symbolic expression checks do not assume that the inputs are codes of orthodox
formulas.

The old seventh row is

\[
 E(c,a)\to\bigl(E(c,b)\to E(a,b)\bigr).
\]

The new row is exactly

\[
 G(a,b,c)=E(c,a)\to
 \bigl(E(c,b)\to Q(R(a,b),E(a,b))\bigr).
\]

The unchanged fused set-theoretic core can be written as follows:

\[
\begin{aligned}
 D&=Q(c,I(R(c,a),R(c,b))),\\
 T&=Q(b,I(c,XA(b,c,R(b,c)))),\\
 S&=XA(a,c,Q(a,I(D,T))),\\
 K_f&=XA(c,I(c,R(b,c)),Q(b,I(R(b,c),S))).
\end{aligned}
\]

The unchanged membership-vacuity term is
\(V=I(R(a,b),Q(c,R(a,b)))\), and the old separate equality-vacuity term is
\(H=I(E(a,b),Q(R(a,b),E(a,b)))\). The old bundle

\[
 N\bigl(I(K_f,I(V,N(H)))\bigr)
\]

is replaced by the exact arithmetic expression

\[
 A(K_f,V)=N\bigl(I(K_f,N(V))\bigr).
\]

The gate is retained literally: if \(c=a\) or \(c=b\), this row emits 0;
otherwise it emits \(A(K_f,V)\). All other primitive instructions are unchanged.
The logical certificate proves that the new equality row provides the removed
helper. This source audit establishes the exact code emitted by the modified
program; it does not assert that the two programs emit the same numbers.

| Part | K224 primitive occurrences | K223 primitive occurrences | Change |
|---|---:|---:|---:|
| Seventh equality row | 300 | 409 | +109 |
| Gated K bundle | 2,077 | 1,750 | −327 |
| Entire source | 4,799 | 4,581 | −218 |

## Independent source binding

The independent checker recovers the literal arithmetic-constructor programs
from the supplied baseline and checks each against its upstream macro using
all-register local bisimulation. It then constructs the four displayed formula
words independently and symbolically executes them with an arbitrary prior
top and stack marker. Comparing expression trees proves their arithmetic
identities for every natural \(a,b,c\), rather than for a sample of inputs.

Every primitive leaf of the proposed complete source is compared against the
baseline after the two declared replacements. A stronger structural check
verifies that the tree outside the common closed source block at address
`11101001001110` is unchanged. Inside that block, the checker independently
assembles 75 closed factors from retained baseline fragments and the new literal
macro words. The supplied local bisimulation algorithm proves this reference
block and the optimized block equivalent for all register values. Finally, two
independent source CFG resolvers agree on all 5,956 guarded cases.

This last step matters because equality of primitive instruction words alone
would not certify the targets of the source language's relative branches.

## Fresh replay of the supplied constructor and emitter

Both supplied scripts also passed a fresh replay against the same independently
obtained K224 package. The reconstructed 226-state parent table and the source
match the supplied files byte for byte:

| Artifact | SHA-256 |
|---|---|
| Source | `fe3713adaf008a71ba4fbc6433de760ef124b8638efbc5c75e3afa2c1142c24f` |
| Parent 226-state table | `e7069fe4dc12fe62ba66cd88c27a51bfd83d548daad07591d3e0b0afaf6afe3d` |

The constructor's compound decoder check covers 4,579 entries. These finite
source checks are complemented by the main packet's separate unbounded binary
runtime and three state-fold certificates. They are not a substitute for those
certificates.

## Files and reproduction

- `independent_k223_source_audit.py`: the additional independent checker.
- `independent_source_receipt.json`: its full source and macro bisimulation
  receipts, exact formula words and expressions.
- `replayed_construction_receipt.json`: fresh replay of the supplied constructor.
- `replayed_emitter_receipt.json`: fresh replay of the supplied emitter checker.

The checker has no fixed workspace paths. After the main replay has been run
with `--output-dir ../K223_replay`, run the following command from the packet
root. Python assertions must remain enabled.

```bash
python3 -B additional_research/audits/independent_k223_source_audit.py \
  --baseline-root ../K223_replay/baseline-input/K224_Construction_2026-10-20 \
  --upstream226 ../K223_replay/baseline-replay/upstream/K225_Construction_2026-10-19/portable/baseline226 \
  --sites portable/results/sites.json \
  --output ../K223_replay/independent_source_receipt.json
```

The audit covers the numerical emitter and register source semantics. The
main packet separately supplies the calculus calibration to the inherited
K224/ZFC result, actual binary transition tables, all-tape fold proofs, and
unbounded runtime cases. No new proof-assistant endpoint is claimed by this
additional checker.
