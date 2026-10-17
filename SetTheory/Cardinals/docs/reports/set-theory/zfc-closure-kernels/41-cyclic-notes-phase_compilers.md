ARCHIVE NOTE: This is a development or independent audit record. The final
article.tex/article.pdf and README.md are authoritative for the delivered
status and runnable archive commands. Some original workspace paths and
earlier-stage comments are retained as provenance. The final U14 source
and its 10,182-node wrapper are included under data/.

# Exact phase optimization for cyclic presentations

These are new compiler components for the proposed E9 and E8 presentations.
They optimize expanded target-term syntax. They do not compile a concrete
ZFC-specific target to a binary Turing machine, and no tree-node saving is
reported as a Turing-state saving. No priority claim over all compiler
literature is made.

## Three phases: E9

Write `n` for Boolean complement and `j` for join. In the E9 signature,
`r^3=id`, and `r` is a Boolean automorphism. The source modal operations have
translations

\[
\tau(c_jt)=r^j c r^{-j}\tau(t),\qquad j\in\{0,1,2\}.
\]

Let `D_t[i]` be the minimum size of a representative of
`r^(-i) tau(t)`, with all arithmetic on phases modulo 3. Costs include every
tree node, including atoms and each rotation. Let `B_t[k]` be the minimum
cost when the representative has no leading `r` at phase `k`.

\[
\begin{aligned}
B_p[0]&=1,& B_p[1]&=B_p[2]=\infty,\\
B_{nt}[k]&=1+D_t[k],\\
B_{u\vee v}[k]&=1+D_u[k]+D_v[k],\\
B_{c_jt}[j]&=1+D_t[j],& B_{c_jt}[k]&=\infty\quad(k\ne j),\\
D_t[i]&=\min_{k=0}^2\{(k-i\bmod3)+B_t[k]\}.
\end{aligned}
\]

If, and only if, the additional **ground** equation `r(p)=p` is included,
set all three base costs of the literal `p` to 1. Schema variables such as
`x`, `y`, and `z` retain `(1,infinity,infinity)`. The implementation exposes
this distinction with an explicit `invariant` option, false by default.

Reconstruction stores the minimizing phase `k`, emits the indicated root
operation and child representatives, and wraps `r^((k-i) mod3)`. Thus the
algorithm uses three finite costs and choices per source node and linear
arithmetic work and memory in the expanded source tree.

### Exactness scope and proof

Keep the source's ordered Boolean/modal tree shape fixed. Permit rotation
distribution through complement and join, extraction of shared rotations,
and cancellation of `r^3`; do not use associativity, commutativity,
idempotence, cylindrifier identities, or other algebraic simplification.

Any candidate representative can first have each leading run of rotations
reduced to length at most 2. Remove that run and inspect its root. An atomic
root has exactly the allowed base phases. A complement or join root has
children at its same residual phase because `r` is an automorphism. A modal
root can be the single native operation `c` only at phase `j`, and its child
must then represent `r^(-j) tau(t)`. These cases exhaust the root forms.
Induction on the fixed source tree proves that the displayed recurrence is
both a lower bound and attained. This is exact optimization in the stated
grammar, not optimization under every E9 identity.

An independent normal-form checker pushes all rotations to the leaves and
records a modal's accumulated conjugacy index. It never calls the recurrence.
Exhaustively enumerating native terms up to a fixed size and grouping by
this normal form therefore supplies an independent bounded optimality oracle.

## Six phases: E8

The smaller native signature has join, `c`, and `s`, with

\[
s=n r^2,\qquad s^2=r,\qquad s^3=n,\qquad s^6=\mathrm{id}.
\]

Even powers of `s` are Boolean automorphisms. Literal translation replaces
negation by `s^3`, and uses `s^(2j) c s^(-2j)` for source modality `c_j`.
The optimizer avoids introducing these chains prematurely.

Define `D_t[i]` to represent `s^(-i) tau_8(t)`, for phases modulo 6. The
recurrences are

\[
\begin{aligned}
B_p[0]&=1, & B_p[k]&=\infty\ (k\ne0),\\
D_{nt}[i]&=D_t[i-3],\\
B_{u\vee v}[k]&=1+D_u[k]+D_v[k] && (k\text{ even}),\\
B_{u\vee v}[k]&=\infty && (k\text{ odd}),\\
B_{c_jt}[2j]&=1+D_t[2j],& B_{c_jt}[k]&=\infty\ (k\ne2j),\\
D_t[i]&=\min_{k=0}^5\{(k-i\bmod6)+B_t[k]\}
&& (t\text{ is not a negation node}).
\end{aligned}
\]

The optional ground law `s^2(p)=p` makes the base costs of `p` equal to 1 at
even phases only. It does not permit `s(p)=p`: that would erase complement
on the designated generator. The optimizer never applies this ground law to
arbitrary substitution variables.

The analogous root decomposition proves exactness in the six-phase grammar.
Double negation is absorbed by the phase shift; no De Morgan, Boolean
reassociation, or modal identity is used. In the independent normal form,
`s^k` is decomposed as complement parity `k mod2` and rotation index
`2k mod3`. Rotations move inward, complements cancel in pairs, and a
complement in front of a join or modal is retained. This permits a second
native-term enumeration oracle that is independent of the six-phase
recurrence.

## Global modal naming

The source Df3 presentation is symmetric in its three modal names. For a
fixed target equation, or an entire family of equations, the implementation
evaluates all six **global** permutations. Every row and both sides receive
the same chosen permutation. The result represents the renamed equations;
it does not claim equality of a term and its renaming in one fixed algebra.
The selected permutation and all six costs are recorded. The constant-factor
search leaves the linear-time bound unchanged.

## Measured syntax reductions

The following counts use identity modal naming, so they isolate phase
optimization from naming changes. `Inv` means the additional literal ground
invariance law is available.

| Source prefix | Source nodes | E9 literal | E9 optimal | E9 Inv | E8 literal | E8 optimal | E8 Inv |
|---|---:|---:|---:|---:|---:|---:|---:|
| `hhhhhhhhp` | 9 | 33 | 12 | 11 | 57 | 15 | 13 |
| `jgngpgjpgp` | 10 | 22 | 17 | 11 | 36 | 26 | 14 |
| `hjgnhphjfpgp` | 12 | 27 | 22 | 19 | 44 | 34 | 28 |

For the first row, E9 emits `r^2 c^8 r(p)`, and E8 emits
`s^4 c^8 s^2(p)`. With ground invariance the innermost rotations disappear.
These examples deliberately do not simplify `c^8` by closure idempotence:
they measure the restricted compiler theorem exactly as stated.

The full 18-row source Df3 axiom list in `rotation9.py` translates literally
to 217 tree nodes and to 199 with the E9 phase compiler. Every source,
literal, and optimized equation side is emitted in
`phase_optimizer_results.json`. This is a check on a finite mathematical
input family, not the unknown size of the ZFC-specific target.

For the three displayed example equations together, a single global modal
renaming lowers the pure E9 optimized total from 57 to 52 nodes. For E8 it
lowers that total from 85 to 65. The result JSONs give all six alternatives.

## Independent checks completed

Both implementations use exact integer costs and deterministic tie breaking.
The tests reject a ground-invariance leak onto schema variables.

| Check | E9 | E8 |
|---|---:|---:|
| All source terms through 6 nodes | 2,156 | 2,156 |
| Native enumeration size bound | 9 | 11 |
| Native terms enumerated | 51,821 | 82,499 |
| Source/phase checks, pure plus ground-invariant | 12,936 | 25,872 |
| Exact optimum matches within native cutoff | 7,205 | 10,352 |
| Certified absence of a smaller term below cutoff | 5,731 | 15,520 |
| Product-algebra semantic comparisons | 497,664 | 995,328 |

The semantic model is `A^3`, with `A` the Boolean powerset algebra of the
eight worlds `{0,1}^3`, and ordinary existential coordinate closures.
The E9 operations are `r(a,b,c)=(b,c,a)` and componentwise
`c=(c_0,c_1,c_2)`. E8 uses `s(a,b,c)=(~c,~a,~b)`. Pure tests enumerate
all 512 triples from the explicit scalar probe set
`{0,1,3,5,15,85,170,255}` on all 98 source terms of at most four nodes.
The invariant tests enumerate **all 256 diagonal generator valuations** of
this product algebra on all 452 source terms of at most five nodes.

These are finite implementation checks supporting the ordinary inductive
proofs. They are not claimed as proof-assistant verification of the compiler,
nor as a ZFC consistency calibration of an emitted binary machine.
