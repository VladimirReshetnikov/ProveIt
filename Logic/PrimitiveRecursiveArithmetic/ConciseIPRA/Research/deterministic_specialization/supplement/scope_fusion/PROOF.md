# One traversal for public grammar and scope

This is an implementation refinement of the unchanged native scalar
Eq/Q/D calculus, not a new mathematical axiomatization. The exact control is
`Research/scalar_uniqueness/code/compact/checker.py` from ProveIt commit
`5d85023b0688e03b75f0ec3a04bb43ef0bb51705`, Git blob
`00361c25eb276ab835103d18c767e80e85b6a04d`. The control source is copied byte
for byte. Both programs retain the same complete integer/list payload check,
the same closed public Eq/Q/D grammar, the same backward packet format,
unused-prefix behavior, and the same proof rules.

## Entry invariant

The old program traverses the public goal twice before consuming a proof
instruction: `v(a)` checks grammatical sorts, arities, canonical Q triples,
and positive variable parity, while the first `i(a)` in `c` checks scope.
The new program combines these traversals in that first `i(a)`. Its new
flag `v` is 1 only for the public entry call and becomes 0 before the first
proof packet is consumed. All recursive calls of `c` use the default 0.

For an integer/list tree `a`, the fused traversal at slot depth `d`, initial
lower bound `k=0`, and flag 1 succeeds exactly when both old traversals
succeed. When it succeeds its value is `a`.

Proof is structural induction on `a`. At a list, the new conditional is
precisely the old shape test:

    len(a) in (1, 2 + d % 2) or a == [a[0]] * 3.

Each child uses the same depth increment `5-len(a)`, so the inductive
hypotheses apply. At an integer the fused acceptance condition is

    0 <= a < d and d % 2 and (not a or a > 2 and a % 2).

This is the conjunction of the old shape/parity test with the old scope
test. If it fails, the new default substitution sentinel is the function
`c`, and `i(c,d=3)` raises TypeError before a proof instruction is read.
Invalid list shapes likewise call `i(c)`. Empty lists raise IndexError at
the repeated-Q test, exactly as rejection rather than acceptance requires.
All raw types have already been validated globally by the unchanged lexical
gate, including types in unused proof prefixes.

Once the public first traversal succeeds, the flag is set to zero. For
flag zero, the new list predicate short-circuits at `not v`, the new
integer guard reduces to `k <= a < d`, and its default-substitution clause
reduces to `d % 2 and i(t,d=3)`. Thus the remaining computation is exactly
the original proof kernel. The entry traversal does not mutate `a` or the
proof packet stream. It follows that both programs accept exactly the same
finite certificates, abstracting from finite interpreter resource limits.

## Measurement and finite checks

Under CPython 3.12.14, normalize by `ast.unparse` plus one LF; count the
complete module. Both include JSON input, the payload check and ACCEPT
output. No custom library is imported.

| Program | UTF-8 bytes | Significant tokens | AST nodes | gzip level 9 |
| --- | ---: | ---: | ---: | ---: |
| Exact current full validator | 866 | 381 | 439 | 504 |
| Fused public traversal | 820 | 360 | 412 | 493 |

The reduction is 46 bytes, 21 tokens, 27 AST nodes and 11 gzip bytes. Gzip
uses level 9 and mtime 0; it is informational rather than an optimization
target. The Python runtime and standard `json` library are common trusted
dependencies, as in the control. This does not beat the 516-byte unchecked
guarded administrative codec and is not a global checker minimum claim.

`python3 verify.py` compares 22,350 integer/list entry shapes, runs 24
unchanged authenticated upstream fixtures, and tests malformed JSON,
free/even/reserved slots, noncanonical Q, administrative roots, and unused
prefix types. There are 62 CLI cases on both programs in ordinary and
optimized Python, totaling 248 CLI runs. The checked proof examples include
contextual equation induction and transport under both D and Q.

Finite checking supplements the structural proof. No Lean/Rocq verification
or identical resource usage, errors, or runtime bound is claimed.
