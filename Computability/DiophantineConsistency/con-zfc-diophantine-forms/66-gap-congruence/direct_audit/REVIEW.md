# Independent one-stack review

## Result

No mathematical defect found in the local transition or finite-path argument.
The exact checks in `audit.py` pass without importing or executing the generator
or upstream code. Run `python audit.py`; optimized Python also passes.

The materialized quartic has **91 total natural variables**, namely two exposed
state coordinates and 89 existential local witnesses. Its 85 quadratic
residuals expand exactly to 3,108 monomials of exact degree four. This is only a
local step equation, not a consistency equation. The global constructor is
uncompiled, its output is unmaterialized, and its variable count is unknown.

## Mathematical review

1. The eight literal rows agree with Code254.rho1 through rho6, KCode222.growG,
   and Code254.rho8. In particular the seventh row is growG, not the older rho7.
   The nested req/clos/nks/vrel/bundle expressions agree with KCode222.
   The numerical implication I is exactly four times the specified Cantor
   pairing, with the second-coordinate orientation preserved.
2. Truth is code zero. The factor v squared therefore includes truth without
   imposing an axiom schema. All factors are nonnegative on natural inputs.
   The bundle guard has a natural witness precisely when c differs from both
   a and b: choose u = abs((c-a)(c-b))-1. Reusing u for rho8 is harmless because
   the factors encode an existential disjunction, not simultaneous schemas.
3. The list residual is twice the exact equality to 1+Cantor(head,tail), so it
   introduces neither parity loopholes nor extra nonnatural stacks. Tail
   descent guarantees every natural stack code decodes to a finite list.
4. Modus ponens consumes the implication on top and its premise immediately
   below; generalization changes only the top. Every reached entry is a
   C222 theorem. The converse needs induction with an arbitrary preserved
   stack tail, not merely an empty stack. The report explicitly proves this
   stronger invariant, so sequentially executing both MP derivations is valid.
5. The inherited source theorem KEndpoint.c222_iff_zf_refutation depends on
   calculus upper/lower theorems, not a TM simulation hypothesis. Bridge.lean
   composes it with the constructible-choice equivalence to ZFC refutation.
   Its source module importing machine files does not make the theorem depend
   on machine-specific assumptions.
6. Every finite sequence admits the displayed beta coding: choose y divisible
   by all integers through the last index and larger than all entries. The
   moduli 1+(i+1)y are pairwise coprime; CRT supplies x. Conversely the bounded
   condition gives a finite valid path. The endpoints exclude length zero.

## Exact artifact checks

The independent checker authenticates all 12 local source files against both
SHA-256 and Git-blob SHA-1 in the pin manifest. It propagates affine expressions
through every literal DAG node, verifies all wire factors against the actual
DAG, verifies natural realizability (64 products of nonnegative affine forms,
20 squares), reconstructs all 85 residuals, and independently expands their
sum of squares. It checks 382 operation nodes and degree bound 1,048,802.
It also parses all 85 generated Lean residual rows and compares their literal
polynomials to the independently reconstructed residuals. Integer coefficients
are checked exactly. No modular test is used for these equalities.

## Static Lean/API review, not elaboration

Rep.equality has the expected integer-expression equality predicate; existsBlock
moves the Fin 89 block to natural witnesses. Rep.compose accepts the two graph
representations; boundedForall binds the Option.none coordinate below outside
coordinate 0. The current/next beta graphs use x=coordinate 1, y=coordinate 2,
and i/i+1 respectively. The endpoint graph uses indices 0 and t. Reindexing
all three outside inputs into Empty plus Fin 3 followed by existsBlock closes
these inputs. QuarticCompiler.compile accepts a closed Rep Empty, as intended.
The Fin.cases construction matches an existing idiom in the pinned remainder
source. No definite API or syntax defect was found in this static inspection.

This is not a Lean parser or typechecker result. In particular, successful
elaboration, definitional-equality inference and the final compiler output
still need testing in the full pinned repository with Lean installed. The
source copies are not a complete dependency closure. The compiler's Wset
and natural-domain conventions must be maintained when stating the eventual
global no-solutions theorem.
