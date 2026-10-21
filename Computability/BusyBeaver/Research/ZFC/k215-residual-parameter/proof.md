# Additive AX with a retained opposite residual and parameter-free MP

This is an ordinary proof for a revised source command language, followed by a literal source correspondence argument. It does not certify any allocated table or its blank initialization. The accepted215 source remains unchanged. The current best source is206 DAG, with4,738 primitive leaves and6,158 guarded cases; the conservative context allocator costs240 states. No214-state candidate is claimed.

Attribution: Source164 (`K215_Construction_and_Research_2026-10-21`) supplies the original absolute-A residual compiler, opposite-residual observation, safe stack interface and all-natural comparison analysis. `/root` supplied the additive-A extension below, including the preserving-zero block, parameter setter and necessary three-half RESET. `/root/review_upstream_reflection` independently checked these blocks, rebound the source edits to accepted command order210, implemented the finite interface/source tests and bounded reassociation/pricing. The inherited dominated-rho8 calibration is Source149's3,728-node forward certificate; Source164's new projection result is not needed here.

## 1. Exact revised interpreter

Let `I(a,b)=4P(a,b)`, `Q_i(a)=4P(i,a)+2`, and falsity `F=1`, with the accepted Cantor pairing `P`. Write `[x]S=P(x,S)`. In particular `P(0,0)=0`; arguments below use literal pairing identities and never assume that pushing zero on the empty stack produces a distinct code.

A state is `(t,S,d,h)`: current theorem, theorem stack, numeric parameter and cached theorem. Let `N` denote NIP and `D` denote DROP. They retain their original effects:

- `D(t,S,d,h)=(h,[t]S,d,h)`.
- `N(t,[x]S,d,h)` halts if `h=1`; otherwise it returns `(t,S,d,x)`. The cache on entry is tested, not the value just popped.
- Parameter-free `MP` succeeds exactly when `I(t,d)=h`, returning `(d,[0]S,d,0)`; otherwise it returns `(0,S,d,0)`. Its old numeric read is removed. Its success zero is retained.

For `AX(c,y,x)`, set `A=d+x`, `B=h+y`, `U=d`, using incoming d,h. Let `g=0` when `c=A` or `c=B`, and otherwise let g be the exact gated native bundle at `(A,B,c)`. The new AX returns

`(g,[rho1,...,rho8,Q_U(h),t]S, max(c−A−1,0),0)`.

The order and arguments of the eight native rows are exactly inherited; rho8 uses `(A,B,c,U)`. There are ten stack entries: eight rows, one GEN value and old t. All newly emitted row/GEN/bundle values differ from1 by their literal constructor tags (zero is also safe). In particular this statement does not require incoming t or h to be well formed or derivable. Since `U≤A`, the emitted rho8 is dominated, exactly as in the accepted source.

The only hardware-independent changes are that the final AX comparison returns the opposite scratch residual in d and MP reads no input field. A remains additive. The new raw command order is the accepted210 order: NIP0, DROP1, MP2, AX(c+3,y,x).

## 2. RESET for arbitrary incoming current and cache

Let `H = AX(0,0,0);N^10`. Then `RESET=H;H;H` returns `(0,S,0,0)` for every `(t,S,d,h)`, without an early halt.

First, AX has A=d and c=0, so its residual is0, although its gate g1 may be nonzero. Its cache is reset to0 before the ten NIPs. The first nine popped entries are newly emitted safe constructor values. The tenth NIP pops old t into the cache only on exit, so t is never tested during this half. This first half finishes `(g1,S,0,t)`.

The second AX has A=c=0 and hence gate0 and residual0, regardless of its incoming cache t. It overwrites that cache before any NIP. Ten safe pops finish `(0,S,0,g1)`.

The third AX again has A=c=0. Its old current is now0; after ten pops the result is `(0,S,0,0)`. No old stack entry is popped. The two-half RESET of the absolute-A proposal would leave g1 cached here, so three halves are necessary for this particular proof.

## 3. A zero setter preserving the current theorem

Assume only that incoming cache is0. Define

`Z=AX(0,0,0);N^10;D;N`.

Because B=c=0, the gate is0 even when A=d is nonzero. The opposite residual is0. After AX and ten pops the state is `(0,S,0,t)`. DROP returns `(t,[0]S,0,t)`. The final NIP halts exactly if t=1; otherwise it pops the newly pushed zero and returns `(t,S,0,0)`.

Thus Z preserves both current value and every old stack entry, while setting d to0. It works for every incoming d. It does not assume t is a theorem or that the old stack is safe; it merely allows the explicit early-halt alternative when t=1.

## 4. Arbitrary parameter setter preserving current and stack

For v∈N define

`SET(v)=Z;AX(v+1,v+1,0);N^10;D;N`.

If Z halts, t=1. Otherwise Z has left `(t,S,0,0)`. The second AX then has A=0 and B=c=v+1, so gate0 and residual `max((v+1)−0−1,0)=v`. Its ten pops, DROP and final NIP perform the same safe restoration as in Z. Consequently SET(v) halts exactly when t=1, and otherwise returns `(t,S,v,0)`.

This is the reason an absolute-A read is unnecessary. SET first establishes d=0 using Z. It does not attempt to force the second AX's A=0 by assuming an incoming d value.

## 5. Selection and strong compiler contract

Suppose AX starts with current0 and returns `(g,[r1,...,r9,0]S,d',0)`, all rj and g being different from1. For1≤j≤9,

`N^j;D;N^(11−j)`

returns `(rj,S,d',0)`. After the first j pops DROP pushes g; the following prefix consists of g, the9−j unselected rows and old current0, exactly11−j entries. Every tested cache is safe. This restores the exact encoded old stack, including zero aliases.

A compiler block for X is a finite block that, on every numerical `(t,S,d,h)`, either halts or returns `(X,S,d',0)` for some d'. It must preserve S exactly; it need not clear d. We construct such blocks for the dominated native calculus.

Truth: use RESET.

Dominated row j at `(A,B,c,U)` with `U≤A`:

`RESET;SET(U);AX(c,B,A−U);N^j;D;N^(11−j)`.

After RESET and SET, current/cache are0 and d=U. AX therefore reads exactly A=U+(A−U), B=B, U=U. It emits the requested row. Selection restores the original stack. Rows1–7 ignore U, so choose U=0 when compiling them.

Gated bundle at `(A,B,c)`, c distinct from A,B:

`RESET;AX(c,B,A);N^10`.

RESET sets d=0, so AX uses the desired A and B. Its gate is the requested literal bundle. Ten safe pops remove only the newly pushed prefix and old current0, leaving `(bundle,S,d',0)`.

GEN: if p compiles X, use

`p;SET(i);D;N;AX(0,0,0);N^9;D;N^2`.

Unless p or SET has halted, they leave `(X,S,i,0)`. DROP/NIP gives `(0,S,i,X)`. AX now has **A=i**, B=X, U=i and c=0; A need not be zero. Its ninth row remains exactly `Q_i(X)`, every new value and its gate are safe, and its opposite residual is0. Selection at j=9 returns `(Q_i(X),S,0,0)`. The proof uses row order and tag safety, not a false gate-zero assertion.

MP: if pA and pI compile A and I(A,B), use

`pA;D;pI;SET(B);N;D;N;MP;N`.

After the two premise blocks and SET, unless they halt, the state is `(I(A,B),[A]S,B,0)`. The premise A remains protected beneath the blocks' temporary prefixes. The next N,D,N give `(A,S,B,I(A,B))`, or halt when A=1. Parameter-free MP succeeds, producing `(B,[0]S,B,0)`. The last N removes the success zero and returns `(B,S,B,0)`.

This is finite structural induction on a dominated native derivation. No object-language formula-substitution or variable-renaming rule is introduced.

## 6. From unrestricted derivations to source halting, and soundness

Source149's ordinary all-natural certificate replaces every unrestricted rho8 instance by a finite derivation from truth and dominated rho8, using only its explicitly checked forward instantiations and MP. All other native rows, GEN and the exact gated bundle are unchanged. Thus an unrestricted native proof can first be translated into a dominated proof, then compiled by section5. This is the inherited universal certificate, not the new restricted projector countermodel or a finite empirical agreement.

For a proof of falsity, append `D;N;N` to its compiler. If the compiler has not already halted, it returns `(1,S,d',0)`. DROP pushes1 and makes current0; the first NIP loads that1 without testing it; the next NIP halts. The original stack is never read. The block therefore halts from every numerical work state, while the soundness argument below is used only from theorem-safe execution states.

For soundness, t,h and every stack element are native derivable. DROP/NIP only rearrange them; NIP can halt only on a derived1. Successful MP derives d from its exact premises; failure returns truth0. AX emits native rows because U≤A, the GEN value from derived h, and either truth0 or the exact allowed bundle. Its numeric residual has no theorem invariant. The accepted safe source seed has truth current/cache/stack; arbitrary unsafe theorem lists are not treated as sound seeds.

The accepted outer scheduler remains unchanged. The revised wire format removes MP's extra field and uses the actual210 tags. Packing a command c before a continuation cursor n uses `1+P(tag,n)` for NIP/DROP/MP and `1+P(c+3,P(y,P(x,n)))` for AX. Unpacking decreases the cursor and reproduces exactly these fields, including P(0,0). A finite compiler block therefore has a finite code.

The cofinal shell `AX(Y,0,0);RESET;compiled-refutation` has codes unbounded with Y. The dummy AX returns a numerical work state, and RESET/the compiled block are valid on every such state. If the fixed tail has cursor z, its initial raw candidate code is `P(Y+3,P(0,P(0,z)))`, which is at least Y and strictly increases with Y. Thus the accepted increasing enumeration eventually reaches a halting compiled block whenever a refutation exists. Conversely a halt from the safe seed yields a native refutation. This composes with the inherited ordinary native-calculus/ZFC calibration. It is a source-program result; the physical table and exact blank tape remain separate obligations.

## 7. Literal accepted215 source correspondence

The seed source is SHA17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba. The additive-X variant changes only two intervals in that exact210-order source:

- `[4578,4590)` is the second AX comparison, entered with H=A, scratch X=c, D=0. The paired decrement loop is unchanged. In its unequal cleanup, replace the open `(CD6,CC2)` by the closed transfer `(CD6,(CI4,CC2))`.
- Remove the closed14-leaf numeric read `[4591,4605)` at the entry to the MP body. This is the actual210-order location, not the old012-order offset4645.

If A=c, both counters become zero, the equality branch clears the bundle, and D stays zero. If A>c, the paired loop consumes one additional H unit, then unequal cleanup clears the remaining H; X=0 so the new transfer adds nothing. If c>A, the paired loop consumes one additional X unit; H=0 and X=c−A−1, which the new transfer adds into initially zero D. The transfer clears X and returns to the same skip-equality branch. Thus in all natural cases the gate is unchanged, H=X=0 and D=max(c−A−1,0). All other counters are unchanged.

The original last U copy remains literal, so GEN and rho8 retain old U and the later input read remains additive A=U+x. The old MP read was a closed additive transfer of the next input field to D; deleting it removes that field and leaves the MP equality/success/failure body unchanged. All source instructions outside the two edited intervals have exactly their previous opcode and guarded target under the explicit splice ordinal map. All external entries into an edited macro are at its first instruction; none jumps into its interior.

The raw source has207 DAG nodes,4,738 leaves, maximum depth47 and zero-run6. `compose.py` checks both full CFG resolvers, every retained instruction/edge and finite isolated gate/load probes. Ordinary loop reasoning above supplies the all-natural claim; the finite probes alone do not.

A deterministic beam of closed halt-free reassociations, freezing the entire original `[398,4572)` partial-selector/contextual172 subtree, saved16 sources of206 DAG. Every saved source preserves the entire ordered primitive word and both guarded CFGs of the raw additive-X source. Closed reassociation preserves finite control effects and divergence; it does not assume a closed factor terminates. The search explored1,204 new roots in five rounds with beam24, not an exhaustive grammar minimum.

## 8. Evidence and current limits

The additional own interface checker passes5,915 finite cases using three safe abstract row instantiations; explicit HOLE instructions stand only for compiler induction hypotheses. It tests RESET3, Z, SET, dominated row/bundle selection, GEN with A=i, MP, terminal detection, protected stack tails including falsity, and order210 wire decoding. It does not execute the enormous native AX generator or substitute for this universal proof.

The conservative allocator's exact215 identity control reproduces all430 rows byte-for-byte. The best206 source passes all4,737 internal prefixes and4,738 literal entries, with explicit108 suffix conditions, but costs240 states in that keep-old-rows policy. That is a price for this allocator, not a physical lower bound. Opening separately ran one bounded role-pool allocation: its accepted215 identity was exact, but the206 source was infeasible under the fixed injective policy (27 new roles,22 eligible states). These agent-authored records are preserved separately; no solver rerun or independent solver audit is claimed here. No full symbolic runtime or blank replay was run for any residual variant, and no smaller accepted machine follows from the source proof.
