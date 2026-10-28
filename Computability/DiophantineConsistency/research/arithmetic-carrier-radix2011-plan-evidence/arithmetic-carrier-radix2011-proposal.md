# Concrete maintained zero to power and radix

Read-only proposal, 27 October 2026. No new Lean source, overlay,
prerequisite refresh or compiler has been created for this proposal.
CarrierSoundness and RadixAlignment are now independently accepted by ROOT.
The accompanying read-only inventory binds their accepted providers and the
accepted PowerRecovery provider; no new compiler is part of this audit.

## Smallest complete client

Proposed new pair: `ArithmeticCarrierRadix2011` and focused Checks, importing
only `ArithmeticCarrierSoundness2011`, `ArithmeticPellPowerRecovery` and
`ArithmeticRadixAlignment`. The substantive endpoint starts from the actual
maintained split-natural equality and positivity of the same Fin14 tuple.
No port bound, additive equation, index identity, source validity, power,
radix or exponent-divisibility premise is supplied by its caller.

The indices are elements of an arbitrary internal IΣ1 arithmetic model.
Let the actual constants be

```
beta = (CurrentMasks2011.beta : V)
K = (CurrentKernel2011.K : V)
MC = (CurrentMasks2011.lowPort : V)
MF = ((CurrentMasks2011.highPort + CurrentMasks2011.beta : Nat) : V)
d = (CurrentMasks2011.width : V) = 94517
```

For the input `v : Fin 14 -> V`, retain

```
q = beta * v 0 + 1
X = v 8 * q
Y = v 7 * q^3
R = ((q-1)*(q-v 1)+v 2)*(q^2-1)+(MC+q*MF)*v 0.
```

The first public theorem `current_power` should have exactly these inputs:

```
(v : Fin 14 -> V) (hv : forall j, 0 < v j)
(hz : expression.splitNatural.1.evalSemiring v =
      expression.splitNatural.2.evalSemiring v)
```

and conclude `X = Exp.exp R`, `Exponential R X` and `Exp.exp R < Y`.
The second public theorem `current_radix` has the same inputs and concludes
those power facts together with

```
exists L : V, 0 < L and
  q = Exp.exp (d*L) and
  d*L <= R and
  v 8 = Exp.exp (R-d*L) and
  Exponential (d*L) q and
  Exponential (R-d*L) (v 8).
```

The new block count is deliberately called **L**. It is not the existing
carrier coordinate `v 9`, which occurs in the first-norm quotient. No
identity between those two values is asserted. Retain `d*L <= R`, not an
unjustified strict inequality: the factor theorem permits the boundary
`v 8=1`, where the remaining exponent is zero.

A companion `current_natural_radix` takes only the actual
`naturalExpression.splitNatural` equality and concludes the same statement
at `fun j => v j+1`. It reuses the accepted structural single-shift binding;
it does not redefine or iterate the positive shift. The fourth mask port
also remains `highPort+beta` exactly once.

## Exact composition and representation

`ArithmeticCarrierSoundness2011.current_equations v hv hz` derives the
transport and all four norms from this same literal zero.
`current_bounds` proves the actual `beta>=15`, `MC<beta` and `MF<2*beta`.
The literal coordinate order is
`J,F,alpha,z,f,i,T,s,w,N,eta,zeta,y,gamma = v 0,...,v 13`.
Apply `ArithmeticPellPowerRecovery.maintained_power` in that order.
Its `delta a` is exactly `(a+1)*(a+3)`, and its `absdiff A B` is
`(A-B)+(B-A)`. Thus the accepted five-equation package matches the power
client without a signed-coordinate assumption or a new norm conversion.
The previously derived scalar windows and first/main index identities
remain inside that accepted theorem; the client does not resupply them.

A private generic positive-tuple helper may consume `Equations` internally
to share the positive and naturally shifted proofs. The public concrete
endpoints must still expose only the actual zero and the stated domain.
No abstract normalized-product hypothesis is an acceptable replacement.

The exact fixed-width identity is proved without expanding the large
coefficient. First establish the generic standard-parameter cast identity

```
Exp.exp (n : V) = (2 : V)^n                  (n : Nat)
```

by ordinary external induction on the finite syntax parameter `n`, using
internal `exp_zero` and `exp_succ`. This is a natural-cast identity only;
all subsequent arbitrary internal exponents remain governed by the
represented exponential. Equivalently the existing `nat_cast_exp` may be
used with a separately established Nat exponential identity.

Use `CurrentMaskData2011`'s exact declarations
`radix=2^47`, `width=47*2011`, `beta=radix^2011-1`, together with generic
`Nat.sub_add_cancel`, cast addition/powers and `pow_mul`, to derive

```
(beta : V)+1 = Exp.exp (CurrentMasks2011.width : V).
```

Then justified subtraction gives
`(beta : V)=Exp.exp (CurrentMasks2011.width : V)-1`.
The finite width equality `47*2011=94517` and `2<=width` are small natural
arithmetic checks, cast into V. Keep the generic equalities opaque when
specializing, so the kernel never normalizes `2^94517` or its decimal
representation. No wide `CurrentMasks2011` theorem import is needed.

The accepted generic theorem has exact signature

```
ArithmeticRadixAlignment.factor_alignment (d J R w : V)
  (hd : 2<=d) (hJ : 0<J)
  (he : Exp.exp R = w*((Exp.exp d-1)*J+1)) :
  0<w and exists L, 0<L and
    (Exp.exp d-1)*J+1=Exp.exp(d*L) and
    d*L<=R and w=Exp.exp(R-d*L).
```

Supply the factorization by reversing the newly derived `X=Exp.exp R`
and rewriting the proven beta identity. Its `J>0` is `hv 0` and its width
bound is the finite actual-width fact. The two Exponential conclusions
follow from the exact exponential equalities and `exponential_exp`.
They are actual represented-graph facts, not a new formula complexity claim.
The generic theorem derives positivity and exponent alignment; the client
must not replace it with supplied radix or repunit witnesses.

I fully read the current 302-line PowerRecovery, the complete Carrier pair,
the exact CurrentMaskData2011 and CurrentEquationSyntax2011 declarations,
and the final RadixAlignment pair. The radix proof's nonnegative block
quotient, modulus-equality boundary exclusion and positive residual-factor
cancellation have no source-level mathematical finding. That challenge was
sent to its author. I subsequently independently replayed both radix leaves;
ROOT accepted that evidence before this inventory was frozen.

A separate scoped read-only challenge by `radix_client_challenge` checked
the direct five-equation binding, opaque finite cast route, distinction of L
from v9, and the positive/natural same-zero endpoints. It found no missing
interface. In particular the natural client must use public
`current_natural_equations` and the shared internal Equations helper, since
the structural shift lemma is private. That challenge did not compile or
authenticate providers and is not acceptance of an implemented client.

## Proposed provider union and launch boundary

The frozen Carrier inventory contains 135 custom modules, including95
Foundation modules,420 custom artifacts and50 external boundary names with
150 total boundary artifacts(50 primaries+100 companions),570 providers.
The entire generic RadixAlignment parent inventory(90 Foundation modules,
360 custom artifacts,38 boundary names) is already inside that DAG; there are no new boundary names. The union
auditor checks exact source, header and complete artifact-hash agreement
for every overlapping module and every overlapping boundary.

Add only the main objects of CarrierSoundness, accepted PowerRecovery and
accepted RadixAlignment. The resulting requested profile is138 custom,
95 Foundation,423 custom artifacts,50 boundaries/150 boundary artifacts,
573 actual first providers,zero prerequisite refresh. Checks objects are
not imported. The three proposed direct imports will determine the exact
reachable DAG, rather than importing a broad umbrella or unused provider.

PowerRecovery's accepted provider is
`/tmp/arithmetic-pell-power-recovery-root-r2hxcchd/lib`;
ROOT replay packet SHA is
`8c8a97aaa083bd02234c62c1fbeb4fe56092fd31a8cd02b6618706c6a5863f48`.
CarrierSoundness's accepted ROOT provider is
`/tmp/arithmetic-carrier-soundness2011-root-d5casc3p/lib`;
its ROOT packet is
`c166d8bf5c09c1faf80bc9c214608b04d01707ac9d1a0ae9430465760bb4cdb7`.
RadixAlignment's accepted peer provider is
`/tmp/arithmetic-radix-alignment-peer-81rmdzv1/lib`;
its peer packet is
`d2ecc9d7e9890a16cd5b72fe99aba6433f49a6179ca7db7de8830816dc93058e`.
The explicit ROOT radix acceptance audit is
`75246f55f6187a9260939f5e0073639d15c8367519b3077b127f39996829edf3`.
No provisional provider or prior failed object is selected.

Before any new compiler, freeze the complete source/header DAG, all custom
and external source/object/artifact pins, exact first providers and package
search order, including implicit Init, with inherited provenance evidence.
Recheck all three accepted packets and explicit radix ROOT acceptance. Request ROOT's review of that exact inventory and this interface.
Only the two new leaf commands would then be proposed: pinned Lean4.32,
`-M6000 -j1 -DElab.async=false`,one thread,512MiB reserve,fresh regular
objects,both input snapshots and complete driver read before execution,
all attempts preserved. No overlay/compiler is authorized by this proposal.

## Explicit remaining obligations

This scalar checkpoint does not internalize population counts, fixed-mask
words, carry recurrences, physical selector decoding or tableau soundness.
An external finite `ZMod N` word cannot be treated as an internally finite
word at a nonstandard L. The converse still requires internally encoded
halting tableaux, scalar packing/rank calibration and simultaneous outer
and auxiliary Pell witnesses. Actual polynomial/HA equivalence and final
proof interpretation remain separate; no metric, display, canonical-source
or cofinality promotion follows from these scalar identities alone.
