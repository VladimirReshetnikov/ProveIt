# Literal adaptive graph and canonical converse at current2011 ports

Read-only proposal, 2026-10-26. The accepted scalar bootstrap, power recovery,
Mersenne and all31-coordinate restoration files remain unchanged. This note
proposes a narrow graph/source binding first, then a separate canonical
converse and actual-current existence equivalence. No new Lean source,
compiler invocation, incoming-code execution, or metric certification is
part of this planning checkpoint.

## 1. Exact graph and first bounded leaf

Use the literal 88-row graph
`candidates/free-j-polarized-positive/source/positive/p13_free_J.json`,
SHA `a6c378ffe706da6ccb17250c31183b0cbff7bdd2c21b85cf0fc393a73bd987b8`.
Its independent coordinates, in order, are

```
[J,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma].
```

The four fixed ports are `[beta,K,MC,MF_source]`; `MF_source` is already
shifted once. The graph's exact tail is `Fs*(Fa*(F0*F1))-1`, with
`F0=1+A0`, `F1=1+A1`. The complete prefix gives

```
q=beta*J+1; k=eta+zeta; E=X*Y; C=q-F-alpha;
c=k*Y+eta; a=E+Y; H=4*a+3; delta=a*a+H;
ell=E*(k*Y); U=Y*q*q;
Bt=(q*K+X)*C-q*F;
R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF_source)*J;
v=k-R-1;
Dstar=U*(X+a*c)+H*(U*gamma+q*E-v);
V=f*f*(c*T-R)-c; y=V+u; I=i*c*c;
A0=firstZ(q,ell,k,r,Y,Bt)^2-(q^3*(q-1))^2*(1+ell*(ell+k));
A1=Dstar^2-U^2*(1+delta*c*c);
Fs=1+I^2-delta*(f*f-1);
Fa=y*y-delta*(f*f-1)*(y*y-V*V).
```

The proposed `NativeAdaptiveGraph.lean` imports only
`NativeAdaptiveSourceRestoration` and `NativeAdaptiveUnitFactors`.
Define a commutative-ring `value (ports : Fin 4 → A) (x : Fin 13 → A)`
with the 88 explicit paid lets in the JSON's actual order, and a named
cut record for the quantities above. Bind the literal lets to these cuts
without replacing the graph by an unverified short formula. Ring-homomorphism
compatibility then supplies `polynomial` and its exact `eval_polynomial`.
Local ring identities bind each cut; a full expanded degree51 normalization
is unnecessary for the logical graph binding.

For arbitrary signed integer inputs, prove

```lean
value ports x = 0 ↔
  firstA0 q (X*k*Y^2) k r Y Bt = 0 ∧
  mainA1 q X Y k eta gamma (k-R-1) = 0 ∧
  NativeAdaptiveStrongIndex.strongFactor a c f i = 1 ∧
  NativeAdaptiveStrongIndex.auxiliaryFactor a c f T R u = 1
```

The cut names on the right are the actual fields computed from `ports,x`.
This uses `NativeAdaptiveUnitFactors.product_one_iff` with arguments
`q,firstZ,1+ell*(ell+k),U,a,c,Dstar,f,I,V,y`. The generic unit factors use
`a^2+4*a+3`, so the delta rewrite is an ordinary ring identity. Associativity
and commutativity put the graph's tail into that theorem's multiplication
order. No positivity, restored index, or factor-sign premise is needed for
this unit extraction.

Then export the all-positive source endpoint:

```lean
-- Proposed signature; x is the actual thirteen-coordinate assignment.
theorem positive_zero_source (ports : Fin 4 → ℤ)
    (hp : NativePellBootstrap.PortBox ports) {d : ℕ}
    (hd : 4 ≤ d) (hbeta : ports 0 = (2:ℤ)^d-1)
    (x : Fin 13 → ℤ) (hx : ∀ j, 0 < x j)
    (hz : value ports x = 0) :
    ∃ s : Fin 31 → ℕ, (∀ j, 0 < s j) ∧
      (∀ j, SplitCertificate59.sourceRows ports (fun k => (s k:ℤ)) j=0) ∧
      (s 0:ℤ)=x 0 ∧ (s 1:ℤ)=x 1 ∧ (s 2:ℤ)=x 2
```

Retain additional f/i/eta/zeta/X/V/y/rank bindings already returned by
`adaptive_positive_source` if economical. This is a real arbitrary-positive
zero→source theorem: its only classification input is the zero of this
literal graph. A canonical parent is not used in this direction.

Focused checks should cover all13 positions, all four unshifted/once-shifted
port positions, the exact final multiplication order, the universal signed
cut equivalence, and the positive-source wrapper. This first pair can freeze
before the larger native/current imports enter.

## 2. Canonical parent supplies the reverse witnesses

Proposed second leaf: `NativeAdaptiveCanonical`, importing the new graph
plus the accepted `NativeShiftedSourceAdapter`. The latter already imports
the ordinary-source/current endpoint and the needed canonical/source APIs.
Its generic construction takes a positive Fin15 parent `p` satisfying
`Carrier66.Canonical ports p` and the actual
`NativeSourceMask.Interface ports d MC MF`. No adaptive zero or adaptive
bootstrap conclusion is assumed.

Let `B=Carrier66.core ports p`, and retain the exact parent fields

```
J=p0, F=p1, alpha=p2, f=p4, T=p7,
s=p8, w=p9, tau=p10, eta=p11, zeta=p12,
y=p13, gammaOld=p14, zOld=p3.
```

The established `Carrier66Source.source_pos`, `canonical_rows`,
`sourceNat_cast`, `sourceNat_rows` and `nativeRank_eq` give one and the same
positive ordinary source. All subsequent source lemmas apply to that source,
not to an unrelated existential witness. In particular its main rank is
exactly `B.rank`, and `B.X=q*w`, `B.Y=q^3*s`.

The adaptive thirteen-vector is

```
[J,F,alpha,f,delta*p6,T,X,Y,rAdaptive,eta,zeta,
 y-V,gammaOld-w+t].
```

Here are the remaining existential choices and every nontrivial positivity
obligation.

1. `u=y-V>0`: source positivity gives `V>0` and `y^2-V^2>0`, while
   `p13=y>0`. Ordered integer arithmetic yields `y>V`.
   The ordinary multiplier is **delta*p6**, not p6; this is the literal
   `Carrier66Source.source` slot6 and is strictly positive.
2. `zOld>1`: use `NativeShiftedSourceAdapter.source_old_z_gt_one` with the
   actual source and Interface. It derives strictness from the spatial/source
   bound and transport. Define `b=q*(zOld-1)`, so `b>=q>=2` and the actual
   graph transport is `Bt=(q-1)*b`.
3. The canonical index condition gives
   `v=k-R-1=E*p5>0`. `NativePellFirstIndex.source_first_pair` supplies
   `n>=13`, `2*n=R+1`, and the exact same `k=2*yn_(2XY^2+1)(n)`.
   Apply the already accepted `NativeAdaptivePowerProjection.first_difference_four`
   after the explicit natural/integer casts to get `4*X*Y^2 | v`.
   Choose an integer `l` with `v=4*X*Y^2*l`; positivity gives `l>=1`.
4. Define **without division** `t=4*q^2*w*s*l`. Since X=q*w and Y=q^3*s,
   the exact identity `v=(q^2*Y)*t` follows by ring arithmetic.
   With q>=2 and w,s,l>=1, `t>w`; thus `gammaOld-w+t>0`.
5. The same canonical index identity already gives `k>E` because R,p5>0.
   Since X>=1 and Y=q^3*s>=s, `E>=s`, hence `k>s`. No extra Pell growth
   lemma is needed for this bound.
6. The positive first norm `tau^2=1+ell*(ell+k)` gives `tau>ell`.
   Put `W=(q-1)*k+1` and
   `rAdaptive=W*b+tau-ell-k-s`. Here W>=k+1 and b>=2, so
   `rAdaptive >= 2*(k+1)+1-k-s > 0`.

All other entries of the new vector are unchanged positive parent fields
or positive products. In particular no sign is assumed for an arbitrary
adaptive carrier root; the reverse map deliberately chooses the positive
canonical `tau`.

## 3. Four exact reverse cut identities

For these chosen witnesses the complete ledger is:

- `firstZ=M*tau`, where `M=q^3*(q-1)`, because
  `ell+k+rAdaptive=W*b+tau-s`, `Y=q^3*s`, and `Bt=(q-1)*b`.
  The canonical first norm therefore gives `A0=0`.
- `q*E=(q^2*Y)*w` and `v=(q^2*Y)*t` imply
  `Dstar=(q^2*Y)*(X+a*c+H*gammaOld)=(q^2*Y)*B.D`.
  The canonical main norm gives `A1=0`.
- `Carrier66Source.canonical_strong_error` gives
  `f^2-1=delta*p6^2*c^4`; hence
  `(delta*p6*c^2)^2=delta*(f^2-1)` and `Fs=1`.
- The parent's `B.S=delta*p6*c^2`, its exact
  `V=f^2*(c*T-R)-c`, and its `B.U=1` give
  `Fa=y^2-delta*(f^2-1)*(y^2-V^2)=1`.

The universal graph cut equivalence yields zero. This construction can
retain J,F,alpha,f,T,X,Y,eta,zeta and the ordinate `V+u=y`. It is an
existence map, not a pointwise inverse preserving arbitrary private source
coordinates. No historical cofinality, compact44 coefficient, supplied
adaptive rank/power fact, or new Pell-seed existence theorem enters.

## 4. Exact current equivalence and interface distinction

The source→Carrier65 direction composes `positive_zero_source` with
`NativeOrdinarySourceConstruction.source_constructs_carrier65`, under
Interface and `MC%4=2`. The reverse starts from
`Carrier66.positive_zero_restores_canonical`, then the construction above.
**Its generic statement also needs `Carrier65Witness.PortBounds ports`.**
Interface/PortBox alone does not state beta>=31, K>0 and all the strict
mask bounds needed by that Carrier65 theorem. These must not be silently
inferred from the weaker width>=4 box.

At the actual current ports, all premises are existing theorems:
`CurrentWindowCarry2011.interface`, `CurrentMasks2011.lowPort_four`,
`CurrentCarrierArithmetic2011.portBounds _ K_pos`, and width94517.
The once-shifted tuple is exactly
`CurrentMasks2011.ports (CurrentKernel2011.K:ℤ)`.
A current polynomial is simply the new polynomial at that tuple. Its target
endpoint is the explicit external Lean statement

```
(∃ x : Fin 13 → ℤ, (∀ j, 0<x j) ∧ eval x currentPolynomial=0)
  ↔ ¬ DiophantineConsistency.ConZFC,
```

and its negation version, by the accepted `CurrentPositiveZero2011` theorem.
No Bridge placeholder, internal HA/ZFC proof, or arbitrary-source-axiom
translation is substituted. The same complete47313-byte coefficient tuple
is used on both sides. The historical 88-operation/degree51 claim is not a
new current metric certificate: a separate full graph/ports/liveness/leader
audit remains necessary before publishing that triple at current ports.

## 5. Cache, reads and staged scope

The adjacent planning audit authenticates **35 custom source/object pairs,
22 explicit external names and66 companions**, with158 source/artifact
observations, for the proposed first graph leaf only. It reuses the accepted
33-module Restoration parent plus the independently accepted Restoration main
and UnitFactors main. Its source import DAG is checked exactly, including
implicit Init. No Foundation or dependency build is needed for this first
pair. The root Restoration provider is
`/tmp/native-adaptive-source-restoration-root-8hhrwabt/lib`; the UnitFactors
independent provider is
`/tmp/native-adaptive-unit-factors-controller-peer-0tr530p5/lib`.

For the later imports, module-name inventory only gives375 existing modules
with the ordinary endpoint, or378 with the accepted shifted-source adapter.
The latter includes the three accepted legacy/adapter mains. New Graph and
Canonical leaves are not counted. Before authorizing their build, the exact
selected wider source/object pins and external boundary names must be
reauthenticated; this note does not claim that wider authentication has run.
No cache or source is copied by the planning script.

I reread the entire inert88-row graph and ordinary free-J proof, the unit
factor theorem, and the relevant current canonical/source/restoration,
first-index, first-difference and strict-z definitions/proofs. The new audit
pins those actual source bytes. This is not a fresh review of every unrelated
theorem in the future larger native closure.

Recommended next authorized scope is **NativeAdaptiveGraph + Checks only**,
freezing the all-positive graph→source direction first. Then approve the
canonical/current pair after its exact union authentication. Both use two
fresh private regular outputs, Lean4.32 `-M6000 -j1 -DElab.async=false`,
full source/driver read,512MiB reserve and retained failed attempts. No
accepted source, shared docs, display, or Git change is proposed.
