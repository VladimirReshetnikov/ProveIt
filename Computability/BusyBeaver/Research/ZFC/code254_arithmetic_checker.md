# A concrete arithmetic representation of the exact C254 checker

2026-10-16. The [exact Cantor adapter](arithmetic_cantor.md) is now implemented
and checked in arbitrary IOpen models, with all-input identification of the
actual `Code254.P` and `Cantor.ofNat` operations. A represented history table
is the next step toward computing our existing
`Code254Proof.check` without constructing or coding the `RawProof` datatype.
The table's recursion is already supported by the pinned Foundation library.
The construction plan below is retained; pairing and projection graphs are now
implemented, while the full evaluator and internal PA proof remain open.
The later [constructor component](arithmetic_code254.md) implements fixed
bounded graphs for all four base4 constructors and the rho1/tag3 payload
branch, including exact all-natural compatibility. The full row selector,
remaining branches and history graph are still open.
The [fixed-template extension](arithmetic_templates254.md) now also implements
rho2–8, the C and G components, and the full bundle, via a uniform finite-circuit
graph compiler. Thus all eleven positive fixed-template graphs are checked.
Their guarded row outputs, complete tag dispatch and history remain open.

The Foundation gitlink is `32e1a0956a8622fad067328ca1959729a7634428`.
The initial read-only plan recovered its source from the Git object database.
The later scoped adapter check uses the existing populated dependency checkout
and cached Foundation/Mathlib objects, without rebuilding those dependencies.

## Preserve the exact literal pairing

Foundation's arithmetic `pair` is

```text
if a<b then b*b+a else a*a+a+b.
```

See its `Foundation/FirstOrder/Arithmetic/IOpen/Basic.lean:511,534`.
Consequently its `pairDef`, `pi₁Def` and `pi₂Def` are **not** the pairing and
projections used by `Code254Proof.quote`. They can still encode the auxiliary
history sequence; they must not decode our literal proof payloads.

For the literal dual Cantor pair use the fixed bounded arithmetic graph

```text
CPair(p,a,b) : 2*p = (a+b)*(a+b+1) + 2*b.
```

The intended forward operation is
`((a+b)*(a+b+1))/2+b`. Division already has a total Δ0 graph
`divDef`/`div_defined` at `IOpen/Basic.lean:109,112`.
The remaining exact lemmas are elementary arithmetic, not an unbounded search:

* Successive products are even, by induction on their argument. This identifies
  the division expression with `CPair`.
* Every `p` has `a,b≤p` with `CPair(p,a,b)`. Induct on **internal** `p`, using
  the bounded property `∃a≤p ∃b≤p CPair(p,a,b)`. From `(a,b)` move to
  `(b+1,0)` when `a=0`, and to `(a−1,b+1)` otherwise. The polynomial identity
  gives the next value `p+1`, and both new components are at most `p+1`.
* The pair is injective. If `s=a+b<t=a'+b'`, then
  `2p≤s(s+3)<(s+1)(s+2)≤t(t+1)≤2p`, a contradiction. Thus the sums agree;
  equality of the polynomial values gives `b=b'` and then `a=a'`.

This supplies unique bounded projection graphs, for example

```text
CFirst(a,p) : a≤p ∧ ∃b≤p CPair(p,a,b)
CSecond(b,p): b≤p ∧ ∃a≤p CPair(p,a,b).
```

They can use exactly the `DefinedFunction` packaging pattern of Foundation's
`pi₁Def`/`pi₁_defined` (`IOpen/Basic.lean:599` onward), with the different
polynomial graph. Include the component bounds and both inverse identities.
The standard-model adapter must then identify these operations with the actual
`Code254.P`/`Cantor.ofNat`; changing to `Nat.pair` or Foundation's pair is not
that adapter. No such arbitrary-model Cantor package was found in the local
clients inspected here.

## A numeric row function for all twelve rules

Let `E(c)` be0 for an invalid proof code, and `1+n` for a valid proof of
formula code `n`. The successor is essential: a valid proof of truth0 has
value1, whereas invalid data has value0.

For `c>0`, put `tag=(c−1)%12`, `payload=(c−1)/12`, and decode **Cantor** fields

```text
(a,t) = unP(payload); (b,d) = unP(t); (e,f) = unP(d).
```

The arithmetic operations `%12` and `/12` are already represented:
`rem_defined` is at `IOpen/Basic.lean:270`. Given a history sequence `S`, use
`v(j)=znth(S,j)` and compute the following fixed finite case distinction.

| Tag | Output value; all failed conditions give0 |
|---:|---|
| 0 | 1 iff `payload=0` |
| 1 | `a+1` iff `b<c`, `d<c`, `v(b)>0`, `v(d)>0`, and `v(d)−1 = wim(v(b)−1,a)` |
| 2 | `wal(a,v(t)−1)+1` iff `t<c` and `v(t)>0` |
| 3 | `rho1(a,t)+1` |
| 4 | `rho2(a,b,d)+1` |
| 5 | `rho3(a,b,d)+1` |
| 6 | `rho4(a,b,d)+1` |
| 7 | `rho5(a,b,d)+1` |
| 8 | `rho6(a,t)+1` |
| 9 | `rho7(a,b,d)+1` |
| 10 | `rho8(a,b,e,f)+1` |
| 11 | `bundle(a,b,d)+1` iff `d≠a` and `d≠b` |

Code0 is invalid. Here `wim`, `wal`, every `rho`, and `bundle` mean the exact
fixed arithmetic expressions from `Code254.lean`, with `F=1`, all four tags,
native equality and both freshness tests. Each is a finite composition of
Cantor pairing, addition and multiplication. There is no theory-membership
oracle, arbitrary matrix search, standard-code condition or weakened MP.

The explicit child guards are harmless in the standard model: each child is
at most `payload<c`. They make the history dependency visibly acyclic, even
before using the projection bounds in later correctness proofs.

This numeric `row(S,c)` is total even for an invalid sequence code `S`:
Foundation's `znth` returns0 for an invalid sequence or out-of-range index.
The fixed row formula is obtained by composing represented functions and the
twelve guarded branches. The missing Cantor adapter, rather than a new generic
recursion theorem, is what presently prevents supplying that literal formula.

## One represented iteration supplies the whole checker

Use a parameter-free `PR.Blueprint 0` and the following construction:

```text
zero()             = Seq[0]
succ((),k,history)  = seqCons(history,row(history,k+1))
history(c)         = construction.result() c
value(c)           = znth(history(c),c)
Check254(c,n)      ⇔ value(c)=n+1.
```

At stage `k`, history has length `k+1`, storing values for codes0 through `k`.
The successor appends code `k+1`; every requested child is already present.
The existing fixed graph and totality APIs are precise:

* `HFS/Seq.lean:124,140`: total `znth`, its Δ0 graph and its out-of-range0
  convention; `:115,205`: `seqCons` and its Δ0 graph.
* `HFS/PRF.lean:18,37`: fixed `Blueprint` formulas and `Construction` with
  `zero_defined`/`succ_defined`; these are the two concrete graph obligations.
* `:138,154`: internally coded computation sequences and unique result exist
  at **every model element**, using actual Σ1 induction.
* `:171,189,194`: result recurrence, one fixed Σ1 result graph, and its Δ1
  form. No external recursion on the possibly nonstandard index is used.

The sequence direction is **append**, despite the name: its literal definition
is `seqCons(s,x)=insert ⟪lh(s),x⟫ s` (`Seq.lean:115`). For `Seq(s)`,
`Seq.lh_seqCons` (`:174`) gives length `lh(s)+1`. Combining
`Seq.mem_seqCons` (`:169`) with `Seq.znth_eq_of_mem` (`:128`) gives
`znth(seqCons(s,x),lh(s))=x`; `Seq.mem_seqCons_iff_of_lt` (`:187`) preserves
each old lookup below `lh(s)`. No old indices shift.

The invalid-sequence default is also unconditional: `znth_existsUnique`
(`Seq.lean:119`) explicitly requires
`¬(Seq(s) ∧ i<lh(s)) → x=0`. Its public consequence `znth_prop_not` (`:131`)
has premise `¬Seq(s) ∨ lh(s)≤i` and conclusion `znth(s,i)=0`. Thus an invalid
sequence gives0 at every index, with no `Seq(s)` assumption.

The local implementation pattern is
`Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/DynamicTruthOrbit.lean:127`:
it supplies literal zero/successor formulas and proves their graph equations,
then invokes `construction.result`. Here the zero formula is just the graph
of the singleton sequence `[0]`, and the successor graph composes `row` with
`seqCons`. Its source has no large quotation constants or typed-proof payload.

Define the acceptance formula by existentially exposing `history(c)` through
the fixed result graph, then testing its `c`-th value against `n+1`. This is
Σ1; total unique evaluation also gives the complementary/Δ1 presentation.
A separate Boolean graph can return1 on acceptance and0 otherwise.

The PA-totality proof target is concrete: prove in every model of `IΣ1` that
`history(c)` exists and has the stated recurrence, then that every `c,n` has
one Boolean result. The represented-iterator totality theorem already handles
nonstandard `c`. Arithmetic completeness can produce the actual PA derivation
of that **same fixed sentence**, following the existing call in
`UniformInternalProvability.lean:157`. A model-dependent choice of unrelated
graph formulas would not suffice; the blueprint here is fixed once and for all.

## Exact next proof targets

The Cantor arithmetic package with fixed Δ0 projection graphs and its
standard-model compatibility lemma is now checked, as are the constructors
and all positive fixed axiom templates. Define the complete twelve-case row
graph, including rejection and both gates, and one history blueprint.
These are independent of Native/ZF/Choice
interpretations and do not require rebuilding their proof-code translations.

The external checker-equivalence target is

```text
∀c n : Nat, Check254_ℕ(c,n) ↔ Code254Proof.check c n = true.
```

Prove it by strong induction on the natural proof code: the two recursive
fields are smaller, and the numeric value records exactly successful parsing,
validity and conclusion. The existing `c254_iff_checked` then gives the usual
external proof-existence equivalence. This comparison covers **all natural
inputs**, including invalid MP nodes, missing children and colliding gates;
quotation roundtrips alone are insufficient.

The arbitrary-model totality theorem is a distinct target. Neither it nor the
standard comparison proves the later PA-internal native/ZF/ZFC proof
translations or machine-trace translations. The construction above identifies
a small concrete first step, not those further endpoints.

## Constructor certificates as an alternative representation

[Source50](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md#batch157-canonical-term-certificates-for-the-full-calculus)
proves ordinary all-input equivalence between the legacy checker and local
quoted certificates with forward polynomial equations. Its separate ground-term
checker removes numeric literal/quotation arithmetic altogether, while retaining
all twelve rules, native equality, both bundle gates and fixed falsity. Only
`B0(Z,Z)` is normalized to Z. The delivered arena verifies unique constructor
keys before treating identifier inequality as numeric inequality.

These are alternatives to the already checked dense history, not corrections
to its all-input equivalence theorem. The new weighted quotation and short-fuel
bounds, normal-form bijection and certificate equivalences are not yet Lean
ports. Our exact arithmetic Cantor component now fills the elementary pairing
step proposed by the report; internal certificate normalization, represented
history and full coded proof/trace transports remain separate obligations.
