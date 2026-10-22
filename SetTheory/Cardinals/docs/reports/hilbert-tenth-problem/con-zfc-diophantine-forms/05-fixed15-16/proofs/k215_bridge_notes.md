# K215 endpoint audit and ZFC interpretation notes

Pinned source commit: `cdd582bec13f908df3711fa9e05d1ddac368a5db`.

## Exact source object

The accepted input is
`Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm`, SHA-256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
Its file has a `#! start 0` header followed by 430 rows of the form
`state read write direction next`. Working states are 0 through 214;
215 is the separate halt. The alphabet is {0,1}, the tape has positions
in Z, all positions initially hold 0, and the initial head position is 0.
The only halt-entering row is `68 1 1 R 215`. In particular, a normalizer
must not treat a temporary stuck configuration or an invalid boundary
encoding as accepting. The halt action writes and moves before entering
the halt; accepting on its precondition `(state=68, read=1)` is equivalent
only after explicitly proving that convention change.

Lean's Core representation uses a list of the positions containing 1;
the empty list is the blank tape. `Machine.step` leaves halted
configurations stationary. `KDenseBridge.BlankHalts M` means
`exists t, (M.run t).state = none`. The list-zipper layer uses `none` as a
missing transition, but `KDenseBridge.blank_iff` relates these conventions.

## Closed logical endpoint

`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` proves:

```lean
KEndpoint215.blank_halts_iff_zfc_refutation :
  BlankHalts machine215 <-> BProv ZFCax_s [] Form.fBot

KEndpoint215.nonhalting_iff_zfc_consistency :
  (not (BlankHalts machine215)) <-> not (BProv ZFCax_s [] Form.fBot)
```

These have no mathematical hypotheses. The recorded independent endpoint
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
The Rocq endpoint
`K215F.CorrectDense215.tm215_halts_iff_ZFC_inconsistent` states
`Dense.halts dense_tm Dense.c0 <-> StandardZFC |-TC bottom`; its negation
is `tm215_nonhalting_iff_ZFC_consistent`. Both endpoint assumption reports
are closed under the global context according to the pinned verification
README. No fresh compiler or kernel run was performed in this audit.

The repository explicitly distinguishes these external proof-assistant
theorems from an internal proof encoded in PA or ZFC syntax. Its accepted
candidate README separately states the ordinary mathematical theorem
`ZFC proves: not Halt(K215, blank) <-> Con(ZFC)`.

## Smaller semantic entry point for later coefficient optimization

For a Diophantine construction it is unnecessary to preserve the 215-state
TM's simulation layers. `KEndpoint.c222_iff_zf_refutation` proves

```lean
KCode222.C222 Code254.F <-> BProv ZFax_s [] Form.fBot
```

and `ConstructibleChoice.zf_refutation_iff_zfc_refutation` transports from
ZF to ZFC. Thus C222(1), a tiny recursively enumerable numerical calculus,
is an equivalent target. Another completely proved interface is
`Enum222.enum_halts_iff : Enum222.Halts <-> C222 F`. Its enumerator has six
natural registers and four command forms; it uses pairing, unpairing,
addition, equality, and the finite axiom code expressions.

Let

    W(a,b) = 2(a+b)(a+b+1)+4b.

Then the literal constructor codes are polynomial, with no division:

    I(a,b)=W(a,b),  E(a,b)=W(a,b)+1,
    A(a,b)=W(a,b)+2, Q(a,b)=W(a,b)+3,
    F=1, N(a)=I(a,1), X(a,b)=N(A(a,N(b))).

C222 is the least subset of N closed under the following twelve rules:
truth 0; modus ponens from t and I(t,b) to b; generalization from h to
A(a,h); eight logical axiom rows (rho1 through rho6, growG, rho8); and
one seed bundle subject to c!=a and c!=b. All row terms are finite
compositions of W and small constants. The source definitions should be
used rather than retyping deeply nested terms without a comparison check.
Gate inequalities have a simple natural Diophantine representation:
(c-a)^2=u+1 and (c-b)^2=v+1. This interface can reduce coefficient size,
but a direct proof-checker to finite-window compiler would still need a
proved implementation; its existence alone does not give an explicit
Diophantine equation.

## How the final result is provable in ZFC

The correct justification is mathematical internalization, not a claim
that ZFC proves soundness of all of Lean or Rocq. Every object used in the
new reduction is a set available in ZFC: natural numbers, integer
polynomials, finite strings, finite maps, finite runs, and bounded
tableaux. Normalization and tableau extraction are proved by induction
on finite computations; polynomial extraction is a finite algebraic
argument plus the stated number-theoretic witness lemmas. These are
ordinary ZFC proofs and apply also to internally finite sequences in an
arbitrary model of ZFC.

For the inherited calibration, use the ordinary source theorem as proved
in the accepted K215 mathematical exposition. Its model-theoretic
arguments use set-coded first-order syntax, first-order completeness,
set-sized models and their definable constructions, quotient sets,
and the constructible class relative to a set model. The lower-chain
"well-founded part" is the internally well-founded part used by
`KQ1ZF`, not an assertion that consistency yields a transitive model of
ZFC. No soundness assumption for ZFC, inaccessible cardinal, or premise
Con(ZFC) is needed for the reduction theorem.

With `Sol(D)` the existence of a tuple in the explicitly specified
domain satisfying all polynomial equations, the proof has the form

    ZFC |- Sol(D) <-> Accept(N)
        <-> Halt(K215, blank)
        <-> Exists p Proof_ZFC(p,bottom).

Negating both sides yields exactly the requested statement. This is a
proof of an equivalence; it is not an unconditional ZFC proof of either
side. An artifact that records the external proof-assistant statement
must not be presented as an internal encoded ZFC derivation.

## Formalization boundary

A conditional Lean wrapper could take the new compiler equivalence as an
explicit hypothesis and compose it with the existing K215 endpoint. Such
a wrapper would not verify the new polynomial, so no conditional wrapper
is included or counted as completed formal work.

## Pinned source URLs

- https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md
- https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md
- https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum222.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ZF.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/CorrectDense215.v
- https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/actual/audit/independent/compiler.log
