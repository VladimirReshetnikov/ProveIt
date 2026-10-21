# Membership-atom alarms for the calibrated numerical calculus

## Result

Replace the NIP command's exact cache test `h = 1` by `h % 4 = 1`, retaining exactly its old nonhalting output: preserve the current formula `t`, counter `d`, and scheduler registers; pop the encoded stack into the cache, with both scratches and the command selector restored to zero.

This is a genuinely different halting predicate on the raw register machine. It halts, for example, on cache `5 = Rel(1,0)` as well as `1 = Rel(0,0)`. It preserves the intended blank nonhalting/Con(ZFC) equivalence whenever the modified source has a sound binary implementation and a calibrated seed. The statement below is an ordinary mathematical proof; no new machine state count or proof-assistant endpoint follows from the predicate alone.

## 1. Literal code identity

The pinned repository defines

    P(i,j) = (i+j)(i+j+1)/2 + j,
    Rel(i,j) = 4 P(i,j) + 1.

For every natural `h` with `h % 4 = 1`, let `(i,j) = unpair(h // 4)`. Cantor's inverse identity and division with remainder give `h = Rel(i,j)`. Conversely every such membership code has residue 1. Thus the proposed test accepts exactly all raw membership-atom codes. It does not accept native equality codes, whose residue is 3, or universal codes, whose residue is 2. The truth alias `0 = Imp(0,0)` is also excluded.

There is no well-formedness assumption: the above decomposition holds for every natural number in the accepted residue class. In the existing decoder these raw codes all decode to membership atoms.

## 2. No membership atom is a theorem in any nonempty irreflexive model

Let `M = (V,R)` have a nonempty domain and irreflexive relation: for every `v` in `V`, not `R(v,v)`. Assume it satisfies every exact gated native bundle required by the numerical calculus. The existing code-soundness theorem says that every derivable code is true under every assignment `e : Nat -> V`.

Suppose `Rel(i,j)` is derivable. Choose any `v` in `V` and the constant assignment `e(k)=v` for all `k`. Literal atom semantics turns soundness into `R(v,v)`, contrary to irreflexivity. This works whether `i=j` or `i!=j`. Distinct variable names need not denote distinct objects.

Consequently every derivable code `h` satisfies `h % 4 != 1` in any such model. In particular, this conclusion does not follow merely from positivity or a syntactic tag invariant; it uses universal assignment semantics and irreflexivity. Expanding the predicate to all odd codes would be invalid: native equality `Eq(i,i)` has residue 3 and is derivable.

The dominated-rho8 calculus used by K215 is a subcalculus of the unrestricted numerical calculus, and the accepted finite rho8 recovery proves equality of their theorem sets on every natural code. Its soundness therefore follows from the same model theorem. This direction does not need the converse rho8 recovery.

## 3. The ZFC consistency implication

The inherited native/ZFC calibration supplies the required nonempty irreflexive native model from a model of ZFC. Within ZFC, the ordinary completeness theorem gives a set-coded model of ZFC from the syntactic statement Con(ZFC); no transitive-model or well-founded-model assumption is inserted. These are the same model and code-soundness inputs used by the existing calibration.

It follows, by ordinary reasoning formalizable in ZFC, that

    Con(ZFC) -> for every h,
      (DominatedTheorem(h) -> h % 4 != 1).

This is not an absolute assertion that the alarm can never be reached. It is the conditional soundness statement needed for a consistency search. ZFC need not prove its own consistency.

## 4. Actual-run soundness of the expanded alarm

The accepted command invariant says that current formula `t`, cache `h`, and every successively decoded stack head are dominated-calculus theorems. The calibrated initial frame satisfies it. AX, MP and DROP are unchanged. A nonhalting new NIP has exactly the old theorem-preserving pop effect. At a new halt, the invariant supplies a theorem `h` whose residue is 1. Section 3 yields a contradiction to Con(ZFC).

Therefore ZFC proves

    Halts(new enumerator, calibrated seed) -> not Con(ZFC).

The proof covers all candidate encodings, including unintended raw payloads; it does not restrict attention to the command words emitted by a correctness compiler.

## 5. Completeness is an early-halting refinement

Compare the old and new command executions from the same boundary state. Until the new execution halts, their stores agree exactly. A non-NIP command is unchanged. At NIP, if the new test is false, then `h != 1`, so both commands take the identical nonhalting pop. If the old machine halts because `h=1`, the new machine also halts because `1 % 4 = 1`. The new execution may halt earlier when its cache is another membership atom.

Induction on a finite old halting execution proves:

    Halts(old enumerator,s) -> Halts(new enumerator,s).

The statement holds for every raw boundary state `s`, independently of theoremhood. In particular, the existing strong proof-block compiler, cofinal padding argument, decreasing proof-list rank, and cutoff-four scheduler theorem transfer for completeness without any changed command words. Their contracts already allow an early halt as an alternative to exact return.

The inherited old equivalence yields the reverse consistency implication:

    not Con(ZFC) -> Halts(new enumerator, calibrated seed).

Together with Section 4, the modified abstract enumerator has precisely the intended consistency-sensitive halting behavior.

## 6. Precise remaining binary obligations

The source replacement must compute the residue test for all natural cache values, halt exactly in residue class 1, and terminate on the other three classes with the same complete register output as old NIP. Its normal exits must have the same surrounding control flow. After compilation, every changed decoder/arithmetic role needs an all-natural full-tape runtime proof, and the exact blank run must reach a valid calibrated frame. Source-DAG size and finite register tests do not discharge those obligations.

If these obligations hold with positive binary durations, the finite blank prefix and runtime simulation compose to prove in ZFC:

    not Halts(M,blank) iff Con(ZFC).

## Sources inspected at the pinned repository commit

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `75716498437bfc7291d5900cab2983a11fd54bac`.

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean`: definitions `wel`, `dec_wel`, `sat_wel`, theorem `c254_sound`.
- `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md`: exact theorem-set equality and unchanged calibrated numerical theory.
- `Computability/BusyBeaver/Research/ZFC/candidate-k215/provenance/permuted-commands/sections/source_calibration.tex`: literal command equations, safe invariant, strong compiler, and cofinal cutoff-four argument.
- `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md`: exact accepted K215 source/runtime/blank interfaces and inherited consistency calibration.

## Novelty scope

The integrated material inspected contains specialized exact-one NIP tests (Source145), cache-result MP variants (Source54), and transfer-pop commands and a derived top-one test (Source166). None of those changes the alarm to the whole membership residue class. The latest incoming binary ZIP archives could not be inspected through the available GitHub text interface, so novelty is claimed only relative to the inspected integrated sources, not as a global priority claim.
