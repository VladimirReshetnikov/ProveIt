# Repeated binding at model-valued lengths

In models of PRA plus IΣ₁, `closeOne p := ∀ bindFormula 0 p` binds the first free parameter of internally valid arity-zero `p`. `closeOne_definable` establishes a Σ₁ function graph, `closeOne_scoped` preserves arity zero, and `closeOne_leaf` lifts a target theorem across one such closure from the pushed environment.

`closeIterConstruction` and `pushIterConstruction` build fixed parameter-free Σ₁ recursion blueprints for the matching formula and environment histories, respectively. They admit histories at every model-valued length, including nonstandard lengths. `closeIter_trace_scoped` proves every entry of a formula history is arity-zero by model-internal Σ₁ induction. `closeTrace_leaf` lifts a target theorem along matched formula/environment histories, and `modelClose_leaf` builds the matching histories to prove:

```
IsSemiformula SourceL 0 p →
Pr (imp (tr (modelPush n e) p) 1) →
Pr (imp (tr e (modelClose n p)) 1)
```

Here `modelClose n p` is the n-fold binding code and `modelPush n e` the n-fold pushed environment, both with model-valued `n`. `modelClose_scope` proves that the result is arity zero. This theorem retains the target theorem at the pushed environment as a premise; the files do **not** derive it from the axiom's admission, prove no free variables remain, obtain a closed separation scheme, or establish a native iPRA derivation.

From the repository root, with a fresh final output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-model-closure.sh "$PWD" \
  /dev/shm/pa194-general-separation-replay \
  /dev/shm/pa194-ranked-open-separation-replay-v3 \
  /dev/shm/pa194-unrestricted-all-replay \
  /dev/shm/pa194-full-one-level-audit \
  /dev/shm/pa194-model-closure-replay
```

The four source modules and 15-declaration axiom audit were compiled in one fresh output. The checker pins those sources and the general-separation prerequisite object before and after, checks 15 axiom reports, and rejects `sorryAx`. Other overlay dependencies, Foundation, and Mathlib are prebuilt; this is a staged replay. Successful log: `/tmp/pa194-model-closure-replay.log`.

`PA194ModelClosureDefinable.lean` also proves Σ₁ function definability of the canonical `modelClose` and `modelPush` operations for model-valued counts. This does not itself establish sentence closure or native iPRA derivability. Its independent and repository staged replays passed against the source-replayed closure and retained prebuilt baselines. From the repository root, select a fresh output:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-model-closure-definability.sh "$PWD" /dev/shm/pa194-model-closure-replay /dev/shm/pa194-general-separation-replay /dev/shm/pa194-ranked-open-separation-replay-v3 /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-full-one-level-audit /dev/shm/pa194-model-closure-definability-repo
```
