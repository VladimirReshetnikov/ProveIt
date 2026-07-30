# Proposal: automatic term synthesis in Leant, borrowing from Djex

*Status: proposal (no implementation yet). Companion to
[PROPOSALS.md](PROPOSALS.md).*

Djex (`C:\Djex`) merges two Haskell expression synthesizers — Djinn
(Dyckhoff's LJT calculus: complete, terminating intuitionistic proof
search that emits programs) and Exference (ranked heuristic search with
resource budgets and type-class evidence) — behind one
parser-independent "synthesis foundation" and a single library contract.
This document analyzes which of its ideas transfer to Lean 4 term
synthesis inside Leant, what they would buy us, and how to build it.

## 1. What Djex actually provides (and what maps)

| Djex idea | Substance | Lean/Leant mapping |
| --- | --- | --- |
| **LJT engine (Djinn)** | Complete, *terminating* proof search for intuitionistic propositional logic over `->`, tuples, `Either`, `Void`, opaque type variables; emits a lambda term, or a definitive "no term exists" | Curry–Howard transfers directly: the same calculus decides the Lean fragment `→ × ⊕ Empty Unit` in `Type` and `→ ∧ ∨ ⊥ ⊤ ¬ ↔` in `Prop`, emitting `fun`/`⟨,⟩`/`Sum.inl`/`.casesOn` terms |
| **Non-inhabitation verdicts** | "Proof-backed non-inhabitation result... when formula translation is complete" (library-api.md) | For *opaque* type variables, LJT failure means **no closed term exists at that polymorphic type** — a trustworthy negative answer no Lean tactic currently gives (`exact?` failing proves nothing) |
| **Exference engine** | Best-first search over an *inventory* of typed constants with per-name ratings (`environment/*.ratings`), explicit step/queue/depth budgets, ranked candidate batches | Phase-3 idea: weighted search seeded from Leant's cached **browse environment** (the constant inventory we already extract for `:browse`/completion), with a ratings file for core/Mathlib |
| **Shared synthesis foundation** | Parser-independent vocabulary (`Name`, `Type`, `Constraint`, `Environment → Inventory → PreparedInventory → QueryResult (SearchBatch Candidate) → Expression`), each arrow a checked boundary | The template for Leant's internal engine boundary: one fragment grammar, one candidate term grammar, one verification protocol, with the engine behind it swappable. **Scope decision: this feature is Haskell-only** — `leant-hs` links Djex in-process; the Python implementation does not grow a synthesis host |
| **Verification posture** | Engines are explicit about semantics ("neither backend guesses the other's"); truncated batches are labeled; a finished heuristic batch with no candidates "is not a proof of non-inhabitation" | Leant goes one better: **every candidate is elaborated by the Lean backend before display** (`example : (T) := term`), so the synthesizer never needs to be trusted — the same outsource-soundness pattern `:search?` and prove mode already use |
| **Embeddable library** | `build-depends: djex`, GHC 9.12.4, sealed session + checked request + result envelope; also three CLIs (`djex djinn --render expression "a -> a"`) | `leant-hs` is built with **the same GHC 9.12.4** — it links Djex directly as a library, in-process, with no subprocess or protocol overhead |
| **Shared REPL conventions** | Explicit backend selection (`djinn`/`exference`/`both`), settable limits, environment files | `:synth` command options: engine choice, candidate count, budget — consistent with Leant's `:set`-style toggles |

Two Djex components deliberately do *not* map:

- **Type-class evidence resolution** (Exference's givens/superclasses/
  instances): Lean's elaborator already resolves instances better than we
  could; synthesized terms should simply leave instance arguments
  implicit and let the backend's elaboration fill them. Djinn's honest
  stance — validate the context, "deliberately withhold class methods"
  from the proof environment — is the right initial posture for Leant too.
- **Haskell-source environment loading**: Leant's inventory comes from
  the live Lean environment via metaprograms, which is strictly better
  than parsing source files.

## 2. Why this is worth having: benefits analysis

### 2.1 It fills a real gap between Lean's existing tools

| Tool | What it does | What it does not do |
| --- | --- | --- |
| `exact?` / `apply?` | Finds an **existing** lemma closing the goal | Cannot *compose* a new term; fails on `(A → B → C) → (A → B) → A → C` unless that exact lemma exists |
| `tauto` / `itauto` (Mathlib) | Decides propositional goals (`itauto` is intuitionistic-complete) | `Prop`-only tactics; need Mathlib imported (minutes on this machine); no term display culture, no negative verdicts, nothing for `Type` |
| `aesop` | General proof search | Heuristic, Mathlib, `Prop`-oriented, no non-inhabitation answers |
| `decide` | Decidable ground propositions | Nothing polymorphic or data-level |
| **Proposed `:synth`** | **Constructs** programs/proofs in the structural fragment, in `Type` *and* `Prop`, with core Lean only, multiple ranked candidates, and trustworthy "no closed term exists" verdicts | Dependent types, recursion (see §5) |

The sweet spot is *higher-order plumbing*: currying/uncurrying,
projections, composition, distribution lemmas (`A × (B ⊕ C) → (A × B) ⊕
(A × C)`), continuation shuffles (`((A → B) → A) → (A → A)`) — terms one
writes constantly, where `:synth` answers in milliseconds with the exact
lambda, works in a bare `--plain` session, and can also say "there is
provably no such closed term" (e.g. Peirce's law, double-negation
elimination) — which is *educationally* precious: Leant's built-in help
already explains `imax` and impredicativity; a synthesizer that answers
"`((A → B) → A) → A` has no constructive inhabitant, and here is the
closest classical variant" continues that pedagogy.

### 2.2 Multiple candidates are a feature, not a luxury

`a → a → a` has two inhabitants that matter (`fun x _ => x` and
`fun _ y => y`). Djinn enumerates alternatives; Exference ranks them.
For *programs* (as opposed to proof-irrelevant `Prop`s, where any
inhabitant will do) candidate choice is the whole point — Leant should
display a numbered batch, each one already Lean-verified, and let the
user pick (`:synth` then `1`), mirroring Djex's `SearchBatch Candidate`
with explicit truncation labeling.

### 2.3 It compounds with what Leant already has

- **Prove mode**: `:synth` on the current goal becomes an `exact <term>`
  script step — a constructive complement to `:auto`'s finisher battery,
  and unlike `exact?` it needs no premise database.
- **`sorry` flow**: `sorry` already prints its goal and offers `:prove`;
  the same hook can offer synthesis when the goal is in-fragment.
- **Browse environment**: the phase-3 inventory (constants + types) is
  exactly what `:browse`/completion already extract and cache.
- **Verification loop**: `example : (T) := candidate` is one `runCmd` —
  infrastructure that exists, including timeout handling and crash
  replay.
- **A reason for `leant-hs` to exist beyond parity**: so far the Haskell
  port mirrors the Python original. In-process Djex embedding is the
  first capability where the Haskell implementation is structurally
  advantaged (same GHC, direct library linkage, no IPC), giving the two
  implementations complementary rather than duplicate roles.

## 3. Architecture

```
 Lean type/goal (string)
        |  backend: #check-normalize, pp with explicit binders
        v
 Fragment translator  ── out-of-fragment ──> honest refusal (":synth handles
        |                                    →/×/⊕/∀(non-dep)/⊥/⊤ over opaque
        v                                    variables; this goal uses X")
 Engine (LJT now; ranked search later)
        |         candidates (internal term grammar)
        v
 Lean renderer (fun/⟨,⟩/Sum.casesOn/False.elim/absurd...)
        |
        v
 Backend verification: example : (T) := term   [reject failures silently]
        |
        v
 Ranked, verified batch  ->  user picks  ->  session/`it`/prove-script
```

Design rules, all inherited from Djex:

1. **Checked boundaries.** The translator refuses anything outside the
   fragment with a specific reason, like Djex's checked request edge —
   no silent wrong answers.
2. **The engine is never trusted.** Only backend-verified candidates are
   shown. This means the LJT port does not need to be bug-free to be
   safe, and phase-3 heuristics can be arbitrarily aggressive.
3. **Negative answers are labeled by strength.** "Provably uninhabited
   (complete fragment)" vs. "search exhausted budget" — Djex's exact
   distinction between Djinn and Exference verdicts.
4. **One narrow engine boundary.** The translator/renderer speak to the
   engine through a small typed interface (goal in, candidate batch
   out), so the LJT engine, a future ranked-search engine, or a
   different backend can be swapped without touching the REPL layer.
   Haskell-only: the engine lives in `leant-hs` as a direct Djex
   library dependency; `leant.py` deliberately does not implement this
   feature.

### Translation notes (the genuinely new work)

- **Into the fragment**: elaborate the goal via the backend with
  pretty-printing pinned (`set_option pp.foralls true`, explicit
  parenthesization); parse only: `∀ (x : _), T` where `x` unused
  (= arrow), `→`, `×`/`And`, `⊕`/`Or`, `Empty`/`False`, `Unit`/`True`,
  `Iff` (as pair of arrows), `¬` (as `→ False`), and opaque heads
  (variables and any constant applied to arguments, treated atomically).
  Universally quantified *type* variables at the front (`∀ {α : Sort u}`)
  become Djinn's opaque variables — this is exactly Djex's "explicit
  prenex polymorphism at the checked request edge".
- **Out of the engine**: LJT proofs are lambda terms with pairing,
  injections, and case splits; render `⟨a, b⟩`, `Sum.inl`/`Or.inl`,
  `nomatch`/`False.elim`, `.1`/`.2`. In `Prop` render the logical
  spellings, in `Type` the data spellings — the translator knows which
  side it is on from the goal's universe.

## 4. Phased plan

- **Phase 0 — spike (S).** `:synth` in `leant-hs` only, engine =
  embedded Djex (`build-depends: djex`; same GHC). Fragment: arrows and
  opaque variables. Verify via backend, render, display batch. Proves
  the translation round-trip end to end.
- **Phase 1 — the real feature (M).** Full propositional fragment (×,
  ⊕, ⊥, ⊤, ¬, ↔, non-dependent ∀), Prop/Type-aware rendering,
  non-inhabitation verdicts, candidate numbering and selection,
  prove-mode integration (`:synth` as a tactic-step producer). The
  Python REPL's `:synth` prints a pointer to `leant-hs` rather than
  growing its own host.
- **Phase 2 — local inductives (M/L).** Treat non-recursive,
  non-dependent user inductives and structures as generalized sums of
  products: constructors as right-rules, `casesOn` as left-rules —
  precisely how Djinn admits Haskell `data` declarations. Leant already
  parses environments well enough (`:browse` machinery) to fetch
  constructor signatures.
- **Phase 3 — ranked environment search (L, optional).** Exference's
  contribution: inventory = browse-env constants, filtered by the
  existing generated-name blacklist; per-name ratings file
  (`leant.ratings`, format lifted from Djex's `environment/*.ratings`);
  best-first search with step/queue/depth budgets surfaced as `:set`
  options; batch truncation reported honestly. This is where `:synth
  (α → β) → List α → List β` starts answering `fun f l => List.map f l`
  — recursion arrives via *library reuse*, not via synthesizing
  recursors, sidestepping termination questions exactly as Exference
  does.
- **Phase 4 — research horizon (not scheduled).** Dependent goals,
  `Decidable` instance synthesis, interaction with `exact?` as a
  sub-oracle inside the search (Djex's `both` backend mode suggests the
  UX: run LJT and the heuristic in parallel, label the sources).

## 5. Honest limitations

- **No dependent types** in the decidable fragment: goals mentioning a
  bound variable in a later type are refused (with the reason). This
  still covers an enormous share of interactive "plumbing" moments.
- **No recursion before phase 3**, and even then only by reusing library
  functions; `:synth` will never invent `Nat.rec`-based programs. Djinn
  has the same boundary and remains useful after twenty years.
- **Parametricity caveat**: "uninhabited" verdicts are about *closed
  terms at the polymorphic type* — `∀ α β, α → β` being uninhabited does
  not mean a particular instantiation is empty. The display must say
  "no closed term of this polymorphic type exists", never "this is
  false"; in `Prop` the verdict must further note it is about
  *constructive* provability (Peirce's law is classically fine).
- **Performance**: LJT on interactive-size goals is microseconds; the
  cost center is the backend verification round-trip (~100–300 ms per
  candidate on this machine), so batches should verify lazily, top
  candidate first.
- **Maintenance**: embedding Djex ties `leant-hs` to a large local
  package (and to its GHC version). Mitigation: the narrow engine
  boundary keeps Djex swappable for a small purpose-built LJT module
  later, without REPL-layer changes.
- **Haskell-only**: Python Leant users must switch binaries for this
  feature — an accepted asymmetry (see §2.3); the two implementations
  now have distinct strengths instead of being mirrors.

## 6. Recommendation

Do phase 0 and phase 1: the effort is modest, every piece of supporting
infrastructure (backend verification, browse env, prove mode) already
exists in `leant-hs`, and the payoff — instant
verified lambda terms, trustworthy uninhabitation answers, and a
prove-mode step that composes rather than searches — is a capability no
current Lean tool combination offers in one place. Phase 2 is worth it
the moment phase 1 sees real use on structures; phase 3 should wait
until the ratings/inventory design can be tried against Mathlib-scale
environments without hurting Leant's startup discipline.
