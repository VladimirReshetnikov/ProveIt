# zfc_254: program and logic layers (design / scoping)

Target: `halts tm254 c0 <-> ZFc ⊢TC ⊥` (and the ZFC / Reg variants via `stdzf_r3_repo/regcon`, `zfc/`),
for the third party's 254-state table `../inputs/zfc_254.tm`, whose source program is
`../inputs/source.py` (reviewed copy: `source_local.py`, identical except for the dropped
`from setup_paths import *`).

Status of this directory: scoping only, no Coq yet. Everything below about the program is
validated by computation (section 8). The logic-layer statements are a plan.

## 0. Summary

* **Coding is not Wade's.** Wade/O'Rear (our v335): `code = pair(pair(x,y), tag)`, standard Cantor
  `pair x y = x + tri(x+y)`, five tags with a primitive `Wn`. zfc_254: `4·P(x,y) + tag`, **dual**
  Cantor `P(x,y) = tri(x+y) + y`, four tags (Imp 0, Rel 1, All 2, Eq 3), no negation
  (`¬A = A → F`). They agree on one point: code 1 = `Rel(0,0)` = `v0 ∈ v0` in both.
  So the halting formula is the same as our `prov (Wel v0 v0)`, but every other code is different,
  and so is the halting test: zfc_254 halts inside NIP when the **cache** (param2) is 1. Wade's
  machine halts at the end of an iteration when topwff is 1.
* **The program graph is pinned down.** Compiling `source_local.py` with Wade's TMBuilder gives a
  219-node DAG (281-state Wade TM, `m254_wade.tm`). Flattened, it is exactly bisimilar to the
  third party's `CONTROL_GRAPH.json` `source_graph`: 6461 sites on both sides (2601 inc, 1931 decnz,
  1927 goto, 1 halt). It also equals their final `graph` up to reordering increments inside
  straight-line inc runs, which is their 339 commuted pairs. Tool: `flatten.py`.
* **The spec `enum_step` (spec.py)** agrees with register-machine runs of the DAG in all tests:
  5,000 fully unary runs and 20,000 runs with closed-form helpers. The accelerated runs include
  AX commands with codes of about 10⁹ bits. Mismatches: 0.
* **The roots.** One AX command pushes ten stack slots and leaves one gated formula current: the
  old current formula, GEN of the cache, eight helper rows ρ8…ρ1, and the bundle (section 3).
* **The completeness macros are designed and tested.** They are exact command blocks:
  Discard, leaf extraction, GEN, an MP node, a START prefix for arbitrary retained data, and a
  halting suffix. `compiler.py` runs them through `spec.enum_step` from random retained states,
  with 0 failures.
* **IR is needed for soundness.** `B6c` (ρ6) and equality existence (ρ1) are **not** pure-logic
  valid when `F` is read as `v0 ∈ v0`, the literal decoding of code 1. They hold in ZF + IR
  (`∀x ¬x∈x`), not in pure logic. This is not about the nonlogical bundle. Inside H+S, deriving
  `F → A` from ρ8 (K) and ρ6 is pure syntax. The bundle's collision cases (a = b) also need IR.
* **The hard part is completeness.** It needs `ZFc ⊢ ⊥ → S0 ⊢ ⊥`, the bisimulation-quotient
  interpretation of ZF in the nonextensional theory S0 = CP + PSC (paper section 5). This is new set
  theory in library ND. It is the dominant cost and the main risk.

## 1. Program facts (source_local.py)

Registers: nextproof, topwff, wffstack, axiomcode, param1, param2, scratch1, scratch2, prooflist;
`param3` is the same register as `axiomcode`. Helpers are the source's own versions, not Wade's.
They do not clear their outputs, so they rely on scratch1 = scratch2 = 0:

| helper | effect (all naturals) |
|---|---|
| `pair(out,in1,in2)` | `out += P(in1,in2)`; in1 = in2 = 0 |
| `unpair(o1,o2,in)` | `(o1,o2) := unP(P(o1,o2) + in)`; in = 0 (so `unP(in)` when o1 = o2 = 0) |
| `if_eq(a,b,body)` | a = b = 0 afterwards; body runs iff the old a = old b |
| `pushwff` | `ws := P(tw, ws)`; tw := 0 |
| `cons` / `wim wel wal weq` | `tw := 4·P(pop, tw) + tag` |
| `read(r)` | `(x, pl) := unP(pl)`; `r += x` (r is **not** cleared) |

`dispatch`: selector 0 → MP, 1 → DROP, 2 → NIP, ≥3 → AX with residual `param3 = selector − 3`.

Boundary invariant (checked): scratch1 = scratch2 = axiomcode = 0 after every main() run.

## 2. Abstract spec: one run of main()  (`spec.py`, Coq target `Enum254.v`)

State `(pl, np, t, S, d, h)` = (prooflist, nextproof, topwff, wffstack, param1, param2).
`S = P(top, rest)` is an infinite stream; `S = 0` reads as all zeros.

```
enum_step (pl, np, t, S, d, h) : option state :=
  (pl, np) := if pl = 0 then (np, np+1) else (pl-1, np)     -- first command of a candidate: no decrement
  (ac, pl) := unP pl ;  (x, pl) := unP pl ;  d := d + x       -- every command reads x into param1
  match ac with
  | 0 (MP)  : if wim t d = h then (t, S) := (d, P(0, S)) else t := 0 ;  h := 0
  | 1 (DROP): (t, S) := (h, P(t, S))                           -- push current, current := cache
  | 2 (NIP) : if h = 1 then HALT (None) else (h, S) := unP S   -- halt on cached F, else cache := pop
  | 3+c (AX): a := d ; (y, pl) := unP pl ; b := h + y ; (u, pl) := unP pl
              S := P(ρ1, P(ρ2, … P(ρ8, P(wal a h, P(t, S)))…))  -- t pushed first, ρ1 on top
              t := if c ≠ a ∧ c ≠ b then bundle a b c else 0
              d := 0 ; h := 0
```
`enum254_halts := ∃ n s, iter n s0 = Some s ∧ enum_step s = None`, where s0 = all zeros.

Notes:
* `d` (param1) only grows between AX commands: MP leaves it equal to the consequent, and DROP/NIP
  add their `x`. Only AX clears it.
* MP success pushes a truth cell `0` below the conclusion.
* Program encoding: a candidate N runs commands from `N` itself. Each later command `κ` is read from
  the cell `1 + P(ac, P(x, [P(y, P(u,)] tail))`. `tail = 0` ends the candidate, so every
  candidate stops after at most N+1 runs.

## 3. Exact root list (one AX command)

Parameters: `a = d + x` (param1), `b = h + y` (param2 after its read), `c = selector − 3` (param3),
`u` (a literal read into topwff), `h` = incoming cache, `t` = incoming current.
`F = Rel(0,0)` (code 1). `¬A = A→F`. `A∧B = ¬(A→¬B)`. `∃x A = ¬∀x ¬A`.
Bold letters are formula positions (decoded codes). Plain letters are variable labels. The same
register serves both roles.

Stack after AX, from the top (paper App. A2 order):

| slot | name | formula |
|---|---|---|
| ρ1 | equality existence | `∃a (a = b)` |
| ρ2 | quantified implication | `∀a(𝐛→𝐜) → (∀a 𝐛 → ∀a 𝐜)` |
| ρ3 | congruence (right) | `a=b → (c∈a → c∈b)` |
| ρ4 | quantifier commutation | `∀a∀b 𝐜 → ∀b∀a 𝐜` |
| ρ5 | congruence (left) | `c=a → (c∈b → a∈b)` |
| ρ6 | B6c | `∃a ∀a 𝐛 → 𝐛` |
| ρ7 | Euclid | `c=a → (c=b → a=b)` |
| ρ8 | Łukasiewicz L | `((𝐜→𝐮)→𝐚) → ((𝐚→𝐜) → (𝐛→𝐜))` |
| G | GEN of the cache | `∀a 𝐡` (uses `h`, before the `y` read) |
| t | old current | `𝐭` |
| current | gated bundle | `(C ∧ G') ∧ (V∈ ∧ V=)` if `c ≠ a ∧ c ≠ b`, else `0` (truth) |

Bundle (variables a, b, c; `φ = 𝐜`, so c is both the matrix code and the output-set label):
```
C  = ∃b [ ∀a ( a∈b → ( ∃c[ ∀b(∀c(c∈b → c∈a) → b∈c) ∧ c∈b ] ∧ ∀c(c∈a → c∈b) ) ) ∧ c∈b ]
G' = ∃c [ ∀a ( a∈b → ∀b ( φ → ∃b (φ ∧ b∈c) ) ) ∧ ∀b ( b∈c → ∃a φ ) ]
V∈ = a∈b → ∀c a∈b        V= = a=b → ∀c a=b
```
C is the powerset-container instance at the free point c. It is CP for distinct names.
G' is Global-Image Collection over the free domain b. The gate covers only `c ≠ a, b`, so the
collisions `a = b` occur and need IR (paper Lemma 7.2).
Self-freshness: every label occurring in the decoding of n is < n. Codes 0 and 1 have no labels once
F is read as closed, so variable c is never free in φ.
`rel` means raw membership: `Rel(i,j)` = `v_i ∈ v_j`. This is the orientation of the paper's
`E(x,A)` = x ∈ A and of Wade's `Wel`.

Comparison with Tarski S2 (our `lprov`): ρ2 = B4, ρ4 = B6b, ρ6 = B6c, ρ1 = B7, ρ7 = B8a,
ρ5 = B8b, ρ3 = B8c (variable roles permuted), V∈ ∧ V= = B6a (with the conjuncts swapped).
B1, B2 and B3 are replaced by L. L is Łukasiewicz's 1948 single axiom
CCCpqrCCrpCsp for the implicational calculus. `F → A` comes from K (via L) and ρ6.

## 4. Code-level calculus and L1

Proposal: state L1 against a **code-level** calculus, so that no decoder appears in L1. The 0/τ
alias and the `F = Rel(0,0)` alias then move into the bridge.

```coq
Inductive thm254 : nat -> Prop :=
  | T_true   : thm254 0
  | T_mp t b : thm254 t -> thm254 (wim t b) -> thm254 b
  | T_gen a h: thm254 h -> thm254 (wal a h)
  | T_r1 a b : thm254 (rho1 a b)          (* … T_r8 a b c u : thm254 (rho8 a b c u) *)
  | T_bundle a b c : c <> a -> c <> b -> thm254 (bundle a b c).
Theorem L1_254 : enum254_halts <-> thm254 1.
```

**Soundness** (`L1_Sound254.v`). Invariant: `thm254 t`, `thm254 h`, and every entry of the stream S
satisfies `thm254`. Zeros are covered by `T_true`. MP: `h = wim t d` gives `thm254 d`. AX: each
pushed slot is a constructor instance, and the current formula is a bundle or 0. NIP with h = 1
gives `thm254 1`. Same shape as v335 `L1.v` `Inv_step` / `goodstack`, minus the decoder.

**Completeness** (`L1_Comp254.v`). Block contract: `Build_X : (T,S,0,0) ↦* (X,S,0,0)` for all
T and S, or an earlier NIP halt. An early halt needs an incoming cache of 1, and any halt is fine
for completeness. Commands: `MP x = (0,x)`, `DROP = (1,0)`, `NIP = (2,0)`, `AX(c;x,y,u)`.

| block | commands | effect |
|---|---|---|
| Discard | `MP 1; AX(1;0,0,0); NIP^10` | (T,S,0,0) → (0,S,0,0). MP fails because `wim T 1 ≥ 4 ≠ 0`; the AX gate fails since c = a = 1; the 10th NIP pops the old current 0 |
| leaf bundle(a,b,c) | `Discard; AX(c;a,b,0); NIP^10` | → (bundle or 0, S, 0, 0) |
| leaf ρj (j = 1..8) | `Discard; AX(c;a,b,u); NIP^j; DROP; NIP^(11−j)` | → (ρj, S, 0, 0) |
| GEN i | `Build_H; DROP; NIP; AX(i;i,0,0); NIP^9; DROP; NIP; NIP` | → (∀i H, S, 0, 0) |
| MP node | `Build_A; DROP; Build_{A→B}; NIP; DROP; NIP; MP B; AX(B;0,0,0); NIP^10; DROP; NIP; NIP` | → (B, S, 0, 0) |
| START | `AX(0;1,1,0)` | arbitrary (t,S,d,h) → (R, S', 0, 0) |
| halt suffix | `DROP; NIP; NIP` | (1,S,0,0) → HALT |

In every NIP above, the incoming cache is 0, an implication code (≡ 0 mod 4), an All code
(≡ 2 mod 4), or a derived theorem. So the macros only halt on a genuine F.
The parameter-inequality problem the paper mentions (b ≥ cache) does not arise, because every AX
runs with d = h = 0.
Program: `N = encode (START ++ Build_F ++ halt suffix)`. Reaching candidate N uses the v335
lemmas `drain`/`reach` (every candidate finishes, np counts up).

Reuse from v335: `iter_*`, `drain`, `reach`, `run_tail`/`run_proof` patterns, `goodstack` style.
New: dual-Cantor arithmetic (`unP (P a b) = (a,b)`, `P a b ≥ a, b`, tag residues mod 4) and the macro
contracts. These are symbolic `enum_step` computations with `Opaque P`.

## 5. Program layer (L2): one run of main = enum_step

v335's `ProgLib.v`/`Prog.v`/`gen_prog.py` approach on the 219-node DAG of `m254_wade.tm`:
* new helper lemmas for the source's own `pair` (`out += P`), `unpair` (diagonal walk with
  `if_not_decnz`), `if_eq` (destructive; body iff equal), and `times_from_scratch` (`tw += 4·s2`);
* 20 linear `while_decnz` loops, generated as in gen_prog.py;
* four dispatch branches matched against `enum_step`.

**Interface with the TM layer (m254-tm).** Their TM implements their final flat `graph`. That graph
is equal to the source program up to commuting increments (`flatten.py`). Two options:

1. m254-tm proves TM ↔ flat-graph small-step. A Coq-checked bisimulation-up-to-commuting
   certificate (finite, decidable, ~4.5k related pairs) then transports to the DAG semantics, and
   L2 is done on the DAG.
2. L2 is proved directly on the flat graph. That is 6460 sites and much larger.

Option 1 is recommended.

## 6. Logical bridge

### 6a. Decoder (`Wff254.v`)
`D : nat → wff` (Logic.v syntax without `Wn`):
* `D 0 = τ := Wim F F` with `F = Wel 0 0`;
* `n > 0`: `n mod 4` selects Imp/Rel/All/Eq over `unP (n/4)`.
Components are smaller than n, so define D by fuel. `code : wff → nat` with `code φ ≥ 1` and
`D (code φ) = φ`. Self-freshness: `occurs v (D n) → v < n` (n ≥ 2), treating F as a closed constant.

### 6b. Soundness: `thm254 n → ZFc_reg ⊢TC ∀-closure (D n)`
1. **F-normalization.** `N(φ)` replaces each literal `Wel 0 0` by ⊥. ZF + IR proves `φ ↔ N(φ)`
   by induction, including under binders of v0. Every decoded root is then a standard formula.
2. **Rows.** ρ2–ρ5, ρ7 and ρ8 are lprov-style logic (equality via the library's equality axioms).
   ρ1 and ρ6 are pure logic only after N. With F = v0∈v0 read literally they fail in models of
   v0∈v0, so IR is needed. The 0/τ collapses (`wim 0 0 = 0`) can occur only in ρ8 and ρ2, not in ρ4, ρ6 or the bundle. They are
   harmless (τ ↔ (τ→τ)) but need a replacement-of-equivalents lemma, or a case split.
3. **Bundle, distinct names.** C is CP. Prove it in ZFc (no Reg needed):
   `V = ⋃ₙ Tₙ`, `T₀ = TC({p})`, `Tₙ₊₁ = Tₙ ∪ 𝒫(Tₙ)`, built by ω-recursion; reuse
   `Std_setrec.v`/`Std_setinf.v` if suitable. G' follows from Collection plus Separation. Collection
   needs ranks, so prove it in ZFc_reg via V_α and least stages (paper Lemma 6.1). Reuse
   `zfc/Z_ord.v` and `Z_trec.v`. V∈ and V= are logic (c ≠ a, b).
4. **Collisions** (`a = b`, c distinct). By IR, C reduces to `∃b c∈b` and G' to "take c empty".
5. Compose with `regcon/Link.v`: `ZFc_reg ⊢ ⊥ ↔ ZFc ⊢ ⊥`.

### 6c. Completeness: `ZFc ⊢TC ⊥ → thm254 1`
Chain: `ZFc ⊢ ⊥ →(Q) S0c ⊢ ⊥ →(B) Bc ⊢ ⊥ →(H) lprov[bundle hyps] ⊢ v0∈v0 →(τ) thm254 1`.

* **(Q) Quotient interpretation** (paper section 5). In library ND over S0c, with S0c = equality
  axioms + closed CP + closed PSC_θ for every θ. Interpret `≡ ↦ ≈` (set-coded bisimulation) and
  `∈ ↦ E*`. In the library, ≡ is a predicate with axioms, so a derivation translates by atom
  substitution (a `Rel.v`-like file). Then prove S0c ⊢ the translated ZFc axioms:
  equality axioms (5.5), Ext (5.6), empty/pair/union (5.6 sec.), Power (5.9), Infinity (5.10),
  Separation and Replacement (5.7 invariance + 5.8).
  Supporting lemmas: raw Separation/Empty/Pairing/Union from PSC+CP (5.1, 5.2), Kuratowski
  endpoint uniqueness (5.3), the all-code bound (5.4), and ≈ reflexive/symmetric/transitive by
  separating diagonal/inverse/composite codes.
* **(B)** Each S0c axiom from bundle instances (paper 7.4). Pick a named version φ of θ with the
  domain guard, padded by a vacuous binder so that `c = code φ` exceeds every label. Instantiate
  the closed bundle at (a, b, c), project G' (App. A3 projections), substitute the domain, and drop
  the vacuous binder. CP: project C with fresh distinct names. Doing this on the library side
  (de Bruijn) avoids most renaming pain.
* **(H)** Library ND → lprov with hypotheses: reuse `Std_H.v` / `Std_tr.v` / `Std_alpha.v` and the
  `Std_glue.v` pattern.
* **(τ)** lprov → thm254 via `Wn a ↦ Wim a F`. The L-derivations of B1, B2 (Peirce instance),
  K and Peirce are found by condensed-detachment search and emitted to Coq (as for `PropBasis.v`).
  B3 is `a → ((a→F) → b)`, using `F → b` from K and ρ6. B6a is a bundle projection with z as the
  selector c. Then `prov254-wff φ → thm254 (code φ)` (no 0 occurs inside codes of genuine wffs).

### 6d. End-to-end
`halts tm254 c0 ↔ enum254_halts ↔ thm254 1 ↔ ZFc ⊢TC ⊥`. The ZFC / Reg variants follow from the
existing `zfc/` and `regcon/` theorems. The intermediate `thm254` drops out of the trust surface.

## 7. File plan and effort

"Naive" is my first estimate. Past Coq estimates ran 3–10× high, so the calibrated column is ≈ naive/3.

| file | content | naive lines | calibrated |
|---|---|---:|---:|
| Codes254.v | P/unP (dual), codes, ρ1–ρ8, bundle, mod-4 facts | 250 | 100 |
| Enum254.v | spec (section 2) | 120 | 80 |
| L1_Sound254.v | thm254 + invariant | 150 | 60 |
| L1_Comp254.v | macros, encoding, reach | 600 | 250 |
| ProgLib254.v / Prog254.v (+ generator) | L2 on the 219-node DAG | 1300 (mostly generated) | 500 |
| Bisim254.v (option 1) | flat graph ≈ DAG up to commuting, checked by computation | 400 | 150 |
| Wff254.v | decoder, code, self-freshness | 300 | 120 |
| Sound_Hilb254.v | thm254 → lprov + IR + CP + GIC (F-normalization, collisions, τ-collapses) | 600 | 250 |
| Sound_Set254.v | library: CP in ZFc; IR, ranks, Collection, GIC in ZFc_reg | 1500 | 600 |
| Comp_Prop254.v | L-derivations, τ translation, projections | 500 | 200 |
| Comp_Bundle254.v | S0c axioms from bundle instances | 700 | 300 |
| Quot*.v | quotient interpretation of ZFc in S0c | 3500 | 1200–1800 |
| Glue254.v, E2E254.v | assembly | 300 | 120 |
| **total** | | **≈10,000** | **≈4,000–4,500** |

Order: Codes/Enum/L1 → L2 (with m254-tm) → Wff/Sound → Comp_Prop/Comp_Bundle → Quot.
The halting direction (machine → ZFC) is the cheap half. It needs only ranks/Collection as new set
theory.

## 8. Tools (all in this directory; run with Python 3.11 from anywhere)

| file | purpose |
|---|---|
| `source_local.py` | reviewed copy of the source (no `setup_paths`) |
| `build_dag.py` | compile with Wade's TMBuilder → `m254_wade.tm`; `load_dag()` gives the DAG (dag.py format) |
| `extract_rpn.py` | stub-evaluates `axioms()` etc. (no hand transcription) and prints the symbolic rows |
| `bignum.py` | exact ints below 2^512; fingerprinted values with known pair structure above |
| `rmsim.py` | Wade path-semantics RM runner; closed forms for while/unpair/pair/if_eq, each checked against brute force |
| `spec.py` | the abstract `enum_step` and the row/bundle code functions |
| `validate.py` | spec vs RM: helper closed forms, symbolic rows, 5k unary runs, 20k accelerated runs. Last run: ALL OK (`validate.log`) |
| `flatten.py` | DAG → flat op graph; bisimulation with `source_graph` (exact) and `graph` (up to commuting incs) |
| `compiler.py` | completeness macros; contracts checked through `spec.enum_step` from random retained states. Last run: 780 contracts, 0 failures |

## 9. Risks

1. **Quotient interpretation (Q).** Largest item. The paper's proof is ordinary mathematics, not
   machine-checked. The delicate points are transitivity of ≈ (composite relation inside a common
   transitive stage), the root edge in Thm 5.6, and formula invariance for E* in the schemas. I
   found no error on reading, but expect friction. Each Separation use needs explicit PSC instances.
2. **Collection in library ND** for soundness of G'. Needs V_α and ranks in ZFc_reg. Partial reuse
   of zfc/ ordinals and recursion. CP needs only ω-recursion.
3. **L2 / TM interface.** The real program is the commuted flat graph. Needs a verified
   commuting-bisimulation step or a flat-graph proof (coordinate with m254-tm).
4. **Aliases.** `F = Rel(0,0)` read literally fails in pure logic. IR is needed for ρ1, ρ6 and the
   bundle collisions. The 0 = `wim 0 0` collapse affects ρ8 and ρ2. Both are handled by the
   code-level calculus plus IR normalization, but they are easy to get subtly wrong.
5. **Self-fresh recipe (B).** Variable bookkeeping for "c = code φ fresh, padded binder, domain
   substitution". It is lighter in de Bruijn, but the named bundle must be matched exactly against
   `dB` of the library instance.
6. **Fingerprint equality in validation** (`bignum`) is probabilistic (~2⁻¹²⁰ per comparison). It is
   only used for testing; Coq never evaluates codes (`Opaque P`).

## 10. Agreed interface with m254-settheory (2026-10-13)

The shared target theory S lives in `zf/m254/settheory/S_def.v` (library minZF signature, ⊢TC):
`S0 = equality axioms + ax_cp + closed GIC instances (phi: $0 input, $1 output, $(k+2) params)`,
`S = S0 + ax_ir`.

* m254-settheory proves `S ⊢TC ⊥ <-> Std_iface.ZFc ⊢TC ⊥`. One direction is via ZFc+Reg ⊢ S (V_α,
  regcon). The other is the quotient, `ZFc ⊢ ⊥ -> S0 ⊢ ⊥`.
* This layer proves `thm254 n -> S ⊢TC closure (dB (D n))`, with the roots and the a=b collisions
  derived in S, and `S ⊢TC ⊥ -> thm254 1`.

So sections 6b.3 (sets) and 6c (Q) move to settheory. What remains here is 6b.1–2, 6b.4 (inside S),
6c (B, H, τ), and the derivation of IR in the machine calculus:
* rho1 at a = 0 is `∀v0(v0=x → v0∈v0) → v0∈v0`, since F is captured;
* the antecedent comes from `x∈x` via rho5, rho3, symmetry, vacuity V∈ (c = 0) and rho2;
* generalizing over x gives `∀x(x∈x → F)` = τ(IR).

## 11. Status 2026-10-13: layer 3 and the bridge are CLOSED (zf/m254/logic/coq, about 2,000 lines)

`python coq/build.py` builds everything at Idle priority, one coqc at a time. Every theorem below
prints "Closed under the global context".

| file | content |
|---|---|
| Codes254.v | dual Cantor P / unP (the source's unpair walk), codes, rows rho1..rho8, bundle |
| Enum254.v | FROZEN interface: `enum_step : state -> option state`, `run`, `s0`, `enum254_halts` |
| Thm254.v | code-level calculus `thm254` (T_true, MP, GEN, rows, gated bundle) |
| L1_Sound254.v, L1_Comp254.v, L1_254.v | `L1_254 : enum254_halts <-> thm254 1`. The macros are as in section 4 (compiler.py) |
| Wff254.v | total decoder `D`; `wim x 1` decodes to `Wn` |
| Bundle254.v | `BW a b c phi`; `D_bundle : c<>a -> c<>b -> D (bundle a b c) = BW a b c (D c)` |
| CD254.v | K, S, B, Peirce from the Łukasiewicz row, found by condensed detachment (cdfast.cpp, cdgen.py) |
| Comp_Prop254.v | `tau` (named wff -> code, Wn = -> F); `lprov_thm : lprov a -> thm254 (tau a)` |
| Comp_Bundle254.v | `SIR_to_thm : SIR ⊢TC ⊥ -> thm254 1`. TB = closures of tau-theorems; EqAx; IR is the closure of F -> F; CP and closed GIC instances from bundle closures (tr_equiv) |
| SoundBW254.v | `V_BW`: bundle wffs are valid in SIR (CP, IR, GIC for dB sab phi; GIC for falsity when a = b) |
| Sound254.v | `thm_to_SIR : thm254 1 -> SIR ⊢TC ⊥` (rows via the E-congruence; x -> F is identified with -.x via IR) |
| Bridge254.v | `bridge254 : thm254 1 <-> SIR ⊢TC ⊥`, `enum254_SIR : enum254_halts <-> SIR ⊢TC ⊥` |
| Logic_ZFc254.v | `enum254_ZFc : enum254_halts <-> ZFc ⊢TC ⊥` (with settheory's `S_equicons`) |

What remains for the end-to-end result: L2 (one run of the program = `enum_step`, assigned to
m254-prog) and the TM layer (m254-tm).
