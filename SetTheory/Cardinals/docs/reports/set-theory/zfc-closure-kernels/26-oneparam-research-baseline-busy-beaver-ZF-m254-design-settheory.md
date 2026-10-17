# zf/m254/settheory: the set-theory layer for the 254-state ZFC machine

## Result (proved, CHECK PASS)

```coq
Theorem S_equicons     : SIR ⊢TC ⊥ <-> ZFc ⊢TC ⊥.                         (* S_main.v *)
Theorem S0_equicons    : S0  ⊢TC ⊥ <-> ZFc ⊢TC ⊥.
Theorem S_ZFC_equicons : SIR ⊢TC ⊥ <-> (fun phi => ZFc phi \/ phi = ax_ac) ⊢TC ⊥.
Theorem ZF_to_S0       : ZFc ⊢TC ⊥ -> S0 ⊢TC ⊥.                             (* direction (B) *)
Theorem S_to_ZF        : SIR ⊢TC ⊥ -> ZFc ⊢TC ⊥.                            (* direction (A), S_sound.v *)
(* Print Assumptions: Closed under the global context (all of them) *)
```

Everything is in the Kirst-Hermes library syntax (minimal signature `∈'`, `≡'`; de Bruijn;
classical ND `⊢TC`). `ZFc` = `Std_iface.ZFc` (zf/stdzf), the same target as the 335/336/354
machines, so the machine side (m254-logic) only has to prove `halts tm c0 <-> SIR ⊢TC ⊥`.

```
python build.py          # compiles everything at Idle priority, then Check.v; prints CHECK PASS
```

Needs the compiled `../../stdzf/coq` (ZF), `../../regcon` (RegCon), `../../zfc` (ZFC) and the
vendored library. About 1,500 lines of Coq; clean build a few minutes.

| file | content | lines |
|---|---|---|
| S_def.v | the theories S0, SIR (CP, GIC schema, IR) | 56 |
| S_qt.v | atom-substitution translation `qt Eqv Mem`; `qt_prv` (derivations translate), `qt_tprv`, `tprv_cut` | 143 |
| S_gic.v | instantiating GIC closures (`gic_use`); raw separation from GIC (`sepS_use`) | 79 |
| S_raw.v | raw set theory in S0: endpoint uniqueness of Kuratowski codes, CP helpers, empty set, exact pairs, unions, code existence, all-code bound | 202 |
| S_quot.v | Bisim / ≈ / E*; ≈ is an equivalence, E* respects it, quotient extensionality, formula invariance | 371 |
| S_ax.v | S0 proves the translation of every axiom of ZF0 + INF_lib | 313 |
| S_sound.v | every SIR axiom holds relativized to L inside ZF + Reg; `S_to_ZF` | 302 |
| S_main.v, Check.v | assembly, statement check | 57 |

---

## 1. The theory S (decoded from source.py)

`ZF2.axioms` in `inputs/source.py` builds, in RPN, the GEN of the cache followed by nine roots.
Reading `Imp`, `Rel`, `All`, `Eq` with `wex = ¬∀¬`, `wa = ¬(A → ¬B)`, params a = param1,
b = param2 (after the read), c = param3, r = a fresh read:

1. `((c → r) → a) → ((a → c) → (b → c))`, Łukasiewicz's single axiom for the implicational calculus;
2. `c=a → (c=b → a=b)`; 3. `(∃a ∀a b) → b` (B6c); 4. `c=a → (R(c,b) → R(a,b))`;
5. `∀a ∀b c → ∀b ∀a c`; 6. `a=b → (R(c,a) → R(c,b))`; 7. `∀a(b → c) → (∀a b → ∀a c)`;
8. `∃a (a=b)`;
9. the bundle, gated (top of stack replaced by code 0 = ⊤ when c = b or c = a; `if_eq` consumes both
   arguments, so the second test really is c vs a):

        ∃b [ ∀a (R(a,b) → (∃c (∀b (∀c (R(c,b) → R(c,a)) → R(b,c)) ∧ R(c,b)) ∧ ∀c (R(c,a) → R(c,b))))
             ∧ R(c,b) ]
      ∧ ∃c [ ∀a (R(a,b) → ∀b (φ_c → ∃b (φ_c ∧ R(b,c)))) ∧ ∀b (R(b,c) → ∃a φ_c) ]
      ∧ ((R(a,b) → ∀c R(a,b)) ∧ (a=b → ∀c a=b))

   φ_c is the formula with code c. With **R(i,j) read as v_i ∈ v_j (direct membership; the PA
   branch's converse reading does not apply here)** the first conjunct is CP at the free point v_c
   and the second is GIC for φ_c (input v_a, output v_b, free domain v_b, collection set v_c).
   Self-freshness makes v_c fresh for φ_c.

The clean theory (`S_def.v`):

    S0  = [ax_refl'; ax_sym'; ax_trans'; ax_eq_elem'; ax_cp] ∪ { forall_times n (gic φ) | closed }
    SIR = S0 + ax_ir

    CP  : ∀p ∃V ( p∈V ∧ ∀x∈V ( x⊆V ∧ ∃W∈V ∀z (z⊆x → z∈W) ) )
    GIC : ∀B ∃C ( ∀a∈B ∀y (φ(a,y) → ∃y' (φ(a,y') ∧ y'∈C))  ∧  ∀y∈C ∃x φ(x,y) )
          (φ: $0 = input, $1 = output, $(k+2) = parameter k)
    IR  : ∀x ¬ x∈x

No extensionality, foundation, choice, empty set, pairing, union, separation or infinity
axioms. Machine-side obligations (m254-logic): every root instance, including the collision case
a = b and the gate-failed ⊤, is derivable in SIR (PDF Lemma 7.2: a = b uses IR, CP and an empty
set from GIC); conversely every SIR axiom is derivable by the machine (PDF §7.4: θ_A(x,y) :=
x∈A ∧ θ, padding to a fresh code, GEN + instantiation for the domain).

## 2. Direction (B): ZFc ⊢ ⊥ → S0 ⊢ ⊥ (bisimulation quotient)

### 2.1 Translation
`qt Eqv Mem φ` replaces `x ≡' y ↦ Eqv x y` and `x ∈' y ↦ Mem x y`, keeping connectives and
quantifiers (no relativization: the quotient ranges over all raw objects). Terms are variables,
so `qt` commutes with substitution and `qt_prv` is a 40-line induction on derivations.
Infinity: we interpret O'Rear's `INF_lib` (∀x ∃y (x∈y ∧ ∀u∈y ∃z∈y z = {u})) and use the proved
`Std_setinf.inf_or_to_zf : ZF0 + INF_lib ⊢ ax_om'`, translated by `qt_prv`. Schema closures:
`qt (forall_times n ψ) = forall_times n (qt ψ)`, the S0 axioms are closed, so it suffices to prove
the open matrix.

### 2.2 Definitions (`S_quot.v`)
Codes: `OP0 x y c` (zf/zfc Z_base), `App0 R x y := ∃c∈R. OP0 x y c`.

    Bisim R := ∀p ∀q (App0 R p q → (∀a∈p ∃b∈q App0 R a b) ∧ (∀b∈q ∃a∈p App0 R a b))
    Eqv x y := ∃R (Bisim R ∧ App0 R x y)                                   ("≈")
    Mem x y := ∃u∈y. Eqv x u                                                ("E*")

This is simpler than the PDF's §5.3, which also asks for a transitive stage W ∋ x,y, an exact
all-code set D over W and R ⊆ D. Those witnesses are only needed inside the proofs of symmetry
and transitivity (built on the spot); dropping them removes the post-collection CP step from
quotient extensionality.

### 2.3 Raw toolkit in S0 (`S_gic.v`, `S_raw.v`)
* Separation (schema) from GIC with `θ(u,v; A, p⃗) := (u ∈ A ∧ v ≡ u) ∧ ψ(v; p⃗)` (ψ applied to
  the OUTPUT), domain A: only the atomic congruence axiom is used, never Leibniz for ψ.
* Empty set: separation by ⊥.
* Exact pair: e empty; CP at e gives V ∋ e and W ∈ V with e ∈ W; e ≢ W. GIC over V with
  `(u≡e ∧ z≡a) ∨ (u≡W ∧ z≡b)`.
* Union: separation from a CP container. Code existence: pairs of pairs.
* Endpoint uniqueness `op_inj`: equality axioms only (PDF Lemma 5.3).
* All-code bound: CP at W, then the power containers Q ∋ subsets of W and D ∋ subsets of Q.

### 2.4 Quotient lemmas (`S_quot.v`)
* `eqv_refl`: diagonal codes over a CP container (separation `psi_diag`).
* `eqv_sym`: reversed codes over a container of R (`psi_rev`), endpoints identified by `op_inj`.
* `eqv_trans`: composite codes over a container of {R1,R2} (`psi_comp`).
* `mem_r`: root forth clause + the same R; `mem_l` from sym + trans.
* `eqv_ext` (quotient extensionality): two GIC instances collect whole local bisimulations
  `θ_f(u,R) := ∃v∈y (Bisim R ∧ App0 R u v)` over x and `θ_b` over y; R := ⋃F ∪ ⋃G ∪ {k}, k a code
  of (x,y); edge cases c ≡ k (coverage) / c ∈ r ∈ F∪G (no-extra gives Bisim r).
* `qt_inv` (formula invariance), by induction on φ.

### 2.5 Translated axioms (`S_ax.v`)
Equality axioms and extensionality from the quotient lemmas; empty set, pair, union from the raw
constructions; power set: CP gives W ⊇ raw subsets of a, P := {r∈W | r⊆a}, an interpreted
subset X is ≈ its raw trace {u∈a | Mem u X} (quotient extensionality); INF_lib: the CP container
is raw-closed under singletons; separation: raw separation by `qtS φ` + `qt_inv`; replacement: GIC
with the raw domain guard `u ∈ a ∧ qtS φ(u,v)`, `qt_inv`, functionality modulo ≈.
IR is not used in (B).

## 3. Direction (A): SIR ⊢ ⊥ → ZFc ⊢ ⊥ (`S_sound.v`)

Instead of the PDF's Lemma 6.1 (V_α, ranks, needs transitive closures and ∈-induction, none of
which exist in zf/zfc), the SIR derivation is relativized to Gödel's L, exactly as zf/zfc's
`ac_relcon`, and each SIR axiom is proved in L inside ZF + Reg. L comes with its own hierarchy,
so no ranks are needed:

* equality axioms: `Z_axL.axL_ZFR`;
* IR: regularity (`Z_ord.no_self_g`);
* GIC^L (`L_gic`): `ord_collect` with Q(δ,u) := "if u has an L-witness y with φ^L(u,y), one lies
  in L_δ" (monotone by `LL_sub`) bounds all witnesses in one L_β (`collect_L`); then separation in
  L (`Z_axL.axL_sep`) from L_β with ∃x φ(x,y) gives C ∈ L;
* CP^L (`L_cp`): V := L_β with β from the reflection principle (`Z_refl.reflection`) for the
  selector formula θ(x,W,s,t) := (s∈t ∧ ∃W' ζ(x,W')) ∨ (¬ s∈t ∧ ζ(x,W)), ζ(x,W) := ∀z (z⊆x → z∈W),
  which reflects ∃W ζ (instance s := p ∈ t := L_α) and ζ itself (instance s = t := x, ¬ x∈x by
  Reg) at the same β. The constructible power set (`axL_power`) gives ∃W ζ in L, reflection puts
  such a W in L_β, and the second reflection makes it contain every constructible subset of x.

Then `S_to_ZFR : SIR ⊢TC ⊥ -> ZFR ⊢TC ⊥` (transfer + `MinZF.collect`) and
`Link.regularity_relcon_std`.

## 4. Review of the PDF's argument (Sec 5-7)

The ordinary argument for (B) is correct. Points found:

1. Correct but over-built (§5.3, §5.4): the stage/all-code witnesses in the definition of ≈ are
   unnecessary (see 2.2).
2. Separation (§5.1) really follows from PSC, and from GIC directly; only atomic congruence is
   needed if the formula is put on the output.
3. Power set (§5.7) is right: CP gives a container for the RAW subsets of a; subset lifting is
   the raw trace plus quotient extensionality.
4. Infinity (§5.8) proves only the weak translated axiom; the library's `ax_om'` (least
   inductive set) needs a ZF derivation on top (we use INF_lib + `inf_or_to_zf`).
5. (B) uses no IR and no foundation-like principle.
6. "Set-coded bisimulation without extensionality" works because codes are only used through
   endpoint uniqueness and all-code SUPERSETS from CP; duplicate codes are harmless.
7. Lemma 6.1 (ZFC ⊢ CP + PSC) is fine, but the formalization is much cheaper through L
   (section 3) than through V_α.
8. Collision soundness (§7.3) is right: a = b is handled by IR; c = a or c = b must stay gated
   (with c = b the container's final atom becomes v_b ∈ v_b under ∃v_b, refuted by IR).
9. The ZFC root only makes sense with R(i,j) = v_i ∈ v_j.

No soundness problem found in SIR: it is equiconsistent with ZF and ZFC (now formally). The
nonstandard numerical aliases (code 1 = Rel(0,0) = F, code 0 = Imp(0,0) = ⊤) are sound in models
of IR, which is why SIR contains IR.

## 5. Remaining work (outside this directory)

m254-logic: `prov254 (the machine's Hilbert system) ⊢ F <-> SIR ⊢TC ⊥`, including adequacy of
the nine-root basis, the gate/alias soundness, and the §7.4 recovery of every GIC closure.
m254-tm: the TM ↔ source-program simulation.
