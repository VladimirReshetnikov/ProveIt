import IPRADerivations.Foundations.Adjunction
import IPRADerivations.Core.Header

/-!
# An equivalence from explicit splittings (`ipra_categorical_methods`, Section 4)

Packet: `foundations/ipra_categorical_methods`, Subsection "Equivalence requires explicit
splittings". For fixed presentations `C`, `D` with laws and a specified functor `F : C → D`
(`Adjunction.Fun`), the *supplied* data are (`Split`):

* a lifting term `λ(a, b, h)` with `λ(h) : a → b` and `F(λ(h)) = h` for `h : F(a) → F(b)`
  (fullness, split);
* terms `c_d`, `s_d : F(c_d) → d`, `t_d : d → F(c_d)` with `s_d ∘ t_d = 1_d` and
  `t_d ∘ s_d = 1_{F(c_d)}` (essential surjectivity, split);

and `F` is faithful (`Split.Laws`). No selector is obtained from a bare existence statement:
the terms are part of the hypothesis, as the packet requires. With

`G(d) = c_d`, `G(f) = λ(t_e ∘ (f ∘ s_d))` for `f : d → e`,
`η_c = λ(t_{F(c)}) : c → G(F(c))`, `η_c⁻¹ = λ(s_{F(c)})`,

the following are derived in iPRA:

* `lift_congr`, `G_hom`, `G_congr`: typing and compatibility with arrow equality;
* `G_id`: `G(1_d) = 1_{c_d}`; `G_comp`: `G(g ∘ f) = G(g) ∘ G(f)`: `G` is a functor;
* `sec_nat`: `s_e ∘ F(G(f)) = f ∘ s_d`: the `s_d` are the components of a natural
  isomorphism `FG ≅ 1_D` (their inverses `t_d` are part of the data);
* `eta_hom`, `etaInv_hom`, `etaInv_eta`, `eta_etaInv`: `η_c` is an isomorphism;
* `eta_nat`: `η_{c'} ∘ u = G(F(u)) ∘ η_c` for `u : c → c'`: a natural isomorphism
  `1_C ≅ GF`.

Each equation in `C` is obtained by applying `F` and using faithfulness.

`cancel_mid` is the general cancellation `(g ∘ p) ∘ (q ∘ f) = g ∘ f` for `p ∘ q = 1`.

Instance with all hypotheses discharged for every presentation with laws: the identity
functor with the identity splitting (`idFun_laws`, `idSplit_laws`).
-/

namespace LeanProofs.IPRA.Foundations.SplitEquivalence

open_ipra
open LeanProofs.IPRA.Foundations.PresentedCategory
open LeanProofs.IPRA.Foundations.Adjunction

/-! ## Cancellation of an inverse pair in the middle of a composite -/

section Cancel

variable {C : Pres} (L : C.Laws) {n : ℕ} {Γ : List (Fm PTm n)}

include L in
/-- `(g ∘ p) ∘ (q ∘ f) = g ∘ f` when `p ∘ q = 1_b`, for `f : a → b`, `q : b → m`, `p : m → b`,
`g : b → d`. -/
theorem cancel_mid {a b m d f q p g : PTm n} (hf : Γ ⊢[PRAAx] C.hom a b f)
    (hq : Γ ⊢[PRAAx] C.hom b m q) (hp : Γ ⊢[PRAAx] C.hom m b p) (hg : Γ ⊢[PRAAx] C.hom b d g)
    (hpq : Γ ⊢[PRAAx] C.eqv b b (C.comp b m b p q) (C.id1 b)) :
    Γ ⊢[PRAAx] C.eqv a d (C.comp a m d (C.comp m b d g p) (C.comp a b m q f))
      (C.comp a b d g f) := by
  have hqf := L.comp_hom hf hq
  -- `(g ∘ p) ∘ (q ∘ f) = g ∘ (p ∘ (q ∘ f))`
  have t₁ := L.assoc hqf hp hg
  -- `p ∘ (q ∘ f) = (p ∘ q) ∘ f = 1 ∘ f = f`
  have s₁ := L.eqv_symm (L.assoc hf hq hp)
  have s₂ := L.comp_congr (L.eqv_refl hf) hpq
  have s₃ := L.id_left hf
  have s := L.eqv_trans s₁ (L.eqv_trans s₂ s₃)
  have t₂ := L.comp_congr s (L.eqv_refl hg)
  exact L.eqv_trans t₁ t₂

end Cancel

/-! ## The supplied data -/

/-- The supplied splitting data for a functor `F : C → D`. -/
structure Split where
  /-- The lifting `λ(a, b, h)` of `h : F(a) → F(b)`; variables `0 = a`, `1 = b`, `2 = h`. -/
  lam : PTm 3
  /-- The object `c_d`; variable `0 = d`. -/
  c : PTm 1
  /-- `s_d : F(c_d) → d`; variable `0 = d`. -/
  s : PTm 1
  /-- `t_d : d → F(c_d)`; variable `0 = d`. -/
  t : PTm 1

namespace Split

variable (S : Split) {n : ℕ}

/-- `λ_{a,b}(h)`. -/
def lift (a b h : PTm n) : PTm n := Syn.subst ![a, b, h] S.lam
/-- `c_d`. -/
def co (d : PTm n) : PTm n := Syn.subst ![d] S.c
/-- `s_d`. -/
def sec (d : PTm n) : PTm n := Syn.subst ![d] S.s
/-- `t_d`. -/
def ret (d : PTm n) : PTm n := Syn.subst ![d] S.t

/-- `F(c_d)`. -/
abbrev Fc (F : Fun) (d : PTm n) : PTm n := F.o (S.co d)

/-- The arrow `t_e ∘ (f ∘ s_d) : F(c_d) → F(c_e)` of `D`, for `f : d → e`. -/
def conj (D : Pres) (F : Fun) (d e f : PTm n) : PTm n :=
  D.comp (S.Fc F d) e (S.Fc F e) (S.ret e) (D.comp (S.Fc F d) d e f (S.sec d))

/-- `G(f) = λ(t_e ∘ (f ∘ s_d)) : c_d → c_e` for `f : d → e`. -/
def G (D : Pres) (F : Fun) (d e f : PTm n) : PTm n :=
  S.lift (S.co d) (S.co e) (S.conj D F d e f)

/-- `η_c = λ(t_{F(c)}) : c → c_{F(c)}`. -/
def η (F : Fun) (c : PTm n) : PTm n := S.lift c (S.co (F.o c)) (S.ret (F.o c))

/-- `η_c⁻¹ = λ(s_{F(c)}) : c_{F(c)} → c`. -/
def ηInv (F : Fun) (c : PTm n) : PTm n := S.lift (S.co (F.o c)) c (S.sec (F.o c))

/-- Faithfulness of `F` and the laws of the supplied liftings and splittings. -/
structure Laws (C D : Pres) (F : Fun) : Prop where
  faithful : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b f g : PTm n},
    (Γ ⊢[PRAAx] C.hom a b f) → (Γ ⊢[PRAAx] C.hom a b g) →
    (Γ ⊢[PRAAx] D.eqv (F.o a) (F.o b) (F.m a b f) (F.m a b g)) → (Γ ⊢[PRAAx] C.eqv a b f g)
  lift_hom : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b h : PTm n},
    (Γ ⊢[PRAAx] C.obj a) → (Γ ⊢[PRAAx] C.obj b) → (Γ ⊢[PRAAx] D.hom (F.o a) (F.o b) h) →
      (Γ ⊢[PRAAx] C.hom a b (S.lift a b h))
  lift_eq : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {a b h : PTm n},
    (Γ ⊢[PRAAx] C.obj a) → (Γ ⊢[PRAAx] C.obj b) → (Γ ⊢[PRAAx] D.hom (F.o a) (F.o b) h) →
      (Γ ⊢[PRAAx] D.eqv (F.o a) (F.o b) (F.m a b (S.lift a b h)) h)
  co_obj : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {d : PTm n},
    (Γ ⊢[PRAAx] D.obj d) → (Γ ⊢[PRAAx] C.obj (S.co d))
  sec_hom : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {d : PTm n},
    (Γ ⊢[PRAAx] D.obj d) → (Γ ⊢[PRAAx] D.hom (S.Fc F d) d (S.sec d))
  ret_hom : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {d : PTm n},
    (Γ ⊢[PRAAx] D.obj d) → (Γ ⊢[PRAAx] D.hom d (S.Fc F d) (S.ret d))
  sec_ret : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {d : PTm n},
    (Γ ⊢[PRAAx] D.obj d) →
      (Γ ⊢[PRAAx] D.eqv d d (D.comp d (S.Fc F d) d (S.sec d) (S.ret d)) (D.id1 d))
  ret_sec : ∀ {n : ℕ} {Γ : List (Fm PTm n)} {d : PTm n},
    (Γ ⊢[PRAAx] D.obj d) →
      (Γ ⊢[PRAAx] D.eqv (S.Fc F d) (S.Fc F d) (D.comp (S.Fc F d) d (S.Fc F d) (S.ret d) (S.sec d))
        (D.id1 (S.Fc F d)))

end Split

/-! ## The quasi-inverse functor and the two natural isomorphisms -/

section Equivalence

variable {C D : Pres} (LC : C.Laws) (LD : D.Laws) {F : Fun} (FL : F.Laws C D) {S : Split}
  (SL : S.Laws C D F) {n : ℕ} {Γ : List (Fm PTm n)}

include LD SL in
/-- The lifting respects arrow equality: `F(λ(h)) = h = h' = F(λ(h'))` and `F` is faithful. -/
theorem lift_congr {a b h h' : PTm n} (ha : Γ ⊢[PRAAx] C.obj a) (hb : Γ ⊢[PRAAx] C.obj b)
    (hh : Γ ⊢[PRAAx] D.hom (F.o a) (F.o b) h) (hh' : Γ ⊢[PRAAx] D.hom (F.o a) (F.o b) h')
    (e : Γ ⊢[PRAAx] D.eqv (F.o a) (F.o b) h h') :
    Γ ⊢[PRAAx] C.eqv a b (S.lift a b h) (S.lift a b h') :=
  SL.faithful (SL.lift_hom ha hb hh) (SL.lift_hom ha hb hh')
    (LD.eqv_trans (SL.lift_eq ha hb hh) (LD.eqv_trans e (LD.eqv_symm (SL.lift_eq ha hb hh'))))

include LD SL in
/-- `t_e ∘ (f ∘ s_d) : F(c_d) → F(c_e)`. -/
theorem conj_hom {d e f : PTm n} (hd : Γ ⊢[PRAAx] D.obj d) (he : Γ ⊢[PRAAx] D.obj e)
    (hf : Γ ⊢[PRAAx] D.hom d e f) :
    Γ ⊢[PRAAx] D.hom (S.Fc F d) (S.Fc F e) (S.conj D F d e f) :=
  LD.comp_hom (LD.comp_hom (SL.sec_hom hd) hf) (SL.ret_hom he)

include LD SL in
/-- `G(f) : c_d → c_e`. -/
theorem G_hom {d e f : PTm n} (hd : Γ ⊢[PRAAx] D.obj d) (he : Γ ⊢[PRAAx] D.obj e)
    (hf : Γ ⊢[PRAAx] D.hom d e f) : Γ ⊢[PRAAx] C.hom (S.co d) (S.co e) (S.G D F d e f) :=
  SL.lift_hom (SL.co_obj hd) (SL.co_obj he) (conj_hom LD SL hd he hf)

include LD SL in
/-- `F(G(f)) = t_e ∘ (f ∘ s_d)`. -/
theorem FG_eq {d e f : PTm n} (hd : Γ ⊢[PRAAx] D.obj d) (he : Γ ⊢[PRAAx] D.obj e)
    (hf : Γ ⊢[PRAAx] D.hom d e f) :
    Γ ⊢[PRAAx] D.eqv (S.Fc F d) (S.Fc F e) (F.m (S.co d) (S.co e) (S.G D F d e f))
      (S.conj D F d e f) :=
  SL.lift_eq (SL.co_obj hd) (SL.co_obj he) (conj_hom LD SL hd he hf)

include LD SL in
/-- `G` respects arrow equality. -/
theorem G_congr {d e f f' : PTm n} (hd : Γ ⊢[PRAAx] D.obj d) (he : Γ ⊢[PRAAx] D.obj e)
    (hf : Γ ⊢[PRAAx] D.hom d e f) (hf' : Γ ⊢[PRAAx] D.hom d e f')
    (h : Γ ⊢[PRAAx] D.eqv d e f f') :
    Γ ⊢[PRAAx] C.eqv (S.co d) (S.co e) (S.G D F d e f) (S.G D F d e f') :=
  lift_congr LD SL (SL.co_obj hd) (SL.co_obj he) (conj_hom LD SL hd he hf)
    (conj_hom LD SL hd he hf')
    (LD.comp_congr (LD.comp_congr (LD.eqv_refl (SL.sec_hom hd)) h) (LD.eqv_refl (SL.ret_hom he)))

include LC LD FL SL in
/-- `G(1_d) = 1_{c_d}`: `F(G(1_d)) = t_d ∘ (1_d ∘ s_d) = t_d ∘ s_d = 1 = F(1_{c_d})`. -/
theorem G_id {d : PTm n} (hd : Γ ⊢[PRAAx] D.obj d) :
    Γ ⊢[PRAAx] C.eqv (S.co d) (S.co d) (S.G D F d d (D.id1 d)) (C.id1 (S.co d)) := by
  have hc := SL.co_obj hd
  have hs := SL.sec_hom hd
  have ht := SL.ret_hom hd
  have t₁ := FG_eq LD SL hd hd (LD.id_hom hd)
  have t₂ := LD.comp_congr (LD.id_left hs) (LD.eqv_refl ht)
  have t₃ := SL.ret_sec hd
  have t₄ := LD.eqv_symm (FL.ar_id hc)
  exact SL.faithful (G_hom LD SL hd hd (LD.id_hom hd)) (LC.id_hom hc)
    (LD.eqv_trans t₁ (LD.eqv_trans t₂ (LD.eqv_trans t₃ t₄)))

include LC LD FL SL in
/-- `G(g ∘ f) = G(g) ∘ G(f)`: applying `F`, both sides are `t_k ∘ ((g ∘ f) ∘ s_d)`, because
`s_e ∘ t_e = 1_e`. -/
theorem G_comp {d e k f g : PTm n} (hd : Γ ⊢[PRAAx] D.obj d) (he : Γ ⊢[PRAAx] D.obj e)
    (hk : Γ ⊢[PRAAx] D.obj k) (hf : Γ ⊢[PRAAx] D.hom d e f) (hg : Γ ⊢[PRAAx] D.hom e k g) :
    Γ ⊢[PRAAx] C.eqv (S.co d) (S.co k) (S.G D F d k (D.comp d e k g f))
      (C.comp (S.co d) (S.co e) (S.co k) (S.G D F e k g) (S.G D F d e f)) := by
  have hgf := LD.comp_hom hf hg
  have hGf := G_hom LD SL hd he hf
  have hGg := G_hom LD SL he hk hg
  have hsd := SL.sec_hom hd
  have hse := SL.sec_hom he
  have hte := SL.ret_hom he
  have htk := SL.ret_hom hk
  have hfs := LD.comp_hom hsd hf
  have hgs := LD.comp_hom hse hg
  have hw := conj_hom LD SL hd he hf
  -- (A) `F(G(g ∘ f)) = t_k ∘ ((g ∘ f) ∘ s_d)`
  have A := FG_eq LD SL hd hk hgf
  -- (B) `F(G(g) ∘ G(f)) = F(G(g)) ∘ F(G(f)) = (t_k ∘ (g ∘ s_e)) ∘ (t_e ∘ (f ∘ s_d))`
  have b₁ := FL.ar_comp hGf hGg
  have b₂ := LD.comp_congr (FG_eq LD SL hd he hf) (FG_eq LD SL he hk hg)
  -- `= t_k ∘ ((g ∘ s_e) ∘ (t_e ∘ (f ∘ s_d)))`
  have b₃ := LD.assoc hw hgs htk
  -- `(g ∘ s_e) ∘ (t_e ∘ (f ∘ s_d)) = g ∘ (f ∘ s_d) = (g ∘ f) ∘ s_d`
  have c₁ := cancel_mid LD hfs hte hse hg (SL.sec_ret he)
  have c₂ := LD.eqv_symm (LD.assoc hsd hf hg)
  have b₄ := LD.comp_congr (LD.eqv_trans c₁ c₂) (LD.eqv_refl htk)
  have B := LD.eqv_trans b₁ (LD.eqv_trans b₂ (LD.eqv_trans b₃ b₄))
  exact SL.faithful (G_hom LD SL hd hk hgf) (LC.comp_hom hGf hGg)
    (LD.eqv_trans A (LD.eqv_symm B))

include LD SL in
/-- Naturality of `s`: `s_e ∘ F(G(f)) = s_e ∘ t_e ∘ f ∘ s_d = f ∘ s_d`. -/
theorem sec_nat {d e f : PTm n} (hd : Γ ⊢[PRAAx] D.obj d) (he : Γ ⊢[PRAAx] D.obj e)
    (hf : Γ ⊢[PRAAx] D.hom d e f) :
    Γ ⊢[PRAAx] D.eqv (S.Fc F d) e
      (D.comp (S.Fc F d) (S.Fc F e) e (S.sec e) (F.m (S.co d) (S.co e) (S.G D F d e f)))
      (D.comp (S.Fc F d) d e f (S.sec d)) := by
  have hsd := SL.sec_hom hd
  have hse := SL.sec_hom he
  have hte := SL.ret_hom he
  have hfs := LD.comp_hom hsd hf
  have t₁ := LD.comp_congr (FG_eq LD SL hd he hf) (LD.eqv_refl hse)
  have t₂ := LD.eqv_symm (LD.assoc hfs hte hse)
  have t₃ := LD.comp_congr (LD.eqv_refl hfs) (SL.sec_ret he)
  have t₄ := LD.id_left hfs
  exact LD.eqv_trans t₁ (LD.eqv_trans t₂ (LD.eqv_trans t₃ t₄))

include FL SL in
/-- `η_c : c → c_{F(c)}`. -/
theorem eta_hom {c : PTm n} (hc : Γ ⊢[PRAAx] C.obj c) :
    Γ ⊢[PRAAx] C.hom c (S.co (F.o c)) (S.η F c) :=
  SL.lift_hom hc (SL.co_obj (FL.ob_obj hc)) (SL.ret_hom (FL.ob_obj hc))

include FL SL in
/-- `η_c⁻¹ : c_{F(c)} → c`. -/
theorem etaInv_hom {c : PTm n} (hc : Γ ⊢[PRAAx] C.obj c) :
    Γ ⊢[PRAAx] C.hom (S.co (F.o c)) c (S.ηInv F c) :=
  SL.lift_hom (SL.co_obj (FL.ob_obj hc)) hc (SL.sec_hom (FL.ob_obj hc))

include LC LD FL SL in
/-- `η_c⁻¹ ∘ η_c = 1_c`: applying `F` gives `s_{F(c)} ∘ t_{F(c)} = 1`. -/
theorem etaInv_eta {c : PTm n} (hc : Γ ⊢[PRAAx] C.obj c) :
    Γ ⊢[PRAAx] C.eqv c c (C.comp c (S.co (F.o c)) c (S.ηInv F c) (S.η F c)) (C.id1 c) := by
  have hFc := FL.ob_obj hc
  have hc' := SL.co_obj hFc
  have hη := eta_hom FL SL hc
  have hι := etaInv_hom FL SL hc
  have t₁ := FL.ar_comp hη hι
  have t₂ := LD.comp_congr (SL.lift_eq hc hc' (SL.ret_hom hFc))
    (SL.lift_eq hc' hc (SL.sec_hom hFc))
  have t₃ := SL.sec_ret hFc
  have t₄ := LD.eqv_symm (FL.ar_id hc)
  exact SL.faithful (LC.comp_hom hη hι) (LC.id_hom hc)
    (LD.eqv_trans t₁ (LD.eqv_trans t₂ (LD.eqv_trans t₃ t₄)))

include LC LD FL SL in
/-- `η_c ∘ η_c⁻¹ = 1`: applying `F` gives `t_{F(c)} ∘ s_{F(c)} = 1`. -/
theorem eta_etaInv {c : PTm n} (hc : Γ ⊢[PRAAx] C.obj c) :
    Γ ⊢[PRAAx] C.eqv (S.co (F.o c)) (S.co (F.o c))
      (C.comp (S.co (F.o c)) c (S.co (F.o c)) (S.η F c) (S.ηInv F c)) (C.id1 (S.co (F.o c))) := by
  have hFc := FL.ob_obj hc
  have hc' := SL.co_obj hFc
  have hη := eta_hom FL SL hc
  have hι := etaInv_hom FL SL hc
  have t₁ := FL.ar_comp hι hη
  have t₂ := LD.comp_congr (SL.lift_eq hc' hc (SL.sec_hom hFc))
    (SL.lift_eq hc hc' (SL.ret_hom hFc))
  have t₃ := SL.ret_sec hFc
  have t₄ := LD.eqv_symm (FL.ar_id hc')
  exact SL.faithful (LC.comp_hom hι hη) (LC.id_hom hc')
    (LD.eqv_trans t₁ (LD.eqv_trans t₂ (LD.eqv_trans t₃ t₄)))

include LC LD FL SL in
/-- Naturality of `η`: `η_{c'} ∘ u = G(F(u)) ∘ η_c` for `u : c → c'`. Applying `F`, both
sides are `t_{F(c')} ∘ F(u)`. -/
theorem eta_nat {c c' u : PTm n} (hc : Γ ⊢[PRAAx] C.obj c) (hc' : Γ ⊢[PRAAx] C.obj c')
    (hu : Γ ⊢[PRAAx] C.hom c c' u) :
    Γ ⊢[PRAAx] C.eqv c (S.co (F.o c')) (C.comp c c' (S.co (F.o c')) (S.η F c') u)
      (C.comp c (S.co (F.o c)) (S.co (F.o c')) (S.G D F (F.o c) (F.o c') (F.m c c' u))
        (S.η F c)) := by
  have hFc := FL.ob_obj hc
  have hFc' := FL.ob_obj hc'
  have hFu := FL.ar_hom hu
  have hk := SL.co_obj hFc
  have hk' := SL.co_obj hFc'
  have hη := eta_hom FL SL hc
  have hη' := eta_hom FL SL hc'
  have hG := G_hom LD SL hFc hFc' hFu
  have hs := SL.sec_hom hFc
  have ht := SL.ret_hom hFc
  have ht' := SL.ret_hom hFc'
  have hus := LD.comp_hom hs hFu
  -- (A) `F(η_{c'} ∘ u) = F(η_{c'}) ∘ F(u) = t_{F(c')} ∘ F(u)`
  have a₁ := FL.ar_comp hu hη'
  have a₂ := LD.comp_congr (LD.eqv_refl hFu) (SL.lift_eq hc' hk' ht')
  have A := LD.eqv_trans a₁ a₂
  -- (B) `F(G(F(u)) ∘ η_c) = (t_{F(c')} ∘ (F(u) ∘ s_{F(c)})) ∘ t_{F(c)}`
  have b₁ := FL.ar_comp hη hG
  have b₂ := LD.comp_congr (SL.lift_eq hc hk ht) (FG_eq LD SL hFc hFc' hFu)
  -- `= t_{F(c')} ∘ ((F(u) ∘ s_{F(c)}) ∘ t_{F(c)})`
  have b₃ := LD.assoc ht hus ht'
  -- `(F(u) ∘ s) ∘ t = F(u) ∘ (s ∘ t) = F(u) ∘ 1 = F(u)`
  have c₁ := LD.assoc ht hs hFu
  have c₂ := LD.comp_congr (SL.sec_ret hFc) (LD.eqv_refl hFu)
  have c₃ := LD.id_right hFu
  have b₄ := LD.comp_congr (LD.eqv_trans c₁ (LD.eqv_trans c₂ c₃)) (LD.eqv_refl ht')
  have B := LD.eqv_trans b₁ (LD.eqv_trans b₂ (LD.eqv_trans b₃ b₄))
  exact SL.faithful (LC.comp_hom hu hη') (LC.comp_hom hη hG) (LD.eqv_trans A (LD.eqv_symm B))

end Equivalence

/-! ## An instance: the identity functor with the identity splitting -/

/-- The identity functor. -/
def idFun : Fun where
  ob := var 0
  ar := var 2

/-- The identity splitting of a category `C`: `λ(h) = h`, `c_d = d`, `s_d = t_d = 1_d`. -/
def idSplit (C : Pres) : Split where
  lam := var 2
  c := var 0
  s := C.idt
  t := C.idt

section IdInstance

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem idFun_o (a : PTm n) : idFun.o a = a := by simp [Fun.o, idFun]

theorem idFun_m (a b f : PTm n) : idFun.m a b f = f := by simp [Fun.m, idFun]

theorem idSplit_lift (C : Pres) (a b h : PTm n) : (idSplit C).lift a b h = h := by
  simp [Split.lift, idSplit]

theorem idSplit_co (C : Pres) (d : PTm n) : (idSplit C).co d = d := by simp [Split.co, idSplit]

theorem idSplit_sec (C : Pres) (d : PTm n) : (idSplit C).sec d = C.id1 d := rfl

theorem idSplit_ret (C : Pres) (d : PTm n) : (idSplit C).ret d = C.id1 d := rfl

/-- The identity functor satisfies the functor laws. -/
theorem idFun_laws {C : Pres} (L : C.Laws) : idFun.Laws C C where
  ob_obj := fun h => by rw [idFun_o]; exact h
  ar_hom := fun h => by rw [idFun_o, idFun_o, idFun_m]; exact h
  ar_congr := fun h => by rw [idFun_o, idFun_o, idFun_m, idFun_m]; exact h
  ar_id := fun h => by rw [idFun_o, idFun_m]; exact L.eqv_refl (L.id_hom h)
  ar_comp := fun h₁ h₂ => by
    simp only [idFun_o, idFun_m]
    exact L.eqv_refl (L.comp_hom h₁ h₂)

/-- The identity splitting satisfies the laws of a splitting of the identity functor. -/
theorem idSplit_laws {C : Pres} (L : C.Laws) : (idSplit C).Laws C C idFun where
  faithful := fun _ _ h => by
    simp only [idFun_o, idFun_m] at h
    exact h
  lift_hom := fun _ _ h => by
    simp only [idFun_o] at h
    rw [idSplit_lift]; exact h
  lift_eq := fun _ _ h => by
    simp only [idFun_o] at h
    simp only [idFun_o, idFun_m, idSplit_lift]
    exact L.eqv_refl h
  co_obj := fun h => by rw [idSplit_co]; exact h
  sec_hom := fun h => by
    simp only [Split.Fc, idFun_o, idSplit_co, idSplit_sec]
    exact L.id_hom h
  ret_hom := fun h => by
    simp only [Split.Fc, idFun_o, idSplit_co, idSplit_ret]
    exact L.id_hom h
  sec_ret := fun h => by
    simp only [Split.Fc, idFun_o, idSplit_co, idSplit_sec, idSplit_ret]
    exact L.id_left (L.id_hom h)
  ret_sec := fun h => by
    simp only [Split.Fc, idFun_o, idSplit_co, idSplit_sec, idSplit_ret]
    exact L.id_left (L.id_hom h)

/-- For the identity splitting of the additive monoid, the functor `G` preserves composition:
a closed sentence of iPRA with all hypotheses discharged. Variables: `0 = d`, `1 = e`, `2 = k`,
`3 = f`, `4 = g`. -/
theorem G_comp_natAdd : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (natAdd.obj (var 0) ⟶ natAdd.obj (var 1) ⟶ natAdd.obj (var 2) ⟶
      natAdd.hom (var 0) (var 1) (var 3) ⟶ natAdd.hom (var 1) (var 2) (var 4) ⟶
      natAdd.eqv ((idSplit natAdd).co (var 0)) ((idSplit natAdd).co (var 2))
        ((idSplit natAdd).G natAdd idFun (var 0) (var 2)
          (natAdd.comp (var 0) (var 1) (var 2) (var 4) (var 3)))
        (natAdd.comp ((idSplit natAdd).co (var 0)) ((idSplit natAdd).co (var 1))
          ((idSplit natAdd).co (var 2))
          ((idSplit natAdd).G natAdd idFun (var 1) (var 2) (var 4))
          ((idSplit natAdd).G natAdd idFun (var 0) (var 1) (var 3)))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI
    (G_comp natAdd_laws natAdd_laws (idFun_laws natAdd_laws) (idSplit_laws natAdd_laws)
      (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0))))))

end IdInstance

end LeanProofs.IPRA.Foundations.SplitEquivalence
