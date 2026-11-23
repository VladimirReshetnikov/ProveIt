import Std

/-!
A deep first-order negative translation.  Binders use de Bruijn indices.
Variadic function symbols take a syntactic argument list. The operations preserve
the usual arity-correct signature fragment; the derivation transformer itself
works on all raw terms.
The two structural constructors wk and up below are admissible transformations
in the positional calculus of the paper.  Natural numbers range over free slots,
so scope is an external invariant. No classical principles are used.
-/
namespace FOLNegative

mutual
  inductive Term where
    | var (i : Nat)
    | fn (f : Nat) (xs : Args)
  inductive Args where
    | nil
    | cons (x : Term) (xs : Args)
end

deriving instance DecidableEq for Term, Args
deriving instance Repr for Term, Args

mutual
  def Term.shift (k : Nat) : Term → Term
    | .var i => .var (if i < k then i else i+1)
    | .fn f xs => .fn f (xs.shift k)
  def Args.shift (k : Nat) : Args → Args
    | .nil => .nil
    | .cons x xs => .cons (x.shift k) (xs.shift k)
end

mutual
  def Term.plug (t : Term) (k : Nat) (s : Term) : Term :=
    match t with
    | .var i => if i < k then .var i else if i = k then s else .var (i-1)
    | .fn f xs => .fn f (xs.plug k s)
  def Args.plug (xs : Args) (k : Nat) (s : Term) : Args :=
    match xs with
    | .nil => .nil
    | .cons x ys => .cons (x.plug k s) (ys.plug k s)
end

mutual
  theorem Term.fresh (t : Term) (k : Nat) :
      (t.shift (k+1)).plug k (.var k) = t := by
    match t with
    | .var i =>
      by_cases h : i < k
      · simp [Term.shift, Term.plug, h, show i < k+1 by omega]
      · by_cases e : i = k
        · subst i; simp [Term.shift, Term.plug]
        · simp [Term.shift, Term.plug, show ¬ i < k+1 by omega,
            show ¬ i+1 < k by omega, show i+1 ≠ k by omega]
    | .fn f xs => simp [Term.shift, Term.plug, Args.fresh xs k]
  theorem Args.fresh (xs : Args) (k : Nat) :
      (xs.shift (k+1)).plug k (.var k) = xs := by
    match xs with
    | .nil => rfl
    | .cons t ts => simp [Args.shift, Args.plug, Term.fresh t k, Args.fresh ts k]
end

inductive F where
  | rel (p : Nat) (args : List Term)
  | eq (s t : Term)
  | bot
  | conj (a b : F)
  | disj (a b : F)
  | arr (a b : F)
  | all (a : F)
  | ex (a : F)
deriving DecidableEq, Repr


infixr:45 " ⇒ᶠ " => F.arr
def neg (a : F) := a ⇒ᶠ .bot
def J (a : F) := neg (neg a)

def F.shift (k : Nat) : F → F
  | .rel p ts => .rel p (ts.map (Term.shift k))
  | .eq s t => .eq (s.shift k) (t.shift k)
  | .bot => .bot
  | .conj a b => .conj (a.shift k) (b.shift k)
  | .disj a b => .disj (a.shift k) (b.shift k)
  | .arr a b => .arr (a.shift k) (b.shift k)
  | .all a => .all (a.shift (k+1))
  | .ex a => .ex (a.shift (k+1))

def F.plug (k : Nat) (s : Term) : F → F
  | .rel p ts => .rel p (ts.map (fun t => t.plug k s))
  | .eq t u => .eq (t.plug k s) (u.plug k s)
  | .bot => .bot
  | .conj a b => .conj (a.plug k s) (b.plug k s)
  | .disj a b => .disj (a.plug k s) (b.plug k s)
  | .arr a b => .arr (a.plug k s) (b.plug k s)
  | .all a => .all (a.plug (k+1) (s.shift 0))
  | .ex a => .ex (a.plug (k+1) (s.shift 0))

theorem F.fresh (a : F) (k : Nat) :
    (a.shift (k+1)).plug k (.var k) = a := by
  induction a generalizing k <;>
    simp_all [F.shift, F.plug, List.map_map, Function.comp_def,
      Term.fresh, Term.shift]

def N : F → F
  | .rel p ts => J (.rel p ts)
  | .eq s t => J (.eq s t)
  | .bot => .bot
  | .conj a b => .conj (N a) (N b)
  | .disj a b => J (.disj (N a) (N b))
  | .arr a b => .arr (N a) (N b)
  | .all a => .all (N a)
  | .ex a => J (.ex (N a))

theorem N_shift (a : F) (k : Nat) : N (a.shift k) = (N a).shift k := by
  induction a generalizing k <;> simp_all [N, F.shift, J, neg]

theorem N_plug (a : F) (k : Nat) (s : Term) :
    N (a.plug k s) = (N a).plug k s := by
  induction a generalizing k s <;> simp_all [N, F.plug, J, neg]

abbrev liftC (Γ : List F) := Γ.map (F.shift 0)
abbrev trC (Γ : List F) := Γ.map N

theorem ctx_comm (Γ : List F) : trC (liftC Γ) = liftC (trC Γ) := by
  simp [trC, liftC, List.map_map, Function.comp_def, N_shift]

/-- Typed rule trees; mode false is intuitionistic and mode true is classical. -/
inductive D (c : Bool) : List F → F → Type where
  | hyp : a ∈ Γ → D c Γ a
  | wk : (∀ x, x ∈ Γ → x ∈ Δ) → D c Γ a → D c Δ a
  | up : D c Γ a → D c (liftC Γ) (a.shift 0)
  | down : D c (liftC Γ) (a.shift 0) → D c Γ a
  | botE : D c Γ .bot → D c Γ a
  | arrI : D c (a::Γ) b → D c Γ (a ⇒ᶠ b)
  | arrE : D c Γ (a ⇒ᶠ b) → D c Γ a → D c Γ b
  | conjI : D c Γ a → D c Γ b → D c Γ (.conj a b)
  | conjL : D c Γ (.conj a b) → D c Γ a
  | conjR : D c Γ (.conj a b) → D c Γ b
  | disjL : D c Γ a → D c Γ (.disj a b)
  | disjR : D c Γ b → D c Γ (.disj a b)
  | disjE : D c Γ (.disj a b) → D c (a::Γ) t → D c (b::Γ) t → D c Γ t
  | allI : D c (liftC Γ) a → D c Γ (.all a)
  | allE (s : Term) : D c Γ (.all a) → D c Γ (a.plug 0 s)
  | exI (s : Term) : D c Γ (a.plug 0 s) → D c Γ (.ex a)
  | exE : D c Γ (.ex a) → D c (a::liftC Γ) (b.shift 0) → D c Γ b
  | refl (s : Term) : D c Γ (.eq s s)
  | eqE (b : F) : D c Γ (.eq s t) → D c Γ (b.plug 0 s) → D c Γ (b.plug 0 t)
  | dne : c = true → D c Γ (J a) → D c Γ a

def headD : D c (a::Γ) a := .hyp (by simp)

def addD (a : F) (d : D c Γ b) : D c (a::Γ) b :=
  .wk (fun _ h => List.mem_cons_of_mem _ h) d

def insertD (a : F) (d : D c (b::Γ) t) : D c (b::a::Γ) t :=
  .wk (fun _ h => by
    cases h with
    | head => exact .head _
    | tail _ hx => exact .tail _ (.tail _ hx)) d

def unitJ (d : D c Γ a) : D c Γ (J a) :=
  .arrI (.arrE headD (addD _ d))

def mapJ (f : D c Γ (a ⇒ᶠ b)) (h : D c Γ (J a)) : D c Γ (J b) :=
  .arrI (.arrE (addD _ h) (.arrI (.arrE (addD _ headD)
    (.arrE (addD _ (addD _ f)) headD))))

def joinJ (d : D c Γ (J (J a))) : D c Γ (J a) :=
  .arrI (.arrE (addD _ d) (.arrI (.arrE headD (addD _ headD))))

def instFresh (d : D c Γ (.all a)) : D c (liftC Γ) a := by
  have e := D.allE (.var 0) (D.up d)
  simpa [F.shift, F.fresh] using e

/-- Negative formulas admit double-negation elimination in intuitionistic deduction. -/
def stable (a : F) {Γ : List F} (d : D false Γ (J (N a))) : D false Γ (N a) :=
  match a with
  | .rel _ _ | .eq _ _ | .disj _ _ | .ex _ => joinJ d
  | .bot => .arrE d (.arrI headD)
  | .conj a b =>
    .conjI (stable a (mapJ (.arrI (.conjL headD)) d))
      (stable b (mapJ (.arrI (.conjR headD)) d))
  | .arr _ b =>
    .arrI (stable b (mapJ (.arrI (.arrE headD (addD _ headD))) (addD _ d)))
  | .all a => by
    apply D.allI
    apply stable a
    apply mapJ (a := F.all ((N a).shift 1))
    · apply D.arrI
      have e := D.allE (.var 0) (headD (c := false) (a := F.all ((N a).shift 1))
        (Γ := liftC Γ))
      simpa [F.fresh] using e
    · exact D.up d


/-- An intuitionistic certificate for the negative translation of a proof
in either source calculus. Each branch is a constructive rule-tree builder. -/
def translate (d : D c Γ a) : D false (trC Γ) (N a) := by
  match d with
  | .hyp h => exact .hyp (List.mem_map_of_mem h)
  | .wk f h =>
    apply D.wk _ (translate h)
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map_of_mem (f y hy)
  | .up h => simpa only [ctx_comm, N_shift] using D.up (translate h)
  | .down h => apply D.down; simpa only [ctx_comm, N_shift] using translate h
  | .botE h => exact .botE (translate h)
  | .arrI h => exact .arrI (translate h)
  | .arrE f x => exact .arrE (translate f) (translate x)
  | .conjI x y => exact .conjI (translate x) (translate y)
  | .conjL x => exact .conjL (translate x)
  | .conjR x => exact .conjR (translate x)
  | .disjL x => exact unitJ (.disjL (translate x))
  | .disjR x => exact unitJ (.disjR (translate x))
  | .disjE h l r =>
    apply stable _
    exact mapJ (.arrI (.disjE headD (insertD _ (translate l)) (insertD _ (translate r))))
      (translate h)
  | .allI h =>
    apply D.allI
    simpa only [ctx_comm] using translate h
  | .allE s h =>
    simpa only [N_plug] using D.allE s (translate h)
  | .exI s h =>
    apply unitJ
    apply D.exI s
    simpa only [N_plug] using translate h
  | .exE h k =>
    apply stable _
    apply mapJ _ (translate h)
    apply D.arrI
    apply D.exE headD
    apply insertD
    simpa only [trC, List.map_cons, ctx_comm, N_shift, List.map_map,
      Function.comp_def] using translate k
  | .refl s => exact unitJ (.refl s)
  | .eqE b eq minor =>
    apply stable _
    apply mapJ _ (translate eq)
    apply D.arrI
    rw [N_plug]
    apply D.eqE (N b) headD
    apply addD
    simpa only [N_plug] using translate minor
  | .dne _ h => exact stable _ (translate h)
termination_by structural d



def packFresh (d : D c Γ a) : D c Γ ((F.ex a).shift 0) := by
  apply D.exI (.var 0)
  simpa [F.fresh] using d

mutual
  /-- In the classical calculus, a formula entails its translation. -/
  def toN (a : F) {Γ : List F} (h : D true Γ a) : D true Γ (N a) :=
    match a with
    | .rel _ _ | .eq _ _ => unitJ h
    | .bot => h
    | .conj a b => .conjI (toN a (.conjL h)) (toN b (.conjR h))
    | .disj a b =>
      .disjE h (unitJ (.disjL (toN a headD))) (unitJ (.disjR (toN b headD)))
    | .arr a b => .arrI (toN b (.arrE (addD _ h) (ofN a headD)))
    | .all a => .allI (toN a (instFresh h))
    | .ex a => .exE h (unitJ (packFresh (toN a headD)))

  /-- In the classical calculus, the translation entails the original formula. -/
  def ofN (a : F) {Γ : List F} (h : D true Γ (N a)) : D true Γ a :=
    match a with
    | .rel _ _ | .eq _ _ => .dne rfl h
    | .bot => h
    | .conj a b => .conjI (ofN a (.conjL h)) (ofN b (.conjR h))
    | .disj a b =>
      .disjE (.dne rfl h) (.disjL (ofN a headD)) (.disjR (ofN b headD))
    | .arr a b => .arrI (ofN b (.arrE (addD _ h) (toN a headD)))
    | .all a => .allI (ofN a (instFresh h))
    | .ex a => .exE (.dne rfl h) (packFresh (ofN a headD))
end

/-- Read any proof as a proof in the classical extension. -/
def promote (d : D c Γ a) : D true Γ a :=
  match d with
  | .hyp h => .hyp h
  | .wk f h => .wk f (promote h)
  | .up h => .up (promote h)
  | .down h => .down (promote h)
  | .botE h => .botE (promote h)
  | .arrI h => .arrI (promote h)
  | .arrE f x => .arrE (promote f) (promote x)
  | .conjI h k => .conjI (promote h) (promote k)
  | .conjL h => .conjL (promote h)
  | .conjR h => .conjR (promote h)
  | .disjL h => .disjL (promote h)
  | .disjR h => .disjR (promote h)
  | .disjE h l r => .disjE (promote h) (promote l) (promote r)
  | .allI h => .allI (promote h)
  | .allE s h => .allE s (promote h)
  | .exI s h => .exI s (promote h)
  | .exE h k => .exE (promote h) (promote k)
  | .refl s => .refl s
  | .eqE b h k => .eqE b (promote h) (promote k)
  | .dne _ h => .dne rfl (promote h)

/-- Recover a proof in the original context by discharging translated
assumptions, then supplying their translations from original assumptions. -/
def originalContext (Γ : List F) {a : F} (h : D true (trC Γ) a) : D true Γ a :=
  match Γ with
  | [] => h
  | t :: ts => .arrE (addD t (originalContext ts (.arrI h))) (toN t headD)

/-- Reverse direction for typed proof trees. -/
def recover (h : D false (trC Γ) (N a)) : D true Γ a :=
  ofN a (originalContext Γ (promote h))

theorem negative_translation_iff (Γ : List F) (a : F) :
    Nonempty (D true Γ a) ↔ Nonempty (D false (trC Γ) (N a)) :=
  ⟨fun ⟨d⟩ => ⟨translate d⟩, fun ⟨d⟩ => ⟨recover d⟩⟩

theorem equiconsistency :
    (¬ Nonempty (D true [] .bot)) ↔ (¬ Nonempty (D false [] .bot)) :=
  not_congr (negative_translation_iff [] .bot)


/-! Tarskian semantics and soundness of exactly the rule trees above. -/
structure Model (ι : Type) where
  func : Nat → List ι → ι
  pred : Nat → List ι → Prop

def consE (x : ι) (e : Nat → ι) : Nat → ι
  | 0 => x
  | i+1 => e i

def insE (e : Nat → ι) (k : Nat) (x : ι) (i : Nat) : ι :=
  if i < k then e i else if i = k then x else e (i-1)

theorem insE_zero (e : Nat → ι) (x : ι) : insE e 0 x = consE x e := by
  funext i
  cases i <;> simp [insE, consE]

theorem insE_succ (e : Nat → ι) (k : Nat) (x y : ι) :
    insE (consE y e) (k+1) x = consE y (insE e k x) := by
  funext i
  cases i with
  | zero => simp [insE, consE]
  | succ i =>
    by_cases h : i < k
    · simp [insE, consE, h]
    · by_cases he : i = k
      · subst i; simp [insE, consE]
      · cases i <;> simp_all [insE, consE] <;> omega

mutual
  def tv (M : Model ι) (e : Nat → ι) : Term → ι
    | .var i => e i
    | .fn f xs => M.func f (av M e xs)
  def av (M : Model ι) (e : Nat → ι) : Args → List ι
    | .nil => []
    | .cons t ts => tv M e t :: av M e ts
end

mutual
  theorem tv_shift (M : Model ι) (e : Nat → ι) (k : Nat) (x : ι) (t : Term) :
      tv M (insE e k x) (t.shift k) = tv M e t := by
    match t with
    | .var i =>
      by_cases h : i < k
      · simp [Term.shift, tv, insE, h]
      · simp [Term.shift, tv, insE, h, show ¬i+1 < k by omega, show i+1≠k by omega]
    | .fn f xs => simp [Term.shift, tv, av_shift M e k x xs]
  theorem av_shift (M : Model ι) (e : Nat → ι) (k : Nat) (x : ι) (ts : Args) :
      av M (insE e k x) (ts.shift k) = av M e ts := by
    match ts with
    | .nil => rfl
    | .cons t ts => simp [Args.shift, av, tv_shift M e k x t, av_shift M e k x ts]
end

mutual
  theorem tv_plug (M : Model ι) (e : Nat → ι) (k : Nat) (s t : Term) :
      tv M e (t.plug k s) = tv M (insE e k (tv M e s)) t := by
    match t with
    | .var i =>
      by_cases h : i < k
      · simp [Term.plug, tv, insE, h]
      · by_cases h' : i = k <;> simp [Term.plug, tv, insE, h, h']
    | .fn f xs => simp [Term.plug, tv, av_plug M e k s xs]
  theorem av_plug (M : Model ι) (e : Nat → ι) (k : Nat) (s : Term) (ts : Args) :
      av M e (ts.plug k s) = av M (insE e k (tv M e s)) ts := by
    match ts with
    | .nil => rfl
    | .cons t ts => simp [Args.plug, av, tv_plug M e k s t, av_plug M e k s ts]
end

def Sat (M : Model ι) (e : Nat → ι) : F → Prop
  | .rel p ts => M.pred p (ts.map (tv M e))
  | .eq s t => tv M e s = tv M e t
  | .bot => False
  | .conj a b => Sat M e a ∧ Sat M e b
  | .disj a b => Sat M e a ∨ Sat M e b
  | .arr a b => Sat M e a → Sat M e b
  | .all a => ∀ x, Sat M (consE x e) a
  | .ex a => ∃ x, Sat M (consE x e) a

theorem sat_shift (M : Model ι) (e : Nat → ι) (k : Nat) (x : ι) (a : F) :
    Sat M (insE e k x) (a.shift k) ↔ Sat M e a := by
  induction a generalizing e k <;>
    simp_all [Sat, F.shift, List.map_map, Function.comp_def, tv_shift, ← insE_succ]

theorem tv_shift0 (M : Model ι) (e : Nat → ι) (x : ι) (s : Term) :
    tv M (consE x e) (s.shift 0) = tv M e s := by
  simpa only [insE_zero] using tv_shift M e 0 x s

theorem sat_plug (M : Model ι) (e : Nat → ι) (k : Nat) (s : Term) (a : F) :
    Sat M e (a.plug k s) ↔ Sat M (insE e k (tv M e s)) a := by
  induction a generalizing e k s <;>
    simp_all [Sat, F.plug, List.map_map, Function.comp_def, tv_plug, tv_shift0, insE_succ]

abbrev CtxSat (M : Model ι) (e : Nat → ι) (Γ : List F) :=
  ∀ a ∈ Γ, Sat M e a

theorem ctxCons {M : Model ι} {e : Nat → ι} (ha : Sat M e a)
    (hΓ : CtxSat M e Γ) : CtxSat M e (a::Γ) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · exact hΓ b hb

theorem sat_shift0 (M : Model ι) (e : Nat → ι) (x : ι) (a : F) :
    Sat M (consE x e) (a.shift 0) ↔ Sat M e a := by
  simpa only [insE_zero] using sat_shift M e 0 x a

theorem sat_plug0 (M : Model ι) (e : Nat → ι) (s : Term) (a : F) :
    Sat M e (a.plug 0 s) ↔ Sat M (consE (tv M e s) e) a := by
  simpa only [insE_zero] using sat_plug M e 0 s a

theorem ctxLift (M : Model ι) (e : Nat → ι) (x : ι) (Γ : List F) :
    CtxSat M (consE x e) (liftC Γ) ↔ CtxSat M e Γ := by
  constructor
  · intro h a ha
    exact (sat_shift0 ..).mp (h _ (List.mem_map_of_mem ha))
  · intro h b hb
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hb
    subst b
    exact (sat_shift0 ..).mpr (h _ ha)

/-- For arbitrary intuitionistic truth values this covers mode false.
In mode true, stability of satisfaction is a parameter, discharged below
by computation for finite decidable structures. -/
theorem sound (M : Model ι) (nonempty : ι) (d : D c Γ a)
    (st : c = true → ∀ e b, (¬¬ Sat M e b) → Sat M e b) :
    ∀ e, CtxSat M e Γ → Sat M e a := by
  induction d with
  | hyp h => exact fun _ hΓ => hΓ _ h
  | wk f _ ih => exact fun _ hΓ => ih _ (fun b hb => hΓ b (f b hb))
  | up _ ih =>
    intro e hΓ
    have eta : e = consE (e 0) (fun i => e (i+1)) := by funext i; cases i <;> rfl
    rw [eta] at hΓ ⊢
    exact (sat_shift0 ..).mpr (ih _ ((ctxLift ..).mp hΓ))
  | down _ ih =>
    exact fun e hΓ => (sat_shift0 ..).mp (ih (consE nonempty e) ((ctxLift ..).mpr hΓ))
  | botE _ ih => exact fun e hΓ => False.elim (ih e hΓ)
  | arrI _ ih => exact fun e hΓ h => ih e (ctxCons h hΓ)
  | arrE _ _ f x => exact fun e hΓ => f e hΓ (x e hΓ)
  | conjI _ _ a b => exact fun e hΓ => ⟨a e hΓ, b e hΓ⟩
  | conjL _ h => exact fun e hΓ => (h e hΓ).1
  | conjR _ h => exact fun e hΓ => (h e hΓ).2
  | disjL _ h => exact fun e hΓ => Or.inl (h e hΓ)
  | disjR _ h => exact fun e hΓ => Or.inr (h e hΓ)
  | disjE _ _ _ h left right =>
    intro e hΓ
    rcases h e hΓ with l | r
    · exact left e (ctxCons l hΓ)
    · exact right e (ctxCons r hΓ)
  | allI _ ih => exact fun e hΓ x => ih _ ((ctxLift M e x _).mpr hΓ)
  | allE s _ ih => exact fun e hΓ => (sat_plug0 ..).mpr (ih e hΓ (tv M e s))
  | exI s _ ih => exact fun e hΓ => ⟨tv M e s, (sat_plug0 ..).mp (ih e hΓ)⟩
  | exE _ _ ex branch =>
    intro e hΓ
    obtain ⟨x, hx⟩ := ex e hΓ
    exact (sat_shift0 ..).mp (branch (consE x e) (ctxCons hx ((ctxLift ..).mpr hΓ)))
  | refl _ => exact fun _ _ => rfl
  | @eqE _ s t b _ _ eq minor =>
    intro e hΓ
    have he : tv M e s = tv M e t := eq e hΓ
    apply (sat_plug0 ..).mpr
    rw [← he]
    exact (sat_plug0 ..).mp (minor e hΓ)
  | dne enabled _ ih => exact fun e hΓ => st enabled e _ (ih e hΓ)

def decideSat {n : Nat} (M : Model (Fin n))
    (relDec : ∀ p xs, Decidable (M.pred p xs)) (a : F) (e : Nat → Fin n) :
    Decidable (Sat M e a) :=
  match a with
  | .rel p ts => relDec p (ts.map (tv M e))
  | .eq s t => inferInstanceAs (Decidable (tv M e s = tv M e t))
  | .bot => inferInstanceAs (Decidable False)
  | .conj b d =>
    letI := decideSat M relDec b e
    letI := decideSat M relDec d e
    inferInstanceAs (Decidable (Sat M e b ∧ Sat M e d))
  | .disj b d =>
    letI := decideSat M relDec b e
    letI := decideSat M relDec d e
    inferInstanceAs (Decidable (Sat M e b ∨ Sat M e d))
  | .arr b d =>
    letI := decideSat M relDec b e
    letI := decideSat M relDec d e
    inferInstanceAs (Decidable (Sat M e b → Sat M e d))
  | .all b =>
    letI := fun x => decideSat M relDec b (consE x e)
    inferInstanceAs (Decidable (∀ x, Sat M (consE x e) b))
  | .ex b =>
    letI := fun x => decideSat M relDec b (consE x e)
    inferInstanceAs (Decidable (∃ x, Sat M (consE x e) b))

theorem finite_sound {n : Nat} (M : Model (Fin (n+1)))
    (relDec : ∀ p xs, Decidable (M.pred p xs)) (d : D c Γ a)
    (e : Nat → Fin (n+1)) (hΓ : CtxSat M e Γ) : Sat M e a :=
  sound M 0 d (fun _ ρ b h => by
    cases decideSat M relDec b ρ with
    | isTrue h' => exact h'
    | isFalse h' => exact False.elim (h h')) e hΓ

theorem consistency (c : Bool) : ¬Nonempty (D c [] .bot) := by
  rintro ⟨d⟩
  let M : Model (Fin 1) := ⟨fun _ _ => 0, fun _ _ => False⟩
  exact finite_sound (n := 0) M (fun _ _ => isFalse id) d (fun _ => 0) (by simp [CtxSat])

end FOLNegative

