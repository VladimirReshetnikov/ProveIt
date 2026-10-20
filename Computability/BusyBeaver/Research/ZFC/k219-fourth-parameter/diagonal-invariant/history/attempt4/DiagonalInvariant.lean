import BusyBeaver.ZFC.Code254

/-! A syntactic MP-closed invariant for the exact U=R(A,B) modification.
All identities and quantified monotonicity are freely admitted in the invariant.
The bundle core may be ANY Q-headed code, so the exact seed/support core is covered.
No unrestricted propositional basis, renaming or substitution theorem is used. -/
namespace K219Diagonal
open SetTheory SetTheory.BusyBeaver.ZFC.Code254
abbrev I := wim
abbrev R := wel
abbrev Q := wal
abbrev E := weq

@[simp] theorem tagI (a b : Nat) : I a b % 4 = 0 := by simp [I, wim]
@[simp] theorem tagR (a b : Nat) : R a b % 4 = 1 := by simp [R, wel, Nat.add_mod]
@[simp] theorem tagQ (a b : Nat) : Q a b % 4 = 2 := by simp [Q, wal, Nat.add_mod]
@[simp] theorem tagE (a b : Nat) : E a b % 4 = 3 := by simp [E, weq, Nat.add_mod]
theorem pair_inj {a b c d : Nat} (h : P a b = P c d) : a=c ∧ b=d := by
  have hh := congrArg Cantor.ofNat h
  simpa only [unP_P, Prod.mk.injEq] using hh
theorem i_inj {a b c d : Nat} (h : I a b = I c d) : a=c ∧ b=d := by
  apply pair_inj
  simp only [I, wim] at h
  omega
theorem q_inj {a b c d : Nat} (h : Q a b = Q c d) : a=c ∧ b=d := by
  apply pair_inj
  simp only [Q, wal] at h
  omega
theorem i_left (a b : Nat) : a ≤ I a b := by
  have := le_P_left a b
  simp only [I,wim]
  omega
theorem r_gt (a b : Nat) : a < R a b := by
  have := le_P_left a b
  simp only [R,wel]
  omega
theorem r_one {a b : Nat} (h : R a b = 1) : a=0 ∧ b=0 := by
  have hp : P a b = 0 := by simp only [R,wel] at h; omega
  exact P_eq_zero hp
@[simp] theorem i_zero : I 0 0 = 0 := by simp [I,wim,P,Cantor.toNat,Cantor.tri]
@[simp] theorem r_zero : R 0 0 = 1 := by simp [R,wel,P,Cantor.toNat,Cantor.tri]

-- Constructor-tag disjointness, including literal falsum.
private theorem ne_tag {a b : Nat} (h : a%4 ≠ b%4) : a≠b := fun e => h (congrArg (·%4) e)
@[simp] theorem iq (a b c d : Nat) : I a b ≠ Q c d := ne_tag (by simp)
@[simp] theorem qi (a b c d : Nat) : Q a b ≠ I c d := ne_tag (by simp)
@[simp] theorem ie (a b c d : Nat) : I a b ≠ E c d := ne_tag (by simp)
@[simp] theorem ei (a b c d : Nat) : E a b ≠ I c d := ne_tag (by simp)
@[simp] theorem ir (a b c d : Nat) : I a b ≠ R c d := ne_tag (by simp)
@[simp] theorem ri (a b c d : Nat) : R a b ≠ I c d := ne_tag (by simp)
@[simp] theorem qe (a b c d : Nat) : Q a b ≠ E c d := ne_tag (by simp)
@[simp] theorem eqn (a b c d : Nat) : E a b ≠ Q c d := ne_tag (by simp)
@[simp] theorem qr (a b c d : Nat) : Q a b ≠ R c d := ne_tag (by simp)
@[simp] theorem rq (a b c d : Nat) : R a b ≠ Q c d := ne_tag (by simp)
@[simp] theorem i1 (a b : Nat) : I a b ≠ 1 := ne_tag (by simp)
@[simp] theorem q1 (a b : Nat) : Q a b ≠ 1 := ne_tag (by simp)
@[simp] theorem e1 (a b : Nat) : E a b ≠ 1 := ne_tag (by simp)

def V (a b c : Nat) := I (R a b) (Q c (R a b))
def H (a b c : Nat) := I (I (I c (R a b)) a) (I (I a c) (I b c))
def X (i p : Nat) := I (Q i (I (Q i p) 1)) 1

inductive Ax where
 | r1 (i j : Nat) | r2 (i p q : Nat) | r3 (a b c : Nat)
 | r4 (i j p : Nat) | r5 (a b c : Nat) | r6 (i p : Nat)
 | g (a b u : Nat) | h (a b c : Nat)
 | bundle (a b c k d : Nat)

def Ax.code : Ax → Nat
 | .r1 i j => I (Q i (I (E i j) 1)) 1
 | .r2 i p q => I (Q i (I p q)) (I (Q i p) (Q i q))
 | .r3 a b c => I (E a b) (I (R c a) (R c b))
 | .r4 i j p => I (Q i (Q j p)) (Q j (Q i p))
 | .r5 a b c => I (E c a) (I (R c b) (R a b))
 | .r6 i p => I (X i p) p
 | .g a b u => I (E u a) (I (E u b) (Q (R a b) (E a b)))
 | .h a b c => H a b c
 | .bundle a b c k d => I (I (V a b c) (Q k d)) 1

@[simp] theorem ax_tag (x : Ax) : x.code % 4 = 0 := by cases x <;> simp [Ax.code,H]

inductive Safe : Nat → Prop
 | ax (x : Ax) : Safe x.code
 | refl (x : Nat) : Safe (I x x)
 | gen (i : Nat) {p : Nat} : Safe p → Safe (Q i p)
 | mono (i : Nat) {p q : Nat} : Safe (I p q) → Safe (I (Q i p) (Q i q))

theorem safe_tag {n : Nat} (h : Safe n) : n%4=0 ∨ n%4=2 := by
 cases h <;> simp

theorem q_strip {n : Nat} (h : Safe n) : ∀ i p, n = Q i p → Safe p := by
 cases h with
 | ax x => intro i p he; have ht := congrArg (·%4) he; simp at ht
 | refl x => intro i p he; exact False.elim (iq _ _ _ _ he)
 | gen j hp => intro i p he; obtain ⟨rfl,rfl⟩ := q_inj he; exact hp
 | mono j hp => intro i p he; exact False.elim (iq _ _ _ _ he)

theorem imp_cases {n : Nat} (h : Safe n) : ∀ a b, n = I a b →
    (∃ x : Ax, x.code = I a b) ∨ a=b ∨
    (∃ i p q, a=Q i p ∧ b=Q i q ∧ Safe (I p q)) := by
 cases h with
 | ax x => intro a b he; exact .inl ⟨x,he⟩
 | refl x => intro a b he; obtain ⟨rfl,rfl⟩ := i_inj he; exact .inr (.inl rfl)
 | gen j hp => intro a b he; exact False.elim (qi _ _ _ _ he)
 | @mono j p q hp =>
   intro a b he
   obtain ⟨rfl,rfl⟩ := i_inj he
   exact .inr (.inr ⟨j,p,q,rfl,rfl,hp⟩)

theorem no_eq_neg (i j : Nat) : ¬ Safe (I (E i j) 1) := by
 intro h
 rcases imp_cases h _ _ rfl with ⟨x,he⟩ | he | ⟨k,p,q,he,_,_⟩
 · cases x <;> simp only [Ax.code,H,X] at he <;>
     obtain ⟨ha,hb⟩ := i_inj he <;> simp_all
 · exact e1 i j he
 · exact eqn i j k p he

theorem no_ex_all (i p : Nat) : ¬ Safe (X i p) := by
 intro h
 rcases imp_cases h _ _ rfl with ⟨x,he⟩ | he | ⟨k,u,v,_,he,_⟩
 · cases x <;> simp only [Ax.code,H,X] at he <;>
     obtain ⟨ha,hb⟩ := i_inj he <;> simp_all
   obtain ⟨rfl,hq⟩ := q_inj ha
   obtain ⟨heq,_⟩ := i_inj hq
   exact eqn _ _ _ _ heq
 · exact q1 _ _ he
 · exact q1 k v he.symm

theorem no_bundle_minor (a b c k d : Nat) :
    ¬ Safe (I (V a b c) (Q k d)) := by
 intro h
 rcases imp_cases h _ _ rfl with ⟨x,he⟩ | he | ⟨j,p,q,he,_,_⟩
 · cases x <;> simp only [Ax.code,H,X,V] at he <;>
     obtain ⟨ha,hb⟩ := i_inj he <;> simp_all
   all_goals obtain ⟨hc,hd⟩ := i_inj ha; simp_all
 · exact iq _ _ _ _ he
 · exact iq _ _ _ _ he

theorem trigger (a b c : Nat) (h : Safe (I (I c (R a b)) a)) : a=0 ∧ b=0 := by
 rcases imp_cases h _ _ rfl with ⟨x,he⟩ | he | ⟨j,p,q,he,_,_⟩
 · cases x <;> simp only [Ax.code,H,X,V] at he <;>
     obtain ⟨ha,hb⟩ := i_inj he <;> simp_all
   · obtain ⟨hc,hd⟩ := i_inj ha
     exact r_one hd.symm
   · rename_i x y z
     obtain ⟨hc,hd⟩ := i_inj ha
     have hlt := r_gt a b
     have hle1 := i_left (I x z) (I y z)
     have hle2 := i_left x z
     omega
   · obtain ⟨hc,hd⟩ := i_inj ha
     exact False.elim (qr _ _ _ _ hd)
 · have hright : R a b ≤ I c (R a b) := by
     have := le_P_right c (R a b)
     simp only [I,wim]
     omega
   have hlt := r_gt a b
   omega
 · exact False.elim (iq _ _ _ _ he)

theorem safe_mp {n : Nat} (hm : Safe n) : ∀ p q, n=I p q → Safe p → Safe q := by
 induction hm with
 | ax x =>
   intro p q he hp
   cases x <;> simp only [Ax.code,H] at he <;>
     obtain ⟨rfl,rfl⟩ := i_inj he
   · exact False.elim (no_eq_neg _ _ (q_strip hp _ _ rfl))
   · exact Safe.mono _ (q_strip hp _ _ rfl)
   · have ht := safe_tag hp; simp at ht
   · exact Safe.gen _ (Safe.gen _ (q_strip (q_strip hp _ _ rfl) _ _ rfl))
   · have ht := safe_tag hp; simp at ht
   · exact False.elim (no_ex_all _ _ hp)
   · have ht := safe_tag hp; simp at ht
   · obtain ⟨rfl,rfl⟩ := trigger _ _ _ hp
     exact Safe.refl _
   · exact False.elim (no_bundle_minor _ _ _ _ _ hp)
 | refl x =>
   intro p q he hp
   obtain ⟨rfl,rfl⟩ := i_inj he
   exact hp
 | gen i _ _ => intro p q he _; exact False.elim (qi _ _ _ _ he)
 | @mono i u v huv ih =>
   intro p q he hp
   obtain ⟨rfl,rfl⟩ := i_inj he
   exact Safe.gen i (ih u v rfl (q_strip hp i u rfl))

inductive Prov : Nat → Prop
 | truth : Prov 0
 | ax (x : Ax) : Prov x.code
 | mp {a b : Nat} : Prov (I a b) → Prov a → Prov b
 | gen (i : Nat) {p : Nat} : Prov p → Prov (Q i p)

theorem prov_safe {n : Nat} (h : Prov n) : Safe n := by
 induction h with
 | truth => simpa using Safe.refl 0
 | ax x => exact Safe.ax x
 | mp _ _ ih1 ih2 => exact safe_mp ih1 _ _ rfl ih2
 | gen i _ ih => exact Safe.gen i ih

theorem no_falsum : ¬ Prov 1 := by
 intro h
 have ht := safe_tag (prov_safe h)
 simp at ht

/-- The semantic implication-to-truth law already fails at the literal falsum code. -/
theorem no_falsum_to_truth : ¬ Prov (wim 1 0) := by
 intro h
 have hs := prov_safe h
 rcases imp_cases hs _ _ rfl with ⟨x,he⟩ | he | ⟨k,p,q,he,_,_⟩
 · cases x <;> simp only [Ax.code,H,X] at he <;>
     obtain ⟨ha,hb⟩ := i_inj he <;> simp_all
 · contradiction
 · exact q1 k p he.symm

-- Exact binding to imported native rows. The native r1 and r6 expand Ex and N.
theorem bind_r1 (i j : Nat) : (Ax.r1 i j).code = rho1 i j := rfl
theorem bind_r2 (i p q : Nat) : (Ax.r2 i p q).code = rho2 i p q := rfl
theorem bind_r3 (a b c : Nat) : (Ax.r3 a b c).code = rho3 a b c := rfl
theorem bind_r4 (i j p : Nat) : (Ax.r4 i j p).code = rho4 i j p := rfl
theorem bind_r5 (a b c : Nat) : (Ax.r5 a b c).code = rho5 a b c := rfl
theorem bind_r6 (i p : Nat) : (Ax.r6 i p).code = rho6 i p := rfl
theorem bind_r8 (a b c : Nat) : (Ax.h a b c).code = rho8 a b c (wel a b) := rfl
/-- Literal expression of KCode222.growG; that uncached module is not imported. -/
theorem bind_g (a b u : Nat) : (Ax.g a b u).code =
    wim (weq u a) (wim (weq u b) (wal (wel a b) (weq a b))) := rfl
/-- Includes the exact seed bundle with k=c and d=clos(a,b,c,c)→N req(b,c,c). -/
theorem bind_bundle (a b c k d : Nat) : (Ax.bundle a b c k d).code =
    wn (wim (wim (wel a b) (wal c (wel a b))) (wal k d)) := rfl

#print axioms safe_mp
#print axioms no_falsum
#print axioms no_falsum_to_truth
#print axioms bind_r1
#print axioms bind_r2
#print axioms bind_r3
#print axioms bind_r4
#print axioms bind_r5
#print axioms bind_r6
#print axioms bind_r8
#print axioms bind_g
#print axioms bind_bundle
end K219Diagonal
