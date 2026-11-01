import BusyBeaver.ZFC.Code254

/-!
Finite proof syntax and an executable natural-number checker for exact C254.

RawProof records all twelve rules and their numeric fields. Its structural
validator checks recursive premises, the exact MP formula, and both bundle
freshness inequalities. Positive base12 tags and Cantor payloads quote trees;
an explicitly fuel-bounded parser reads untrusted natural numbers.

This is an external coding theorem. There is no PA representation/totality
proof, proof-data-to-enumerator compiler, or new machine endpoint. The original
calculus is Mira-Cult's, as attributed in the imported Code254 module.
-/

namespace SetTheory.BusyBeaver.ZFC.Code254Proof
open Code254

/-- Finite, unindexed data; a raw tree is not necessarily a valid proof. -/
inductive RawProof where
  | truth
  | mp (output : Nat) (minor major : RawProof)
  | gen (binder : Nat) (premise : RawProof)
  | r1 (a b : Nat)
  | r2 (a b c : Nat)
  | r3 (a b c : Nat)
  | r4 (a b c : Nat)
  | r5 (a b c : Nat)
  | r6 (a b : Nat)
  | r7 (a b c : Nat)
  | r8 (a b c u : Nat)
  | bundle (a b c : Nat)

def RawProof.conclusion : RawProof → Nat
  | .truth => 0
  | .mp b _ _ => b
  | .gen a p => wal a p.conclusion
  | .r1 a b => rho1 a b
  | .r2 a b c => rho2 a b c
  | .r3 a b c => rho3 a b c
  | .r4 a b c => rho4 a b c
  | .r5 a b c => rho5 a b c
  | .r6 a b => rho6 a b
  | .r7 a b c => rho7 a b c
  | .r8 a b c u => rho8 a b c u
  | .bundle a b c => Code254.bundle a b c

/-- All children are validated; MP compares its exact major formula, and
bundle checks c!=a and c!=b. There is no extra theory-membership oracle. -/
def RawProof.valid : RawProof → Bool
  | .truth => true
  | .mp b p q => p.valid && (q.valid && decide (q.conclusion = wim p.conclusion b))
  | .gen _ p => p.valid
  | .bundle a b c => decide (c ≠ a) && decide (c ≠ b)
  | _ => true

theorem RawProof.sound (p : RawProof) : p.valid = true → C254 p.conclusion := by
  induction p with
  | truth => intro _; exact .truth
  | mp b p q ihp ihq =>
    intro h
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .mp (ihp h.1) (h.2.2 ▸ ihq h.2.1)
  | gen a p ih => intro h; exact .gen a (ih h)
  | r1 a b => intro _; exact .r1 a b
  | r2 a b c => intro _; exact .r2 a b c
  | r3 a b c => intro _; exact .r3 a b c
  | r4 a b c => intro _; exact .r4 a b c
  | r5 a b c => intro _; exact .r5 a b c
  | r6 a b => intro _; exact .r6 a b
  | r7 a b c => intro _; exact .r7 a b c
  | r8 a b c u => intro _; exact .r8 a b c u
  | bundle a b c =>
    intro h
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .bundle a b c h.1 h.2

/-- Prop elimination produces existence of finite data, not a chosen
computation inspecting a proposition-valued derivation. -/
theorem rawProof_exists {n : Nat} (h : C254 n) :
    ∃ p : RawProof, p.valid = true ∧ p.conclusion = n := by
  induction h with
  | truth => exact ⟨.truth, rfl, rfl⟩
  | @mp t b _ _ ihp ihq =>
    obtain ⟨p, hp, hpn⟩ := ihp
    obtain ⟨q, hq, hqn⟩ := ihq
    exact ⟨.mp b p q, by simp [RawProof.valid, hp, hq, hpn, hqn], rfl⟩
  | gen a _ ih =>
    obtain ⟨p, hp, hpn⟩ := ih
    exact ⟨.gen a p, hp, by simp only [RawProof.conclusion, hpn]⟩
  | r1 a b => exact ⟨.r1 a b, rfl, rfl⟩
  | r2 a b c => exact ⟨.r2 a b c, rfl, rfl⟩
  | r3 a b c => exact ⟨.r3 a b c, rfl, rfl⟩
  | r4 a b c => exact ⟨.r4 a b c, rfl, rfl⟩
  | r5 a b c => exact ⟨.r5 a b c, rfl, rfl⟩
  | r6 a b => exact ⟨.r6 a b, rfl, rfl⟩
  | r7 a b c => exact ⟨.r7 a b c, rfl, rfl⟩
  | r8 a b c u => exact ⟨.r8 a b c u, rfl, rfl⟩
  | bundle a b c hca hcb => exact ⟨.bundle a b c, by simp [RawProof.valid, hca, hcb], rfl⟩

/-- Zero is invalid; tag0/payload0 is proof code1 for formula code0. -/
def node (tag payload : Nat) : Nat := 12 * payload + tag + 1

def RawProof.quote : RawProof → Nat
  | .truth => node 0 0
  | .mp b p q => node 1 (P b (P p.quote q.quote))
  | .gen a p => node 2 (P a p.quote)
  | .r1 a b => node 3 (P a b)
  | .r2 a b c => node 4 (P a (P b c))
  | .r3 a b c => node 5 (P a (P b c))
  | .r4 a b c => node 6 (P a (P b c))
  | .r5 a b c => node 7 (P a (P b c))
  | .r6 a b => node 8 (P a b)
  | .r7 a b c => node 9 (P a (P b c))
  | .r8 a b c u => node 10 (P a (P b (P c u)))
  | .bundle a b c => node 11 (P a (P b c))

def RawProof.height : RawProof → Nat
  | .mp _ p q => max p.height q.height + 1
  | .gen _ p => p.height + 1
  | _ => 1

/-- Parse one constructor; validity is checked separately after parsing. -/
def decodeStep (rec : Nat → Option RawProof) (tag payload : Nat) : Option RawProof :=
  let a := (Cantor.ofNat payload).1
  let tail := (Cantor.ofNat payload).2
  let b := (Cantor.ofNat tail).1
  let c := (Cantor.ofNat tail).2
  match tag with
  | 0 => if payload = 0 then some .truth else none
  | 1 => do
      let p ← rec b
      let q ← rec c
      pure (.mp a p q)
  | 2 => do
      let p ← rec tail
      pure (.gen a p)
  | 3 => some (.r1 a tail)
  | 4 => some (.r2 a b c)
  | 5 => some (.r3 a b c)
  | 6 => some (.r4 a b c)
  | 7 => some (.r5 a b c)
  | 8 => some (.r6 a tail)
  | 9 => some (.r7 a b c)
  | 10 => some (.r8 a b (Cantor.ofNat c).1 (Cantor.ofNat c).2)
  | 11 => some (.bundle a b c)
  | _ => none

/-- Total parser with an explicit depth bound; zero and truncated trees fail. -/
def decodeFuel : Nat → Nat → Option RawProof
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, z + 1 => decodeStep (decodeFuel fuel) (z % 12) (z / 12)

theorem decode_node (fuel tag payload : Nat) (ht : tag < 12) :
    decodeFuel (fuel + 1) (node tag payload) = decodeStep (decodeFuel fuel) tag payload := by
  have hm : (12 * payload + tag) % 12 = tag := by omega
  have hd : (12 * payload + tag) / 12 = payload := by omega
  simp only [node, decodeFuel, hm, hd]

theorem RawProof.height_le_quote (p : RawProof) : p.height ≤ p.quote := by
  induction p with
  | truth => simp [height, quote, node]
  | mp b p q ihp ihq =>
    have hp := le_P_left p.quote q.quote
    have hq := le_P_right p.quote q.quote
    have hb := le_P_right b (P p.quote q.quote)
    simp only [height, quote, node]
    omega
  | gen a p ih =>
    have hp := le_P_right a p.quote
    simp only [height, quote, node]
    omega
  | r1 a b => simp [height, quote, node]
  | r2 a b c => simp [height, quote, node]
  | r3 a b c => simp [height, quote, node]
  | r4 a b c => simp [height, quote, node]
  | r5 a b c => simp [height, quote, node]
  | r6 a b => simp [height, quote, node]
  | r7 a b c => simp [height, quote, node]
  | r8 a b c u => simp [height, quote, node]
  | bundle a b c => simp [height, quote, node]

/-- Exact parser roundtrip for every raw tree, including invalid proofs. -/
theorem RawProof.decode_quote (p : RawProof) :
    ∀ fuel, p.height ≤ fuel → decodeFuel fuel p.quote = some p := by
  induction p with
  | truth =>
    intro fuel hf
    cases fuel with
    | zero => simp [height] at hf
    | succ fuel => simp [quote, decode_node, decodeStep]
  | mp b p q ihp ihq =>
    intro fuel hf
    cases fuel with
    | zero => simp [height] at hf
    | succ fuel =>
      have hp : p.height ≤ fuel := by simp only [height] at hf; omega
      have hq : q.height ≤ fuel := by simp only [height] at hf; omega
      simp [quote, decode_node, decodeStep, unP_P, ihp fuel hp, ihq fuel hq]
  | gen a p ih =>
    intro fuel hf
    cases fuel with
    | zero => simp [height] at hf
    | succ fuel =>
      have hp : p.height ≤ fuel := by simp only [height] at hf; omega
      simp [quote, decode_node, decodeStep, unP_P, ih fuel hp]
  | r1 a b =>
    intro fuel hf
    cases fuel <;> simp_all [height, quote, decode_node, decodeStep, unP_P]
  | r2 a b c =>
    intro fuel hf
    cases fuel <;> simp_all [height, quote, decode_node, decodeStep, unP_P]
  | r3 a b c =>
    intro fuel hf
    cases fuel <;> simp_all [height, quote, decode_node, decodeStep, unP_P]
  | r4 a b c =>
    intro fuel hf
    cases fuel <;> simp_all [height, quote, decode_node, decodeStep, unP_P]
  | r5 a b c =>
    intro fuel hf
    cases fuel <;> simp_all [height, quote, decode_node, decodeStep, unP_P]
  | r6 a b =>
    intro fuel hf
    cases fuel <;> simp_all [height, quote, decode_node, decodeStep, unP_P]
  | r7 a b c =>
    intro fuel hf
    cases fuel <;> simp_all [height, quote, decode_node, decodeStep, unP_P]
  | r8 a b c u =>
    intro fuel hf
    cases fuel <;> simp_all [height, quote, decode_node, decodeStep, unP_P]
  | bundle a b c =>
    intro fuel hf
    cases fuel <;> simp_all [height, quote, decode_node, decodeStep, unP_P]

/-- Parse first, then validate every rule and the requested conclusion. -/
def check (code n : Nat) : Bool :=
  match decodeFuel (code + 1) code with
  | none => false
  | some p => p.valid && decide (p.conclusion = n)

theorem check_sound {code n : Nat} (h : check code n = true) : C254 n := by
  unfold check at h
  cases he : decodeFuel (code + 1) code with
  | none => simp [he] at h
  | some p =>
    simp only [he, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2 ▸ p.sound h.1

theorem RawProof.check_quote (p : RawProof) :
    check p.quote p.conclusion = p.valid := by
  unfold check
  rw [p.decode_quote (p.quote + 1) (by have := p.height_le_quote; omega)]
  simp

/-- Exact external numerical coding of the original C254 relation. -/
theorem c254_iff_checked (n : Nat) : C254 n ↔ ∃ code, check code n = true := by
  constructor
  · intro h
    obtain ⟨p, hp, hpn⟩ := rawProof_exists h
    exact ⟨p.quote, by rw [← hpn, p.check_quote]; exact hp⟩
  · rintro ⟨code, h⟩
    exact check_sound h

theorem reject_zero (n : Nat) : check 0 n = false := rfl

theorem accept_truth : check 1 0 = true := by decide

end SetTheory.BusyBeaver.ZFC.Code254Proof
