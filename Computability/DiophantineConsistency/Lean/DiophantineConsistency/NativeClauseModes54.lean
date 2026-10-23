import DiophantineConsistency.NativeClause54

/-! # The compact54 receiver-mode labels and exact local clause decoder -/

namespace DiophantineConsistency.NativeClauseModes54

open NativeClause54

set_option maxRecDepth 4000

structure Label where
  west : ℕ
  north : ℕ
  east : ℕ
  south : ℕ
  deriving DecidableEq

structure InRange (t : Label) : Prop where
  west_lt : t.west < 1024
  north_lt : t.north < 1024
  east_lt : t.east < 1024
  south_lt : t.south < 1024

inductive Kind where
  | ordinary
  | rightReceiver
  | leftReceiver
  deriving DecidableEq

def rightLabel : Label := ⟨256,0,0,512⟩
def leftLabel : Label := ⟨0,0,512,512⟩

def ValidMode : Kind → Label → Prop
  | .ordinary,t => InRange t
  | .rightReceiver,t => t = rightLabel
  | .leftReceiver,t => t = leftLabel

def rightFlag : Kind → ℕ | .rightReceiver => 1 | _ => 0
def leftFlag : Kind → ℕ | .leftReceiver => 1 | _ => 0

def Allowed : Kind → ℕ → ℕ → ℕ → Prop
  | .ordinary,QR,QL,u => QR = 0 ∧ QL = 0 ∧ u = 0
  | .rightReceiver,_,QL,_ => QL = 0
  | .leftReceiver,QR,_,_ => QR = 0

def encode (t : Label) : ℕ :=
  2 * t.west + 2 ^ 11 * t.north + 2 ^ 21 * (2 * t.east) + 2 ^ 32 * t.south

def expanded (t : Label) (QR QL u : ℕ) : Label :=
  ⟨t.west+QR,t.north+u,t.east+QL,t.south+2*QR+2*QL+u⟩

theorem encode_expanded (t : Label) (QR QL u : ℕ) :
    encode (expanded t QR QL u) = encode t + auxiliary QR QL u := by
  unfold encode expanded auxiliary
  ring

theorem encode_even (t : Label) : encode t % 2 = 0 := by
  unfold encode
  omega

theorem encode_lt {t : Label} (ht : InRange t) : encode t < labelBase := by
  obtain ⟨hw,hn,he,hs⟩ := ht
  unfold encode labelBase
  norm_num
  omega

theorem allowed_of_gate_bounds {kind : Kind} {QR QL u : ℕ}
    (hR : rightGate 1 (rightFlag kind) QR < 256)
    (hL : leftGate 1 (leftFlag kind) QL < 256)
    (hu : commonGate 1 (rightFlag kind) (leftFlag kind) u < 2) :
    Allowed kind QR QL u := by
  cases kind <;> simp only [rightFlag,leftFlag,rightGate,leftGate,commonGate,Allowed] at * <;> omega

theorem gate_bounds_of_allowed {kind : Kind} {QR QL u : ℕ}
    (ha : Allowed kind QR QL u) (hQR : QR < 256) (hQL : QL < 256) (hu : u ≤ 1) :
    rightGate 1 (rightFlag kind) QR < 256 ∧ leftGate 1 (leftFlag kind) QL < 256 ∧
      commonGate 1 (rightFlag kind) (leftFlag kind) u < 2 := by
  cases kind <;> simp only [rightFlag,leftFlag,rightGate,leftGate,commonGate,Allowed] at * <;> omega

/-- Valid receiver payloads fit the four original edge fields. -/
theorem expanded_inRange {kind : Kind} {t : Label} {QR QL u : ℕ}
    (ht : ValidMode kind t) (ha : Allowed kind QR QL u)
    (hQR : QR < 256) (hQL : QL < 256) (hu : u ≤ 1) :
    InRange (expanded t QR QL u) := by
  cases kind with
  | ordinary =>
    change InRange t at ht
    obtain ⟨hR,hL,hU⟩ := ha
    subst QR QL u
    simpa [expanded] using ht
  | rightReceiver =>
    change t = rightLabel at ht
    change QL = 0 at ha
    subst t QL
    constructor <;> simp only [expanded,rightLabel] <;> omega
  | leftReceiver =>
    change t = leftLabel at ht
    change QR = 0 at ha
    subst t QR
    constructor <;> simp only [expanded,leftLabel] <;> omega

def localClause (kind : Kind) (t : Label) (n QR QL u Z y A1 A2 : ℕ) : ℕ :=
  pack n (rightGate n (n * rightFlag kind) QR) (leftGate n (n * leftFlag kind) QL)
    (commonGate n (n * rightFlag kind) (n * leftFlag kind) u)
    (payload n (n * encode t) (auxiliary QR QL u) Z y A1 A2)

attribute [local irreducible] pack payload payloadModulus labelBase auxiliary encode
  rightGate leftGate commonGate

/-- Exact local acceptance, including every receiver bit in an empty cell.
The ignored dummy digits do not occur in this clause. -/
theorem local_clause_iff {kind : Kind} {t : Label} {n QR QL u Z y A1 A2 : ℕ}
    (ht : ValidMode kind t) (hn : n < 512) (hQR : QR < 256) (hQL : QL < 256) (hu : u ≤ 1)
    (hZ : Z < labelBase) (hZbit : Z % 2 = y) (hy : y ≤ 1) (hA1 : A1 ≤ 1) (hA2 : A2 ≤ 1) :
    localClause kind t n QR QL u Z y A1 A2 &&& clauseMask = 0 ↔
      (n = 0 ∧ QR = 0 ∧ QL = 0 ∧ u = 0 ∧ Z = 0 ∧ y = 0 ∧ A1 = 0 ∧ A2 = 0) ∨
      (n = 1 ∧ Allowed kind QR QL u ∧ y = 1 ∧ A1 = 1 ∧ A2 = 1 ∧
        encode (expanded t QR QL u) + Z = labelBase - 1) := by
  constructor
  · intro hmask
    obtain ⟨hn1,hR,hL,hU,hP,_⟩ := gate_sound hn hQR hQL hu hmask
    have hallowed (hnEq : n = 1) : Allowed kind QR QL u := by
      subst n
      simpa only [one_mul] using allowed_of_gate_bounds (by simpa using hR)
        (by simpa using hL) (by simpa using hU)
    have hLV (hnEq : n = 1) : n * encode t + auxiliary QR QL u < labelBase := by
      have hrange := expanded_inRange ht (hallowed hnEq) hQR hQL hu
      have he := encode_lt hrange
      rw [encode_expanded] at he
      simpa only [hnEq,one_mul] using he
    have hLeven : (n * encode t) % 2 = 0 := by
      rw [Nat.mul_mod,encode_even]
      simp
    obtain hzero | hocc := (aggregate_iff hn1 (by intro h; rw [h,zero_mul]) hLV
      (auxiliary_lt hQR hQL hu) hZ hLeven (auxiliary_even QR QL u) hZbit hy hA1 hA2).mp hP
    · obtain ⟨hn,_,hV,hZ,hy,hA1,hA2⟩ := hzero
      obtain ⟨hQR,hQL,hu⟩ := (auxiliary_eq_zero_iff QR QL u).mp hV
      exact Or.inl ⟨hn,hQR,hQL,hu,hZ,hy,hA1,hA2⟩
    · obtain ⟨hn,hy,hA1,hA2,hcomp⟩ := hocc
      refine Or.inr ⟨hn,hallowed hn,hy,hA1,hA2,?_⟩
      simpa only [hn,one_mul,encode_expanded] using hcomp
  · rintro (⟨hn,hQR,hQL,hu,hZ,hy,hA1,hA2⟩ | ⟨hn,ha,hy,hA1,hA2,hcomp⟩)
    · subst_vars
      simp [localClause,pack,rightGate,leftGate,commonGate,payload,auxiliary]
    · subst n A1 A2
      rw [hy]
      obtain ⟨hR,hL,hU⟩ := gate_bounds_of_allowed ha hQR hQL hu
      have hP : payload 1 (encode t) (auxiliary QR QL u) Z 1 1 1 = payloadModulus := by
        rw [encode_expanded] at hcomp
        calc _ = 1 + (encode t + auxiliary QR QL u + Z) + 3 * labelBase := by
              unfold payload
              ring
          _ = 1 + (labelBase - 1) + 3 * labelBase := by rw [hcomp]
          _ = payloadModulus := by unfold labelBase payloadModulus; decide
      unfold localClause
      simp only [one_mul]
      apply (masked_fields_iff (n := 1) (gr := rightGate 1 (rightFlag kind) QR)
        (gl := leftGate 1 (leftFlag kind) QL) (gu := commonGate 1 (rightFlag kind) (leftFlag kind) u)
        (P := payload 1 (encode t) (auxiliary QR QL u) Z 1 1 1)
        (by decide : 1 < 512) (by omega) (by omega) (by omega)).mpr
      refine ⟨by decide,(clear_top_bit_iff (k := 8) (by omega)).mpr hR,
        (clear_top_bit_iff (k := 8) (by omega)).mpr hL,
        (clear_top_bit_iff (k := 1) (by omega)).mpr hU,?_⟩
      exact (congrArg (fun z : ℕ => z % payloadModulus) hP).trans (Nat.mod_self payloadModulus)

end DiophantineConsistency.NativeClauseModes54
