import Mathlib.Data.Nat.Pairing

/-!
The complete Tree submodule from AnnotatedProofCode.lean at e73fa2e916c9,
with decoder-graph.patch applied. Original executable definitions and
all original declarations are retained. Only the surrounding unrelated
checker imports, outer opens and declarations are excluded in this test.
-/
namespace DiophantineConsistency.AnnotatedProofCode

inductive Tree where
  | atom (n : Nat)
  | fork (left right : Tree)
  deriving DecidableEq, Repr

namespace Tree

def quote : Tree → Nat
  | atom n => Nat.pair 0 n+1
  | fork a b => Nat.pair (quote a+1) (quote b)+1

def depth : Tree → Nat
  | atom _ => 1
  | fork a b => max a.depth b.depth+1

/-- Fuel zero and code zero are rejected. Every recursive code is smaller. -/
def decode : Nat → Nat → Option Tree
  | 0, _ => none
  | _+1, 0 => none
  | fuel+1, code+1 =>
    let p := Nat.unpair code
    match p.1 with
    | 0 => some (atom p.2)
    | left+1 => do
      let a ← decode fuel left
      let b ← decode fuel p.2
      pure (fork a b)

theorem depth_le_quote (t : Tree) : t.depth≤t.quote := by
  induction t with
  | atom n => simp only [depth,quote]; omega
  | fork a b ha hb =>
    have hl := Nat.left_le_pair (a.quote+1) b.quote
    have hr := Nat.right_le_pair (a.quote+1) b.quote
    simp only [depth,quote]
    omega

theorem decode_quote (t : Tree) (fuel : Nat) (hf : t.depth≤fuel) :
    decode fuel t.quote=some t := by
  induction t generalizing fuel with
  | atom n =>
    cases fuel with
    | zero => simp [depth] at hf
    | succ fuel => simp [quote,decode]
  | fork a b ha hb =>
    cases fuel with
    | zero => simp [depth] at hf
    | succ fuel =>
      have hfa : a.depth≤fuel := by simp only [depth] at hf; omega
      have hfb : b.depth≤fuel := by simp only [depth] at hf; omega
      simp [quote,decode,ha fuel hfa,hb fuel hfb]

/-- A fixed, total parser; the input itself supplies a sufficient fuel bound. -/
def parse (code : Nat) : Option Tree := decode code code

@[simp] theorem parse_quote (t : Tree) : parse t.quote=some t :=
  decode_quote t t.quote (depth_le_quote t)

theorem decoded_spec {fuel code : Nat} {t : Tree}
    (h : decode fuel code=some t) : t.quote=code ∧ t.depth≤fuel := by
  induction fuel generalizing code t with
  | zero => simp [decode] at h
  | succ fuel ih =>
    cases code with
    | zero => simp [decode] at h
    | succ code =>
      have hp := Nat.pair_unpair code
      simp only [decode] at h
      cases he : (Nat.unpair code).1 with
      | zero =>
        simp only [he] at h hp
        cases h
        exact ⟨by simp only [quote,hp], by simp [depth]⟩
      | succ left =>
        simp only [he] at h hp
        change (decode fuel left).bind (fun a =>
          (decode fuel (Nat.unpair code).2).bind (fun b => some (fork a b))) = some t at h
        simp only [Option.bind_eq_some_iff,Option.some.injEq] at h
        obtain ⟨a,ha,b,hb,rfl⟩ := h
        obtain ⟨hqa,hda⟩ := ih ha
        obtain ⟨hqb,hdb⟩ := ih hb
        exact ⟨by simp only [quote,hqa,hqb,hp], by simp only [depth]; omega⟩

/-- The old API remains available by projection. -/
theorem decoded_depth_le {fuel code : Nat} {t : Tree}
    (h : decode fuel code=some t) : t.depth≤fuel := (decoded_spec h).2

theorem quote_of_decode {fuel code : Nat} {t : Tree}
    (h : decode fuel code=some t) : t.quote=code := (decoded_spec h).1

theorem decode_eq_some_iff (fuel code : Nat) (t : Tree) :
    decode fuel code=some t ↔ t.quote=code ∧ t.depth≤fuel := by
  constructor
  · exact decoded_spec
  · rintro ⟨rfl,hf⟩
    exact decode_quote t fuel hf

theorem quote_injective : Function.Injective quote := by
  intro a b h
  have hh := congrArg parse h
  simpa only [parse_quote,Option.some.injEq] using hh

theorem decode_quote_iff (t u : Tree) (fuel : Nat) :
    decode fuel t.quote=some u ↔ u=t ∧ t.depth≤fuel := by
  rw [decode_eq_some_iff,quote_injective.eq_iff]
  exact and_congr_right (fun h => by rw [h])

theorem decode_quote_none_of_lt (t : Tree) (fuel : Nat) (h : fuel<t.depth) :
    decode fuel t.quote=none := by
  cases hh : decode fuel t.quote with
  | none => rfl
  | some u =>
    have hf := (decode_quote_iff t u fuel).mp hh
    omega

def quoteList {α : Type} (f : α → Tree) : List α → Tree
  | [] => atom 0
  | a::as => fork (f a) (quoteList f as)

def parseList {α : Type} (f : Tree → Option α) : Tree → Option (List α)
  | atom 0 => some []
  | fork a as => do
    let x ← f a
    let xs ← parseList f as
    pure (x::xs)
  | _ => none

@[simp] theorem parseList_quoteList {α : Type} (q : α → Tree) (p : Tree → Option α)
    (h : ∀ a,p (q a)=some a) (as : List α) :
    parseList p (quoteList q as)=some as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [quoteList,parseList,h a,ih]

def tagged (tag : Nat) (fields : List Tree) : Tree :=
  fork (atom tag) (quoteList id fields)

def untagged : Tree → Option (Nat × List Tree)
  | fork (atom tag) fields => do
    let fields ← parseList some fields
    pure (tag,fields)
  | _ => none

@[simp] theorem untagged_tagged (tag : Nat) (fields : List Tree) :
    untagged (tagged tag fields)=some (tag,fields) := by
  simp [tagged,untagged,parseList_quoteList id some (fun _ => rfl)]

def parseNat : Tree → Option Nat
  | atom n => some n
  | _ => none

@[simp] theorem parseNat_atom (n : Nat) : parseNat (atom n)=some n := rfl

end Tree
#print axioms Tree.decoded_spec
#print axioms Tree.decode_eq_some_iff
#print axioms Tree.decode_quote_iff
end DiophantineConsistency.AnnotatedProofCode
