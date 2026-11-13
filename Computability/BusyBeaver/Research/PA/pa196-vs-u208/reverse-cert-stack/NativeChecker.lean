import CertificateStack

/-!
Direct natural-number implementation of the PA196 proof checker row/fuel
recurrence. This is a transcription to be connected to imported model-valued
`Checker.verifyValue`; that equality has not yet been proved here.
-/
namespace PA196CertificateStack.NativeChecker
open PA196CertificateStack.Cantor PA196CertificateStack.Native

def left (n : Nat) : Nat := (decode n).1
def right (n : Nat) : Nat := (decode n).2

/-- Numeric counterpart of the imported `CheckerRule.rule`. -/
def rule (previous : Nat → Nat) (tag payload : Nat) : Nat :=
  let r1 := right payload
  let r2 := right r1
  let r3 := right r2
  let r4 := right r3
  let a := left payload
  let b := left r1
  let c := left r2
  let u := left r3
  match tag with
  | 0 => if r3 = 0 then
      let minor := previous b
      let major := previous c
      if minor = 0 then 0 else if major = 0 then 0
      else if major = I (minor-1) a + 1 then a+1 else 0
    else 0
  | 1 => if r2 = 0 then
      let minor := previous b
      if minor = 0 then 0 else U a (minor-1)+1
    else 0
  | 2 => if r2 = 0 then head1 a b+1 else 0
  | 3 => if r3 = 0 then head2 a b c+1 else 0
  | 4 => if r3 = 0 then head3 a b c+1 else 0
  | 5 => if r3 = 0 then head4 a b c+1 else 0
  | 6 => if r2 = 0 then head5 a b+1 else 0
  | 7 => if r3 = 0 then head6 a b c+1 else 0
  | 8 => if r4 = 0 then if u ≤ a then rho8 a b c u+1 else 0 else 0
  | 9 => if r3 = 0 then if c = a then 0 else if c = b then 0 else bundle a b c+1 else 0
  | _ => 0

/-- Entry of the bounded checker table after the indicated fuel. -/
def entry : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel+1, bound, tree =>
      if tree ≤ bound then
        rule (entry fuel bound) (left tree) (right tree)
      else 0

def verify (code : Nat) : Nat := entry (left code) (right code) (right code)
def cert (proof formula : Nat) : Prop := verify proof = formula+1

theorem verify_leaf (tag payload : Nat) :
    verify (leaf tag payload) = rule (fun _ => 0) tag payload := by
  simp [verify, leaf, entry, left, right, decode_pair]

end PA196CertificateStack.NativeChecker

namespace PA196CertificateStack.NativeChecker
open PA196CertificateStack.Cantor PA196CertificateStack.Native

theorem truth : cert 739 0 := by
  have ht : leaf 8 (pack4 0 0 0 0) = 739 := by decide
  rw [← ht]
  simp [cert, verify_leaf, rule, pack4, pack3, pack2, left, right,
    rho8, I, pair, triangle, decode]

theorem head1_ok (D H : Nat) : cert (leaf 2 (pack2 D H)) (head1 D H) := by
  simp [cert, verify_leaf, rule, pack2, left, right, decode_pair]

theorem head2_ok (D A H : Nat) : cert (leaf 3 (pack3 D A H)) (head2 D A H) := by
  simp [cert, verify_leaf, rule, pack3, pack2, left, right, decode_pair]

theorem head3_ok (D A H : Nat) : cert (leaf 4 (pack3 D A H)) (head3 D A H) := by
  simp [cert, verify_leaf, rule, pack3, pack2, left, right, decode_pair]

theorem head4_ok (D A H : Nat) : cert (leaf 5 (pack3 D A H)) (head4 D A H) := by
  simp [cert, verify_leaf, rule, pack3, pack2, left, right, decode_pair]

theorem head5_ok (D H : Nat) : cert (leaf 6 (pack2 D H)) (head5 D H) := by
  simp [cert, verify_leaf, rule, pack2, left, right, decode_pair]

theorem head6_ok (D A H : Nat) : cert (leaf 7 (pack3 D A H)) (head6 D A H) := by
  simp [cert, verify_leaf, rule, pack3, pack2, left, right, decode_pair]

theorem r8_ok (D A H d : Nat) (h : d ≤ D) :
    cert (leaf 8 (pack4 D A H d)) (rho8 D A H d) := by
  simp [cert, verify_leaf, rule, pack4, pack3, pack2, left, right, decode_pair, h]

theorem bundle_ok (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b) :
    cert (leaf 9 (pack3 a b c)) (bundle a b c) := by
  simp [cert, verify_leaf, rule, pack3, pack2, left, right, decode_pair, ha, hb]

end PA196CertificateStack.NativeChecker

#print axioms PA196CertificateStack.NativeChecker.truth
#print axioms PA196CertificateStack.NativeChecker.head1_ok
#print axioms PA196CertificateStack.NativeChecker.head2_ok
#print axioms PA196CertificateStack.NativeChecker.head3_ok
#print axioms PA196CertificateStack.NativeChecker.head4_ok
#print axioms PA196CertificateStack.NativeChecker.head5_ok
#print axioms PA196CertificateStack.NativeChecker.head6_ok
#print axioms PA196CertificateStack.NativeChecker.r8_ok
#print axioms PA196CertificateStack.NativeChecker.bundle_ok

namespace PA196CertificateStack.NativeChecker
open PA196CertificateStack.Cantor PA196CertificateStack.Native

/-- Increasing the values of already accepted premises leaves any accepted
rule application unchanged. This is the semantic core of fuel transport. -/
theorem rule_stable (p q : Nat → Nat) (tag payload : Nat)
    (hpq : ∀ n, p n ≠ 0 → q n = p n)
    (accepted : rule p tag payload ≠ 0) :
    rule q tag payload = rule p tag payload := by
  cases tag with
  | zero =>
    have hx : p (left (right payload)) ≠ 0 := by
      intro hz
      apply accepted
      simp [rule, hz]
    have hy : p (left (right (right payload))) ≠ 0 := by
      intro hz
      apply accepted
      simp [rule, hz]
    simp [rule, hpq _ hx, hpq _ hy]
  | succ n =>
    cases n with
    | zero =>
      have hx : p (left (right payload)) ≠ 0 := by
        intro hz
        apply accepted
        simp [rule, hz]
      simp [rule, hpq _ hx]
    | succ n =>
      simp only [rule]
      split <;> first | omega | rfl

end PA196CertificateStack.NativeChecker

namespace PA196CertificateStack.NativeChecker

theorem entry_stable : ∀ fuel fuel' bound bound' tree,
    fuel ≤ fuel' → bound ≤ bound' → entry fuel bound tree ≠ 0 →
      entry fuel' bound' tree = entry fuel bound tree := by
  intro fuel
  induction fuel with
  | zero =>
    intro fuel' bound bound' tree hf hb accepted
    simp [entry] at accepted
  | succ fuel ih =>
    intro fuel' bound bound' tree hf hb accepted
    cases fuel' with
    | zero => omega
    | succ fuel' =>
      have hle : fuel ≤ fuel' := by omega
      by_cases ht : tree ≤ bound
      · have ht' : tree ≤ bound' := Nat.le_trans ht hb
        simp only [entry, if_pos ht] at accepted
        simp only [entry, if_pos ht, if_pos ht']
        apply rule_stable
        · intro n hn
          exact ih fuel' bound bound' n hle hb hn
        · exact accepted
      · simp [entry, ht] at accepted

end PA196CertificateStack.NativeChecker

#print axioms PA196CertificateStack.NativeChecker.rule_stable
#print axioms PA196CertificateStack.NativeChecker.entry_stable

namespace PA196CertificateStack.NativeChecker
open PA196CertificateStack.Cantor PA196CertificateStack.Native

theorem triangle_ge (n : Nat) : n ≤ triangle n := by
  induction n with
  | zero => simp [triangle]
  | succ n ih => simp only [triangle]; omega

theorem pair_bounds (a b : Nat) : a ≤ pair a b ∧ b ≤ pair a b := by
  have h := triangle_ge (a+b)
  constructor
  · simp only [pair]; omega
  · simp [pair]

theorem mpTree_bounds (b p q : Nat) : p ≤ mpTree b p q ∧ q ≤ mpTree b p q := by
  have htree := (pair_bounds 0 (pack3 b p q)).2
  have h3 := (pair_bounds b (pack2 p q)).2
  have hp := (pair_bounds p (pair q 0)).1
  have hq := Nat.le_trans (pair_bounds q 0).1 (pair_bounds p (pair q 0)).2
  exact ⟨Nat.le_trans hp (Nat.le_trans h3 htree),
         Nat.le_trans hq (Nat.le_trans h3 htree)⟩

theorem genTree_bound (v p : Nat) : p ≤ genTree v p := by
  exact Nat.le_trans (pair_bounds p 0).1 <|
    Nat.le_trans (pair_bounds v (pair p 0)).2 (pair_bounds 1 (pack2 v p)).2

end PA196CertificateStack.NativeChecker

namespace PA196CertificateStack.NativeChecker
open PA196CertificateStack.Cantor PA196CertificateStack.Native

theorem mp_ok (a b minor major : Nat) (hm : cert minor a)
    (hj : cert major (I a b)) : cert (mpCertificate b minor major) b := by
  let fm := left minor
  let fj := left major
  let tm := right minor
  let tj := right major
  let bound := mpTree b tm tj
  have hm0 : entry fm tm tm = a+1 := hm
  have hj0 : entry fj tj tj = I a b+1 := hj
  have hmne : entry fm tm tm ≠ 0 := by rw [hm0]; omega
  have hjne : entry fj tj tj ≠ 0 := by rw [hj0]; omega
  have hm' : entry (fm+fj) bound tm = a+1 :=
    (entry_stable fm (fm+fj) tm bound tm (by omega) (mpTree_bounds b tm tj).1 hmne).trans hm0
  have hj' : entry (fm+fj) bound tj = I a b+1 :=
    (entry_stable fj (fm+fj) tj bound tj (by omega) (mpTree_bounds b tm tj).2 hjne).trans hj0
  have hrule : rule (entry (fm+fj) bound) 0 (pack3 b tm tj) = b+1 := by
    simp [rule, pack3, pack2, left, right, decode_pair, hm', hj']
  have hf : left (mpCertificate b minor major) = fm+fj+1 := by
    simp [mpCertificate, left, decode_pair, fm, fj]
  have ht : right (mpCertificate b minor major) = bound := by
    simp [mpCertificate, right, decode_pair, bound, tm, tj]
  unfold cert verify
  rw [hf, ht]
  simp only [entry, Nat.le_refl, if_true]
  simpa [bound, mpTree, left, right, decode_pair] using hrule

theorem gen_ok (v a child : Nat) (h : cert child a) : cert (genCertificate v child) (U v a) := by
  let fuel := left child
  let tree := right child
  let bound := genTree v tree
  have h0 : entry fuel tree tree = a+1 := h
  have hne : entry fuel tree tree ≠ 0 := by rw [h0]; omega
  have h' : entry fuel bound tree = a+1 :=
    (entry_stable fuel fuel tree bound tree (Nat.le_refl _) (genTree_bound v tree) hne).trans h0
  have hrule : rule (entry fuel bound) 1 (pack2 v tree) = U v a+1 := by
    simp [rule, pack2, left, right, decode_pair, h']
  have hf : left (genCertificate v child) = fuel+1 := by
    simp [genCertificate, left, decode_pair, fuel]
  have ht : right (genCertificate v child) = bound := by
    simp [genCertificate, right, decode_pair, bound, tree]
  unfold cert verify
  rw [hf, ht]
  simp only [entry, Nat.le_refl, if_true]
  simpa [bound, genTree, left, right, decode_pair] using hrule

end PA196CertificateStack.NativeChecker

#print axioms PA196CertificateStack.NativeChecker.mp_ok
#print axioms PA196CertificateStack.NativeChecker.gen_ok

namespace PA196CertificateStack.NativeChecker
open PA196CertificateStack.Cantor PA196CertificateStack.Native PA196CertificateStack.Commands

/-- All required interfaces hold for the direct fuel/table checker. The
connection of this checker to the imported model-valued checker is separate. -/
theorem checker_interfaces : CheckerInterfaces cert where
  truth := truth
  mp := mp_ok
  gen := gen_ok
  head1 := head1_ok
  head2 := head2_ok
  head3 := head3_ok
  head4 := head4_ok
  head5 := head5_ok
  head6 := head6_ok
  r8 := r8_ok
  bundle := bundle_ok

/-- A halting PA196-shaped command word yields a code accepted as formula 1
by the direct numeric checker, without conditional checker hypotheses. -/
theorem halt_produces_accepted_certificate (cs : List Command)
    (halt : run pair decode heads gate cs ⟨0,0,0,0⟩ = none) :
    ∃ proof, extract (decode := decode) (checkerConstructors cert checker_interfaces) cs
        ⟨0,0,0,0⟩ ⟨739,0,739⟩ = some proof ∧ verify proof = 2 := by
  obtain ⟨proof, hex, hcert⟩ := native_halt_extractor cert checker_interfaces cs halt
  exact ⟨proof, hex, hcert⟩

end PA196CertificateStack.NativeChecker

#print axioms PA196CertificateStack.NativeChecker.checker_interfaces
#print axioms PA196CertificateStack.NativeChecker.halt_produces_accepted_certificate

namespace PA196CertificateStack.NativeChecker

/-- A direct finite-list presentation of the fuel table. This is a standard
Nat model of the row recurrence, not yet Foundation's HFS-coded table. -/
def listTable : Nat → Nat → List Nat
  | 0, bound => List.replicate (bound+1) 0
  | fuel+1, bound =>
      let previous := listTable fuel bound
      (List.range (bound+1)).map fun tree =>
        rule (fun n => previous.getD n 0) (left tree) (right tree)

theorem entry_eq_listTable : ∀ fuel bound tree,
    entry fuel bound tree = (listTable fuel bound).getD tree 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro bound tree
    simp only [entry, listTable, List.getD, List.getElem?_replicate]
    split <;> rfl
  | succ fuel ih =>
    intro bound tree
    by_cases h : tree ≤ bound
    · have hr : tree < bound+1 := by omega
      simp only [entry, if_pos h, listTable, List.getD, List.getElem?_map,
        List.getElem?_range hr, Option.map_some, Option.getD_some]
      apply congrArg (fun previous => rule previous (left tree) (right tree))
      funext n
      exact ih bound n
    · have hr : (List.range (bound+1)).length ≤ tree := by simp; omega
      simp only [entry, if_neg h, listTable, List.getD, List.getElem?_map,
        List.getElem?_eq_none hr, Option.map_none, Option.getD_none]

end PA196CertificateStack.NativeChecker

#print axioms PA196CertificateStack.NativeChecker.entry_eq_listTable
