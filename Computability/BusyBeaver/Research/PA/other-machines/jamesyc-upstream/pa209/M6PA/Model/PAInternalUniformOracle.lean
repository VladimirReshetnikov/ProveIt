module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalFileGuards
public import M6PA.Model.PAInternalSymbolicAudit
public import M6PA.Model.PAInternalOracleAlphabet
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.FileBoxes
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open FileLayout M6.Runtime Symbolic
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- Every oracle call in the unchanged symbolic checker receives an actual
all-model machine trace, using one complete-file interpretation. -/
theorem allowed_oracle (n xs : V) (hsize : (10 : V)≤len xs) (br : Branch)
    (hg : Guard xs br) : AllowedOracle n (box xs) InternalOracleAlphabet.allowed br := by
  intro q x l _ q' x' extra hor
  cases x with
  | plain e =>
    cases e with
    | inc r => simp [oracle] at hor
    | dec r => simp [oracle] at hor
    | none =>
      cases hs : skipTarget q with
      | none => simp [oracle,hs] at hor
      | some r =>
        have ho := hor
        simp only [oracle,hs,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hor
        obtain ⟨rfl,rfl,rfl⟩ := hor
        obtain ⟨hq,hr⟩ := skipTarget_sk hs
        subst q
        simpa [config,word,denseControl] using
          mark_call xs (word n (box xs) l 0) ⟨r,hr⟩ (index_valid xs hsize r hr)
  | mark r =>
    by_cases hr : r<9
    · by_cases h64 : q=64
      · subst q
        simp only [oracle,if_pos hr,ite_true,Option.some.injEq,Prod.mk.injEq] at hor
        obtain ⟨rfl,rfl,rfl⟩ := hor
        simpa [config,word,denseControl] using increment_call xs (word n (box xs) l 0) r
      · by_cases h0 : q=0
        · subst q
          cases br with
          | none => simp [oracle,hr] at hor
          | some b =>
            rcases b with ⟨r',z⟩
            by_cases he : r=r'
            · subst r'
              cases z with
              | true =>
                simp only [oracle,if_pos hr,show ¬(0=64) by decide,ite_false,ite_true,
                  Option.some.injEq,Prod.mk.injEq] at hor
                obtain ⟨rfl,rfl,rfl⟩ := hor
                have hz : value r xs=0 := hg
                simpa [config,word,denseControl] using zero_call xs (word n (box xs) l 0) r
                  (index_valid xs hsize r hr) hz (suffix_nonempty xs hsize r hr)
              | false =>
                simp only [oracle,if_pos hr,show ¬(0=64) by decide,ite_false,ite_true,
                  Option.some.injEq,Prod.mk.injEq] at hor
                obtain ⟨rfl,rfl,rfl⟩ := hor
                have hp : value r xs≠0 := hg
                let L := word n (box xs) l 0
                have hd : ((1+1)*L+1)/2=L := by simpa using LeftPhase.bit_div true L
                have hm : ((1+1)*L+1)%2=1 := by simpa using LeftPhase.bit_mod true L
                simpa [config,word,denseControl,L,hd,hm] using positive_call xs L r hp
            · simp [oracle,hr,he] at hor
        · simp [oracle,hr,h64,h0] at hor
    · simp [oracle,hr] at hor

/-- A single interpretation theorem consumes ANY accepted original-style
finite checker certificate. No manual translation of each contract is needed. -/
theorem checked_contract (n xs : V) (hsize : (10 : V)≤len xs)
    (fuel : Nat) (c : M6.RuntimeContracts.Contract) (hc : M6.RuntimeContracts.check fuel c=true)
    (hg : Guard xs c.branch) :
    Progress true (config n (box xs) denseControl c.initial)
      (config n (box xs) denseControl c.target) := by
  apply contract_sound n (box xs) fuel c hc
  exact audit_sound n (box xs) InternalOracleAlphabet.allowed c.branch
    (fun s => sMatches s c.target) (allowed_oracle n xs hsize c.branch hg)
    (head xs) fuel c.initial false
    (InternalOracleAlphabet.audit_covered c.branch (fun s => sMatches s c.target) fuel c.initial false)
end Models
#print axioms allowed_oracle
#print axioms checked_contract
end M6.Arithmetic.PA.InternalTrace.FileBoxes

