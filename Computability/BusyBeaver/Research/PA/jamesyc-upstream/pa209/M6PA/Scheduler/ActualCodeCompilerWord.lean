module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCodeCompilerSound
public import M6.Source.CommandAtomEncoding
public import M6.Source.UniversalCommandWitness
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.NativeCalculus.ActualBasis.Code
open M6.Source M6.Source.Enumeration M6.Source.Cantor
open M6.Source.CommandAtomEncoding
attribute [local irreducible] word encodeWord encodeAtoms atoms compileCertificate commandsEval commandEval

def haltCertificate (code : Nat) : List Command :=
  [.ax 0 0 0] ++ compileCertificate code ++ [.shift]

def candidateCode (code : Nat) : Nat := encodeAtoms (atoms (haltCertificate code))-1

theorem candidateCode_word (code : Nat) : word (candidateCode code)=haltCertificate code := by
  unfold candidateCode haltCertificate
  exact candidate_atoms (.ax 0 0 0) (compileCertificate code ++ [.shift])

theorem haltCertificate_universal (code : Nat) (h : verify code=some 1) (s : CommandStore) :
    commandsEval (haltCertificate code) s=none := by
  obtain ⟨p,hp⟩ := compileCertificate_matches code 1 h
  unfold haltCertificate
  rw [←hp]
  exact haltWord_universal p s

theorem candidateCode_universal (code : Nat) (h : verify code=some 1) (s : CommandStore) :
    commandsEval (word (candidateCode code)) s=none := by
  rw [candidateCode_word]
  exact haltCertificate_universal code h s

#print axioms candidateCode_word
#print axioms candidateCode_universal
end M6.PA.NativeCalculus.ActualBasis.Code

