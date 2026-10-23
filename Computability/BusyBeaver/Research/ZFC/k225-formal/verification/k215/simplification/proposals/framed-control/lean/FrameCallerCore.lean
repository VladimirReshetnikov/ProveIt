import FrameContracts

namespace SetTheory.BusyBeaver.ZFC.KFrameCallers
open KZip KRuntimeCore KLeftFrame KFramedTemplates KFrameContracts KTableCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0


def bits (s : String) : List Bool := s.toList.map (fun c => c == '1')

def metas : List Meta := [
  ⟨62, bits "111", bits "", false, 3⟩,
  ⟨13, bits "11", bits "", false, 2⟩,
  ⟨108, bits "001", bits "1", true, 1⟩,
  ⟨42, bits "11", bits "", false, 2⟩,
  ⟨83, bits "111", bits "", false, 3⟩,
  ⟨138, bits "111", bits "1", false, 2⟩,
  ⟨141, bits "11", bits "", false, 2⟩,
  ⟨57, bits "11", bits "", false, 2⟩,
  ⟨80, bits "0111", bits "0", false, 3⟩,
  ⟨72, bits "11", bits "", false, 2⟩,
  ⟨126, bits "11", bits "", false, 2⟩,
  ⟨47, bits "11", bits "", false, 2⟩,
  ⟨139, bits "11", bits "", false, 2⟩,
  ⟨108, bits "101", bits "", false, 2⟩,
  ⟨103, bits "0011", bits "1", true, 1⟩,
  ⟨122, bits "1", bits "", false, 1⟩,
  ⟨103, bits "0110111", bits "100", true, 1⟩,
  ⟨103, bits "00111", bits "1", true, 1⟩,
  ⟨96, bits "0011111", bits "1", true, 1⟩,
  ⟨162, bits "0011", bits "1", true, 1⟩,
]

def metaAt (i : Nat) : Meta := metas[i]?.getD default
def templateAt (i : Nat) : LocalTemplate := templates[i]?.getD default

def shapeCheck : Bool :=
  decide (metas.length = templates.length) &&
    (List.range metas.length).all (fun i => decide (Shape (metaAt i) (templateAt i)))

theorem shapes_checked : shapeCheck = true := by decide +kernel

def checkCaller (c : Caller) : Bool :=
  decide (c.templateIndex < metas.length) &&
    decide (CallerOK (metaAt c.templateIndex) (templateAt c.templateIndex) c)

#print axioms shapes_checked
end SetTheory.BusyBeaver.ZFC.KFrameCallers
