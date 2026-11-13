module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionRealizedBinary
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def realizedTermCompatible {n : Nat} (t : SourceTerm n) : RealizedTermCompatible t :=
  match t with
  | .bvar i => realizedBound i
  | .fvar i => realizedFree i
  | .func .zero _ => fun σ _ A b f c g _ r s hr hs =>
      realizedZero σ A b f c g (fun i => Fin.elim0 i) r s (by simpa only [BinaryOperation.term, Presentation.zero, Presentation.succ,
          Presentation.add, Presentation.mul, Rew.func, Function.comp_apply, value, Matrix.cons_val_zero, Matrix.cons_val_one] using hr) hs
  | .func .succ ts => fun σ _ A b f c g H r s hr hs =>
      realizedSuccessor (ts 0) (realizedTermCompatible (ts 0)) σ A b f c g
        (Fin.cases (H 0) (fun i => Fin.elim0 i)) r s (by simpa only [BinaryOperation.term, Presentation.zero, Presentation.succ,
          Presentation.add, Presentation.mul, Rew.func, Function.comp_apply, value, Matrix.cons_val_zero, Matrix.cons_val_one] using hr) hs
  | .func .add ts => fun σ _ A b f c g H r s hr hs =>
      realizedBinary .addition (ts 0) (ts 1)
        (realizedTermCompatible (ts 0)) (realizedTermCompatible (ts 1)) σ A b f c g
        (Fin.cases (H 0) (Fin.cases (H 1) (fun i => Fin.elim0 i))) r s (by simpa only [BinaryOperation.term, Presentation.zero, Presentation.succ,
          Presentation.add, Presentation.mul, Rew.func, Function.comp_apply, value, Matrix.cons_val_zero, Matrix.cons_val_one] using hr) hs
  | .func .mul ts => fun σ _ A b f c g H r s hr hs =>
      realizedBinary .multiplication (ts 0) (ts 1)
        (realizedTermCompatible (ts 0)) (realizedTermCompatible (ts 1)) σ A b f c g
        (Fin.cases (H 0) (Fin.cases (H 1) (fun i => Fin.elim0 i))) r s (by simpa only [BinaryOperation.term, Presentation.zero, Presentation.succ,
          Presentation.add, Presentation.mul, Rew.func, Function.comp_apply, value, Matrix.cons_val_zero, Matrix.cons_val_one] using hr) hs

#print axioms realizedTermCompatible
end M6.PA.ForwardRelational
