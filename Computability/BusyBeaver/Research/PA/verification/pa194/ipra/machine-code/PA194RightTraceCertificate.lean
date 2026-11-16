import PA194GenericRightTrace
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194RightTraceCertificate
open PA194GenericRightTrace

def generate (q : Nat) : List Bool → Option (List Nat × Nat)
  | [] => some ([],q)
  | b::bs =>
    if q < 194 then
      let (w,d,n) := PA194Rows.rows.getD (q+q+(if b then 1 else 0)) (0,0,194)
      if d = 1 then (generate n bs).map (fun (ws,last) => (w::ws,last)) else none
    else none

theorem generatedTrace (bs : List Bool) (q : Nat) (ws : List Nat) (dest : Nat)
    (h : generate q bs = some (ws,dest)) : Trace q bs ws dest := by
  induction bs generalizing q ws dest with
  | nil =>
    simp [generate] at h
    rcases h with ⟨rfl,rfl⟩
    exact Trace.nil _
  | cons b bs ih =>
    simp only [generate] at h
    split at h
    next hq =>
      generalize hr : PA194Rows.rows.getD (q+q+(if b then 1 else 0)) (0,0,194) = row at h
      rcases row with ⟨w,d,n⟩
      split at h
      next hd =>
        change d = 1 at hd
        simp only [Prod.fst,Prod.snd] at h
        subst d
        cases hh : generate n bs with
        | none => simp [hh] at h
        | some pair =>
          rcases pair with ⟨ws',last⟩
          simp [hh] at h
          rcases h with ⟨rfl,rfl⟩
          apply Trace.cons q w n last b bs ws' hq
          · exact hr
          · exact ih n ws' last hh
      next hd => simp at h
    next hq => simp at h
#print axioms generatedTrace
end PA194RightTraceCertificate
