import CM215Check00
import CM215Check01
import CM215Check02
import CM215Check03
import CM215Check04
import CM215Check05
import CM215Check06
import CM215Check07
import CM215Check08
import CM215Check09
import CM215Check10
import CM215Check11
import CM215Check12
import CM215Check13
import CM215Check14
import CM215Check15
import CM215Check16
import CM215Check17
import CM215Check18
namespace CM215Certificate
open MarkerTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem table_check : FiniteMarkerCertificate.check parentTable markerTable = true := by
  change (List.finRange 303).all stateCheck = true
  rw [partition]
  simp only [List.all_append, check00, check01, check02, check03, check04, check05, check06, check07, check08, check09, check10, check11, check12, check13, check14, check15, check16, check17, check18, Bool.and_self]

theorem localRows : FiniteMarkerCertificate.LocalRows parentTable markerTable where
  old52zero := rfl
  old52one := rfl
  old176zero := rfl
  old176one := rfl
  new52zero := rfl
  new52one := rfl
  new176zero := rfl
  new176one := rfl
  new185zero := rfl
  new129zero := rfl

theorem certificate : Certificate parentTable markerTable :=
  FiniteMarkerCertificate.certificate _ _ table_check localRows

theorem all_tape_halts_iff (h : Int) (t : Tape) :
    PositiveStuttering.Halts (step parentTable) ⟨0, h, t⟩ ↔
    PositiveStuttering.Halts (step markerTable) ⟨0, h, t⟩ :=
  MarkerTransport.all_tape_halts_iff certificate h t

theorem blank_halts_iff :
    PositiveStuttering.Halts (step parentTable) ⟨0, 0, fun _ => false⟩ ↔
    PositiveStuttering.Halts (step markerTable) ⟨0, 0, fun _ => false⟩ :=
  all_tape_halts_iff _ _

theorem parent_working_states : liveCount parentTable (List.finRange 303) = 215 := by
  rw [partition]
  simp only [liveCount_append, oldCount00, oldCount01, oldCount02, oldCount03, oldCount04, oldCount05, oldCount06, oldCount07, oldCount08, oldCount09, oldCount10, oldCount11, oldCount12, oldCount13, oldCount14, oldCount15, oldCount16, oldCount17, oldCount18]

theorem marker_working_states : liveCount markerTable (List.finRange 303) = 215 := by
  rw [partition]
  simp only [liveCount_append, newCount00, newCount01, newCount02, newCount03, newCount04, newCount05, newCount06, newCount07, newCount08, newCount09, newCount10, newCount11, newCount12, newCount13, newCount14, newCount15, newCount16, newCount17, newCount18]

theorem exactly_six_changed_rows : changes (List.finRange 303) = 6 := by
  rw [partition]
  simp only [changes_append, changed00, changed01, changed02, changed03, changed04, changed05, changed06, changed07, changed08, changed09, changed10, changed11, changed12, changed13, changed14, changed15, changed16, changed17, changed18]

#print axioms table_check
#print axioms certificate
#print axioms all_tape_halts_iff
#print axioms blank_halts_iff
#print axioms parent_working_states
#print axioms marker_working_states
#print axioms exactly_six_changed_rows
end CM215Certificate
