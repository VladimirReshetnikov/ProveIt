import DiophantineConsistency.ArithmeticHome215

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticHome215Checks
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineTape215 ArithmeticRegisterBoxes215 ArithmeticSymbolicCore215 ArithmeticHome215
open KRuntimeCore (Seg SConf Branch)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : KHomeReady.ready KTableCore.tm215=true := ready215
example (R : V) : runFrom 18 (leftFrame 2 0 (2*R+1))=frameSparse 84 1 R := boundary_actual R
example : runFrom 18 (leftFrame 2 (0:V) 1)=frameSparse 84 1 0 := by simpa using boundary_actual (0:V)
example (n L R : V) (hn : 0<n) :
    Reach (leftFrame 50 (bitPrefix true n L) R) (leftFrame 2 L (bitPrefix true n R)) :=
  scan_ones 7 (by decide) n L R hn
/-- Zero gap and zero constant retain a nonzero conservative streak. -/
example (v : Fin 9 → V) (k L R : V) :
    ∃ j, j≤3 ∧ j<8 ∧ Reach
      (leftFrame (KHome.state 3) (flatValue 0 v k [.run true 9 0] L) R)
      (leftFrame (KHome.state j) L (flatValue 0 v k [.run true 9 0] R)) :=
  scanBound_actual 0 v k (by rfl : KHome.scanBound 3 [.run true 9 0]=some 3) (by decide) (by rfl) L R
example (x : KRuntimeCore.BoxSt) (xs : List Seg) (i : Nat) : KHome.scanBound i (.box x::xs)=none := rfl
example : KHome.scanBound 0 [.run false 1 0]=none := by decide +kernel
example : KHome.stripBlank [.run true 0 1]=none := rfl
/-- Arbitrarily long exterior zero segments vanish at the exterior zero tail. -/
example (gap k : V) (v : Fin 9 → V) (a c : Nat) :
    flatValue gap v k [.bit true,.run false a c] 0=1 := by
  simpa using stripBlank_actual gap v k (by rfl : KHome.stripBlank [.run false a c,.bit true]=some [])
/-- The right payload may be an actual register box, even with zero spare count. -/
example (gap k : V) (v : Fin 9 → V) :
    ReachPos (interpret gap v k (2,true,[.bit true],[.box (.plain .none)]))
      (interpret gap v k (84,false,[.bit true],[.box (.plain .none)])) :=
  home_actual gap v k (by decide +kernel)
example (gap k : V) (v : Fin 9 → V) (hk : 0<k) {br : Branch} (hv : BranchValid br v)
    {s t : SConf} {m : Bool} (hh : KHome.home s=none)
    (hs : KRuntimeCore.sstep KTableCore.tm215 br s=some (t,m)) : StepOk gap v k s t m :=
  stepper_actual gap v k hk hv (by simpa [KHomeReady.stepper,ready215,KHomeReady.homeStep,hh] using hs)
example (gap k : V) (v : Fin 9 → V) (hk : 0<k) {br : Branch} (hv : BranchValid br v)
    {fuel : Nat} {s t target : SConf}
    (h : KHomeReady.exec KTableCore.tm215 br (fun u => KRuntimeCore.sMatches u target) fuel s false=some t) :
    ReachPos (interpret gap v k s) (interpret gap v k target) := exec_matches_actual gap v k hk hv h
/-- An initially true moved flag allows a zero-step target check. -/
example (s : SConf) : KHomeReady.exec KTableCore.tm215 none (fun _ => true) 1 s true=some s := rfl
example (gap k : V) (v : Fin 9 → V) (hk : 0<k) {br : Branch} (hv : BranchValid br v)
    {fuel : Nat} {s t : SConf} {target : SConf → Bool}
    (h : KHomeReady.exec KTableCore.tm215 br target fuel s true=some t) :
    Reach (interpret gap v k s) (interpret gap v k t) := (exec_flag_actual gap v k hk hv h).2.1
#print axioms reset_row
#print axioms next_row
#print axioms ready215
#print axioms flatValue_append
#print axioms scan_zeros_exact
#print axioms scan_ones
#print axioms boundary_actual
#print axioms scanBound_actual
#print axioms stripBlank_actual
#print axioms home_actual
#print axioms stepper_actual
#print axioms exec_flag_actual
#print axioms ArithmeticHome215.exec_actual
#print axioms exec_matches_actual
end DiophantineConsistency.ArithmeticHome215Checks
