module
public import PA196.Table
public import PA196.Literal
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA196.Conjugacy
open M6.Zip
abbrev machine := Literal.machine
def labels : List Nat := [74, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 66, 68, 69, 70, 71, 72, 73, 75, 77, 80, 81, 82, 83, 84, 87, 88, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 103, 104, 105, 106, 107, 108, 109, 110, 111, 113, 114, 122, 123, 124, 125, 126, 127, 128, 130, 137, 138, 139, 141, 144, 161, 164, 166, 174, 179, 185, 188, 190, 194, 196, 197, 198, 213, 214, 217, 221, 301, 302, 310, 312, 1300, 1301, 1302, 1303, 1305, 1306, 1307, 1308, 1309, 1310, 1312, 1313, 1314, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1324, 1326, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 254]
def label (q : Nat) : Nat := labels.getD q (q+1001)
def relabelAction (a : Bool × Bool × Nat) : Bool × Bool × Nat := (a.1,a.2.1,label a.2.2)
theorem labels_injective : labels.Nodup := by decide +kernel
theorem exact_rows : (List.range 197).all (fun q => [false,true].all (fun b =>
  decide (Table.machine (label q) b = (machine q b).map relabelAction))) = true := by decide +kernel
theorem rows_conjugate {q : Nat} (hq : q < 197) (b : Bool) :
 Table.machine (label q) b = (machine q b).map relabelAction := by
 have h := List.all_eq_true.mp exact_rows q (List.mem_range.mpr hq)
 have hb : b ∈ [false,true] := by cases b <;> simp
 exact of_decide_eq_true (List.all_eq_true.mp h b hb)
theorem working_count : Literal.workingLabels.length = 196 := by decide +kernel
theorem defined_row_count : Literal.workingLabels.length * 2 = 392 := by decide +kernel
theorem start_mapping : label 0 = 74 := by decide
theorem root_mapping : label 75 = 84 := by decide
theorem halt_mapping : label 196 = 254 := by decide
#print axioms rows_conjugate
end PA196.Conjugacy

namespace PA196.Conjugacy
open M6.Zip
set_option maxHeartbeats 16000000

def mapConf (c : Conf) : Conf := ⟨label c.q,c.l,c.r⟩
private theorem next_bounded_check : (List.range 197).all (fun q => [false,true].all (fun b =>
  match machine q b with | none => true | some (_,_,q') => decide (q' < 197))) = true := by decide +kernel

theorem next_bounded {q t : Nat} {b w d : Bool} (hq : q < 197)
    (h : machine q b = some (w,d,t)) : t < 197 := by
  have hh := List.all_eq_true.mp next_bounded_check q (List.mem_range.mpr hq)
  have hb : b ∈ [false,true] := by cases b <;> simp
  have ht := List.all_eq_true.mp hh b hb
  rw [h] at ht
  exact of_decide_eq_true ht

theorem step_conjugate (c : Conf) (hq : c.q < 197) :
    step Table.machine (mapConf c) = (step machine c).map mapConf := by
  rcases c with ⟨q,l,r⟩
  simp only [step,mapConf,rows_conjugate hq]
  cases he : machine q (r.headD false) with
  | none => rfl
  | some a =>
    rcases a with ⟨w,d,t⟩
    cases d <;> rfl

theorem step_bounded {c c' : Conf} (hq : c.q < 197) (h : step machine c = some c') :
    c'.q < 197 := by
  unfold step at h
  cases he : machine c.q (c.r.headD false) with
  | none => rw [he] at h; cases h
  | some a =>
    rcases a with ⟨w,d,t⟩
    have ht := next_bounded hq he
    cases d <;> simp only [he, Option.some.injEq] at h <;> subst c' <;> exact ht

theorem run_conjugate (n : Nat) (c : Conf) (hq : c.q < 197) :
    run Table.machine n (mapConf c) = (run machine n c).map mapConf := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [run,step_conjugate c hq]
    cases he : step machine c with
    | none => rfl
    | some c' => simpa using ih c' (step_bounded hq he)

theorem run_bounded {n : Nat} {c c' : Conf} (hq : c.q < 197)
    (h : run machine n c = some c') : c'.q < 197 := by
  induction n generalizing c with
  | zero => simp only [run,Option.some.injEq] at h; subst c'; exact hq
  | succ n ih =>
    simp only [run] at h
    cases he : step machine c with
    | none => rw [he] at h; cases h
    | some x => rw [he] at h; exact ih (step_bounded hq he) h

theorem halts_transport {c : Conf} (hq : c.q < 197) (h : Halts machine c) :
    Halts Table.machine (mapConf c) := by
  obtain ⟨c',⟨n,hr⟩,hs⟩ := h
  refine ⟨mapConf c',⟨n,?_⟩,?_⟩
  · rw [run_conjugate n c hq,hr]; rfl
  · rw [step_conjugate c' (run_bounded hq hr),hs]; rfl

#print axioms run_conjugate
#print axioms halts_transport
end PA196.Conjugacy
