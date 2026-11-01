import DiophantineConsistency.AdaptiveGap85NegativeMultiplier
/-! The 42 bounded linear cases for the negative special template.
Every branch is proved in an arbitrary IΣ₁ model. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85NegativeLinearOptimized
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem case_8_1 (X : V) (hX : 4≤X) (h : 27*(8*X+1)=(4*(8:V)*(X+1)+3)*1) : False := by
  have he : (184:V)*X=8 := by
    have hh : (32*X+27)+(184*X)=(32*X+27)+8 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(8:V)*(X+1)+3)*1 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hle : (184:V)*4≤184*X := Arithmetic.mul_le_mul_left hX
  rw [he] at hle
  have hlt : (8:V)<184*4 := by norm_num
  exact (not_le_of_gt hlt) hle
 
private theorem case_8_2 (X : V) (hX : 4≤X) (h : 27*(8*X+1)=(4*(8:V)*(X+1)+3)*2) : False := by
  have he : (152:V)*X=43 := by
    have hh : (64*X+27)+(152*X)=(64*X+27)+43 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(8:V)*(X+1)+3)*2 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hle : (152:V)*4≤152*X := Arithmetic.mul_le_mul_left hX
  rw [he] at hle
  have hlt : (43:V)<152*4 := by norm_num
  exact (not_le_of_gt hlt) hle
 
private theorem case_8_3 (X : V) (hX : 4≤X) (h : 27*(8*X+1)=(4*(8:V)*(X+1)+3)*3) : False := by
  have he : (120:V)*X=78 := by
    have hh : (96*X+27)+(120*X)=(96*X+27)+78 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(8:V)*(X+1)+3)*3 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hle : (120:V)*4≤120*X := Arithmetic.mul_le_mul_left hX
  rw [he] at hle
  have hlt : (78:V)<120*4 := by norm_num
  exact (not_le_of_gt hlt) hle
 
private theorem case_8_4 (X : V) (hX : 4≤X) (h : 27*(8*X+1)=(4*(8:V)*(X+1)+3)*4) : False := by
  have he : (88:V)*X=113 := by
    have hh : (128*X+27)+(88*X)=(128*X+27)+113 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(8:V)*(X+1)+3)*4 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hle : (88:V)*4≤88*X := Arithmetic.mul_le_mul_left hX
  rw [he] at hle
  have hlt : (113:V)<88*4 := by norm_num
  exact (not_le_of_gt hlt) hle
 
private theorem case_8_5 (X : V) (hX : 4≤X) (h : 27*(8*X+1)=(4*(8:V)*(X+1)+3)*5) : False := by
  have he : (56:V)*X=148 := by
    have hh : (160*X+27)+(56*X)=(160*X+27)+148 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(8:V)*(X+1)+3)*5 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hle : (56:V)*4≤56*X := Arithmetic.mul_le_mul_left hX
  rw [he] at hle
  have hlt : (148:V)<56*4 := by norm_num
  exact (not_le_of_gt hlt) hle
 
private theorem case_8_6 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(8:V)*(X+1)+3)*6) : False := by
  have he : (24:V)*X=183 := by
    have hh : (192*X+27)+(24*X)=(192*X+27)+183 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(8:V)*(X+1)+3)*6 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hz : (183:V)%24=0 := mod_eq_zero_iff_dvd.mpr ⟨X,he.symm⟩
  have hr : (183:V)%24=15 := by
    calc
      _ = ((15:V)+7*24)%24 := by congr 1; ring
      _ = (15:V)%24 := mod_add_mul 15 7 (by simp)
      _ = 15 := mod_eq_self_of_lt (by norm_num)
  rw [hr] at hz
  norm_num at hz
 
private theorem case_16_1 (X : V) (hX : 4≤X) (h : 27*(8*X+1)=(4*(16:V)*(X+1)+3)*1) : False := by
  have he : (152:V)*X=40 := by
    have hh : (64*X+27)+(152*X)=(64*X+27)+40 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(16:V)*(X+1)+3)*1 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hle : (152:V)*4≤152*X := Arithmetic.mul_le_mul_left hX
  rw [he] at hle
  have hlt : (40:V)<152*4 := by norm_num
  exact (not_le_of_gt hlt) hle
 
private theorem case_16_2 (X : V) (hX : 4≤X) (h : 27*(8*X+1)=(4*(16:V)*(X+1)+3)*2) : False := by
  have he : (88:V)*X=107 := by
    have hh : (128*X+27)+(88*X)=(128*X+27)+107 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(16:V)*(X+1)+3)*2 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hle : (88:V)*4≤88*X := Arithmetic.mul_le_mul_left hX
  rw [he] at hle
  have hlt : (107:V)<88*4 := by norm_num
  exact (not_le_of_gt hlt) hle
 
private theorem case_16_3 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(16:V)*(X+1)+3)*3) : False := by
  have he : (24:V)*X=174 := by
    have hh : (192*X+27)+(24*X)=(192*X+27)+174 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(16:V)*(X+1)+3)*3 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hz : (174:V)%24=0 := mod_eq_zero_iff_dvd.mpr ⟨X,he.symm⟩
  have hr : (174:V)%24=6 := by
    calc
      _ = ((6:V)+7*24)%24 := by congr 1; ring
      _ = (6:V)%24 := mod_add_mul 6 7 (by simp)
      _ = 6 := mod_eq_self_of_lt (by norm_num)
  rw [hr] at hz
  norm_num at hz
 
private theorem case_16_4 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(16:V)*(X+1)+3)*4) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(40*X+241) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(16:V)*(X+1)+3)*4 := h
      _ = _ := by ring
  have hz : (0:V)=40*X+241 := add_left_cancel hh
  have hp : 0<40*X+241 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_16_5 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(16:V)*(X+1)+3)*5) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(104*X+308) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(16:V)*(X+1)+3)*5 := h
      _ = _ := by ring
  have hz : (0:V)=104*X+308 := add_left_cancel hh
  have hp : 0<104*X+308 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_16_6 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(16:V)*(X+1)+3)*6) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(168*X+375) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(16:V)*(X+1)+3)*6 := h
      _ = _ := by ring
  have hz : (0:V)=168*X+375 := add_left_cancel hh
  have hp : 0<168*X+375 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_24_1 (X : V) (hX : 4≤X) (h : 27*(8*X+1)=(4*(24:V)*(X+1)+3)*1) : False := by
  have he : (120:V)*X=72 := by
    have hh : (96*X+27)+(120*X)=(96*X+27)+72 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(24:V)*(X+1)+3)*1 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hle : (120:V)*4≤120*X := Arithmetic.mul_le_mul_left hX
  rw [he] at hle
  have hlt : (72:V)<120*4 := by norm_num
  exact (not_le_of_gt hlt) hle
 
private theorem case_24_2 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(24:V)*(X+1)+3)*2) : False := by
  have he : (24:V)*X=171 := by
    have hh : (192*X+27)+(24*X)=(192*X+27)+171 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(24:V)*(X+1)+3)*2 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hz : (171:V)%24=0 := mod_eq_zero_iff_dvd.mpr ⟨X,he.symm⟩
  have hr : (171:V)%24=3 := by
    calc
      _ = ((3:V)+7*24)%24 := by congr 1; ring
      _ = (3:V)%24 := mod_add_mul 3 7 (by simp)
      _ = 3 := mod_eq_self_of_lt (by norm_num)
  rw [hr] at hz
  norm_num at hz
 
private theorem case_24_3 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(24:V)*(X+1)+3)*3) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(72*X+270) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(24:V)*(X+1)+3)*3 := h
      _ = _ := by ring
  have hz : (0:V)=72*X+270 := add_left_cancel hh
  have hp : 0<72*X+270 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_24_4 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(24:V)*(X+1)+3)*4) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(168*X+369) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(24:V)*(X+1)+3)*4 := h
      _ = _ := by ring
  have hz : (0:V)=168*X+369 := add_left_cancel hh
  have hp : 0<168*X+369 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_24_5 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(24:V)*(X+1)+3)*5) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(264*X+468) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(24:V)*(X+1)+3)*5 := h
      _ = _ := by ring
  have hz : (0:V)=264*X+468 := add_left_cancel hh
  have hp : 0<264*X+468 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_24_6 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(24:V)*(X+1)+3)*6) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(360*X+567) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(24:V)*(X+1)+3)*6 := h
      _ = _ := by ring
  have hz : (0:V)=360*X+567 := add_left_cancel hh
  have hp : 0<360*X+567 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_32_1 (X : V) (hX : 4≤X) (h : 27*(8*X+1)=(4*(32:V)*(X+1)+3)*1) : False := by
  have he : (88:V)*X=104 := by
    have hh : (128*X+27)+(88*X)=(128*X+27)+104 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(32:V)*(X+1)+3)*1 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hle : (88:V)*4≤88*X := Arithmetic.mul_le_mul_left hX
  rw [he] at hle
  have hlt : (104:V)<88*4 := by norm_num
  exact (not_le_of_gt hlt) hle
 
private theorem case_32_2 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(32:V)*(X+1)+3)*2) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(40*X+235) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(32:V)*(X+1)+3)*2 := h
      _ = _ := by ring
  have hz : (0:V)=40*X+235 := add_left_cancel hh
  have hp : 0<40*X+235 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_32_3 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(32:V)*(X+1)+3)*3) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(168*X+366) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(32:V)*(X+1)+3)*3 := h
      _ = _ := by ring
  have hz : (0:V)=168*X+366 := add_left_cancel hh
  have hp : 0<168*X+366 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_32_4 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(32:V)*(X+1)+3)*4) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(296*X+497) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(32:V)*(X+1)+3)*4 := h
      _ = _ := by ring
  have hz : (0:V)=296*X+497 := add_left_cancel hh
  have hp : 0<296*X+497 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_32_5 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(32:V)*(X+1)+3)*5) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(424*X+628) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(32:V)*(X+1)+3)*5 := h
      _ = _ := by ring
  have hz : (0:V)=424*X+628 := add_left_cancel hh
  have hp : 0<424*X+628 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_32_6 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(32:V)*(X+1)+3)*6) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(552*X+759) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(32:V)*(X+1)+3)*6 := h
      _ = _ := by ring
  have hz : (0:V)=552*X+759 := add_left_cancel hh
  have hp : 0<552*X+759 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_40_1 (X : V) (hX : 4≤X) (h : 27*(8*X+1)=(4*(40:V)*(X+1)+3)*1) : False := by
  have he : (56:V)*X=136 := by
    have hh : (160*X+27)+(56*X)=(160*X+27)+136 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(40:V)*(X+1)+3)*1 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hle : (56:V)*4≤56*X := Arithmetic.mul_le_mul_left hX
  rw [he] at hle
  have hlt : (136:V)<56*4 := by norm_num
  exact (not_le_of_gt hlt) hle
 
private theorem case_40_2 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(40:V)*(X+1)+3)*2) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(104*X+299) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(40:V)*(X+1)+3)*2 := h
      _ = _ := by ring
  have hz : (0:V)=104*X+299 := add_left_cancel hh
  have hp : 0<104*X+299 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_40_3 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(40:V)*(X+1)+3)*3) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(264*X+462) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(40:V)*(X+1)+3)*3 := h
      _ = _ := by ring
  have hz : (0:V)=264*X+462 := add_left_cancel hh
  have hp : 0<264*X+462 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_40_4 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(40:V)*(X+1)+3)*4) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(424*X+625) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(40:V)*(X+1)+3)*4 := h
      _ = _ := by ring
  have hz : (0:V)=424*X+625 := add_left_cancel hh
  have hp : 0<424*X+625 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_40_5 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(40:V)*(X+1)+3)*5) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(584*X+788) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(40:V)*(X+1)+3)*5 := h
      _ = _ := by ring
  have hz : (0:V)=584*X+788 := add_left_cancel hh
  have hp : 0<584*X+788 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_40_6 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(40:V)*(X+1)+3)*6) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(744*X+951) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(40:V)*(X+1)+3)*6 := h
      _ = _ := by ring
  have hz : (0:V)=744*X+951 := add_left_cancel hh
  have hp : 0<744*X+951 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_48_1 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(48:V)*(X+1)+3)*1) : X=7 := by
  have he : (24:V)*X=168 := by
    have hh : (192*X+27)+(24*X)=(192*X+27)+168 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(48:V)*(X+1)+3)*1 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have he' : (24:V)*X=24*7 := by rw [he]; ring
  exact mul_left_cancel₀ (by simp : (24:V)≠0) he'
 
private theorem case_48_2 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(48:V)*(X+1)+3)*2) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(168*X+363) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(48:V)*(X+1)+3)*2 := h
      _ = _ := by ring
  have hz : (0:V)=168*X+363 := add_left_cancel hh
  have hp : 0<168*X+363 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_48_3 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(48:V)*(X+1)+3)*3) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(360*X+558) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(48:V)*(X+1)+3)*3 := h
      _ = _ := by ring
  have hz : (0:V)=360*X+558 := add_left_cancel hh
  have hp : 0<360*X+558 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_48_4 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(48:V)*(X+1)+3)*4) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(552*X+753) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(48:V)*(X+1)+3)*4 := h
      _ = _ := by ring
  have hz : (0:V)=552*X+753 := add_left_cancel hh
  have hp : 0<552*X+753 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_48_5 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(48:V)*(X+1)+3)*5) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(744*X+948) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(48:V)*(X+1)+3)*5 := h
      _ = _ := by ring
  have hz : (0:V)=744*X+948 := add_left_cancel hh
  have hp : 0<744*X+948 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_48_6 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(48:V)*(X+1)+3)*6) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(936*X+1143) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(48:V)*(X+1)+3)*6 := h
      _ = _ := by ring
  have hz : (0:V)=936*X+1143 := add_left_cancel hh
  have hp : 0<936*X+1143 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_27_1 (X : V) (hX : 4≤X) (h : 27*(8*X+1)=(4*(27:V)*(X+1)+3)*1) : False := by
  have he : (108:V)*X=84 := by
    have hh : (108*X+27)+(108*X)=(108*X+27)+84 := by
      calc
        _ = 27*(8*X+1) := by ring
        _ = (4*(27:V)*(X+1)+3)*1 := h
        _ = _ := by ring
    exact add_left_cancel hh
  have hle : (108:V)*4≤108*X := Arithmetic.mul_le_mul_left hX
  rw [he] at hle
  have hlt : (84:V)<108*4 := by norm_num
  exact (not_le_of_gt hlt) hle
 
private theorem case_27_2 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(27:V)*(X+1)+3)*2) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(0*X+195) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(27:V)*(X+1)+3)*2 := h
      _ = _ := by ring
  have hz : (0:V)=0*X+195 := add_left_cancel hh
  have hp : 0<0*X+195 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_27_3 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(27:V)*(X+1)+3)*3) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(108*X+306) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(27:V)*(X+1)+3)*3 := h
      _ = _ := by ring
  have hz : (0:V)=108*X+306 := add_left_cancel hh
  have hp : 0<108*X+306 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_27_4 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(27:V)*(X+1)+3)*4) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(216*X+417) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(27:V)*(X+1)+3)*4 := h
      _ = _ := by ring
  have hz : (0:V)=216*X+417 := add_left_cancel hh
  have hp : 0<216*X+417 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_27_5 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(27:V)*(X+1)+3)*5) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(324*X+528) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(27:V)*(X+1)+3)*5 := h
      _ = _ := by ring
  have hz : (0:V)=324*X+528 := add_left_cancel hh
  have hp : 0<324*X+528 := by simp
  exact (ne_of_gt hp) hz.symm
 
private theorem case_27_6 (X : V) (_hX : 4≤X) (h : 27*(8*X+1)=(4*(27:V)*(X+1)+3)*6) : False := by
  have hh : (216*X+27)+0=(216*X+27)+(432*X+639) := by
    calc
      _ = 27*(8*X+1) := by ring
      _ = (4*(27:V)*(X+1)+3)*6 := h
      _ = _ := by ring
  have hz : (0:V)=432*X+639 := add_left_cancel hh
  have hp : 0<432*X+639 := by simp
  exact (ne_of_gt hp) hz.symm
 
theorem finite_linear_cases (X Y m : V) (hX : 4≤X)
    (hY : Y=8 ∨ Y=16 ∨ Y=24 ∨ Y=32 ∨ Y=40 ∨ Y=48 ∨ Y=27)
    (hm : m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨ m=5 ∨ m=6)
    (h : 27*(8*X+1)=(4*Y*(X+1)+3)*m) : X=7 ∧ Y=48 ∧ m=1 := by
  rcases hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (case_8_1 X hX h)
    · exact False.elim (case_8_2 X hX h)
    · exact False.elim (case_8_3 X hX h)
    · exact False.elim (case_8_4 X hX h)
    · exact False.elim (case_8_5 X hX h)
    · exact False.elim (case_8_6 X hX h)
  · rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (case_16_1 X hX h)
    · exact False.elim (case_16_2 X hX h)
    · exact False.elim (case_16_3 X hX h)
    · exact False.elim (case_16_4 X hX h)
    · exact False.elim (case_16_5 X hX h)
    · exact False.elim (case_16_6 X hX h)
  · rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (case_24_1 X hX h)
    · exact False.elim (case_24_2 X hX h)
    · exact False.elim (case_24_3 X hX h)
    · exact False.elim (case_24_4 X hX h)
    · exact False.elim (case_24_5 X hX h)
    · exact False.elim (case_24_6 X hX h)
  · rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (case_32_1 X hX h)
    · exact False.elim (case_32_2 X hX h)
    · exact False.elim (case_32_3 X hX h)
    · exact False.elim (case_32_4 X hX h)
    · exact False.elim (case_32_5 X hX h)
    · exact False.elim (case_32_6 X hX h)
  · rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (case_40_1 X hX h)
    · exact False.elim (case_40_2 X hX h)
    · exact False.elim (case_40_3 X hX h)
    · exact False.elim (case_40_4 X hX h)
    · exact False.elim (case_40_5 X hX h)
    · exact False.elim (case_40_6 X hX h)
  · rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨case_48_1 X hX h,rfl,rfl⟩
    · exact False.elim (case_48_2 X hX h)
    · exact False.elim (case_48_3 X hX h)
    · exact False.elim (case_48_4 X hX h)
    · exact False.elim (case_48_5 X hX h)
    · exact False.elim (case_48_6 X hX h)
  · rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (case_27_1 X hX h)
    · exact False.elim (case_27_2 X hX h)
    · exact False.elim (case_27_3 X hX h)
    · exact False.elim (case_27_4 X hX h)
    · exact False.elim (case_27_5 X hX h)
    · exact False.elim (case_27_6 X hX h)
end DiophantineConsistency.AdaptiveGap85NegativeLinearOptimized
