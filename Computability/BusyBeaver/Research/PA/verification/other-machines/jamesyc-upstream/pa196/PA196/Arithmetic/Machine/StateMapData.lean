module
public import PA196.Arithmetic.Machine.PAStepFormula
public import PA196.Arithmetic.Machine.Exact.PAStepFormula
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA196.Arithmetic.Machine.StateMap
def sourceTag (q : Exact.WorkingState) : Nat := literalTags.getD q.val 215
theorem sourceTag_lt : ∀ q : Exact.WorkingState, sourceTag q < 215 := by decide +kernel
def auxState (q : Exact.WorkingState) : WorkingState := ⟨sourceTag q,sourceTag_lt q⟩
def auxControl : Exact.Control → Control
  | none => none
  | some q => some (auxState q)
def inverseEntries : List (Nat × Nat) := [(0,0), (1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (9,8), (10,9), (11,10), (12,11), (13,12), (14,13), (15,14), (16,15), (17,16), (18,17), (19,18), (20,19), (21,20), (22,21), (23,22), (24,23), (25,24), (26,25), (27,26), (28,27), (29,28), (30,29), (31,30), (32,31), (33,32), (34,33), (35,34), (36,35), (37,36), (38,37), (39,38), (40,39), (41,40), (42,41), (43,42), (44,43), (45,44), (46,45), (47,46), (48,47), (49,48), (51,49), (53,50), (54,51), (55,52), (56,53), (57,54), (58,55), (59,56), (60,57), (61,58), (62,59), (63,60), (64,61), (66,62), (68,63), (69,64), (70,65), (71,66), (72,67), (73,68), (74,69), (76,70), (77,71), (78,72), (79,73), (80,74), (81,75), (84,76), (85,77), (87,78), (88,79), (89,80), (90,81), (91,82), (92,83), (93,84), (94,85), (95,86), (96,87), (97,88), (98,89), (99,90), (100,91), (101,92), (102,93), (103,94), (104,95), (105,96), (106,97), (107,98), (109,99), (110,100), (115,101), (116,102), (117,103), (118,104), (119,105), (120,106), (121,107), (123,108), (130,109), (131,110), (132,111), (133,112), (135,113), (151,114), (153,115), (155,116), (163,117), (166,118), (170,119), (173,120), (175,121), (177,122), (178,123), (179,124), (180,125), (192,126), (193,127), (196,128), (199,129), (202,130), (203,131), (211,132), (213,133), (8,134), (50,135), (52,136), (65,137), (67,138), (75,139), (82,140), (83,141), (86,142), (108,143), (111,144), (112,145), (113,146), (114,147), (122,148), (124,149), (125,150), (126,151), (127,152), (128,153), (129,154), (134,155), (136,156), (137,157), (138,158), (139,159), (140,160), (141,161), (142,162), (143,163), (144,164), (145,165), (146,166), (147,167), (148,168), (149,169), (150,170), (152,171), (154,172), (156,173), (157,174), (158,175), (159,176), (160,177), (161,178), (162,179), (164,180), (165,181), (167,182), (168,183), (169,184), (171,185), (172,186), (174,187), (176,188), (181,189), (182,190), (183,191), (184,192), (185,193), (186,194), (187,195), (215,196)]
def lookupNat : List (Nat × Nat) → Nat → Nat
  | [],_ => 0
  | (a,b)::rest,q => if q=a then b else lookupNat rest q
def literalIndex (q : Nat) : Nat := lookupNat inverseEntries q
theorem inverse_code (c : Exact.Control) :
    literalIndex (PA.StepFormula.controlCode (auxControl c)) = Exact.PA.StepFormula.controlCode c := by
  cases c with
  | none => decide +kernel
  | some q => exact (by decide +kernel : ∀ q : Exact.WorkingState,
      literalIndex (PA.StepFormula.controlCode (auxControl (some q))) =
        Exact.PA.StepFormula.controlCode (some q)) q
theorem inverse_zero : literalIndex 0=0 := rfl
theorem inverse_halt : literalIndex 215=196 := by decide +kernel
theorem row_binding : ∀ (q : Exact.WorkingState) (b : Bool),
    row (auxState q) b = ⟨(Exact.row q b).write,(Exact.row q b).right,auxControl (Exact.row q b).next⟩ := by
  decide +kernel
theorem aux_complete : ∀ s : WorkingState, active s → ∃ q : Exact.WorkingState, auxState q=s := by
  decide +kernel
def NotPaddingNat (q : Nat) : Prop := q≠188 ∧ q≠189 ∧ q≠190 ∧ q≠191 ∧ q≠194 ∧ q≠195 ∧ q≠197 ∧ q≠198 ∧ q≠200 ∧ q≠201 ∧ q≠204 ∧ q≠205 ∧ q≠206 ∧ q≠207 ∧ q≠208 ∧ q≠209 ∧ q≠210 ∧ q≠212 ∧ q≠214
instance (q : Nat) : Decidable (NotPaddingNat q) := inferInstanceAs (Decidable (_ ∧ _))
theorem active_iff : ∀ s : WorkingState, active s ↔ NotPaddingNat s.val := by decide +kernel
theorem target_not_padding : ∀ (s : WorkingState) (b : Bool), active s →
    NotPaddingNat (PA.StepFormula.controlCode (row s b).next) := by decide +kernel
#print axioms row_binding
#print axioms aux_complete
end PA196.Arithmetic.Machine.StateMap
