import BusyBeaver.ZFC.KSource215Programs

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def sTree0 : Tree := .node (.leaf (.decnz 8)) (.leaf (.brk 1))

theorem sTree0_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 0 = sTree0 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 8)) (.leaf (.brk 1)) = Tree.node (.leaf (.decnz 8)) (.leaf (.brk 1))
    rfl

def sTree1 : Tree := .node (.leaf (.inc 6)) (.leaf (.cont 3))

theorem sTree1_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 1 = sTree1 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 6)) (.leaf (.cont 3)) = Tree.node (.leaf (.inc 6)) (.leaf (.cont 3))
    rfl

def sTree2 : Tree := .node (.leaf (.inc 8)) sTree1

theorem sTree2_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 2 = sTree2 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 8)) (toTree p215 f 1) = Tree.node (.leaf (.inc 8)) sTree1
    simp only [sTree1_eq f (by omega)]

def sTree3 : Tree := .node (.leaf (.decnz 0)) sTree2

theorem sTree3_eq (f : Nat) (hf : 3 ≤ f) :
    toTree p215 f 3 = sTree3 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 0)) (toTree p215 f 2) = Tree.node (.leaf (.decnz 0)) sTree2
    simp only [sTree2_eq f (by omega)]

def sTree4 : Tree := .node (.leaf (.decnz 6)) (.leaf (.cont 2))

theorem sTree4_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 4 = sTree4 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (.leaf (.cont 2)) = Tree.node (.leaf (.decnz 6)) (.leaf (.cont 2))
    rfl

def sTree5 : Tree := .node (.leaf (.inc 0)) sTree4

theorem sTree5_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 5 = sTree5 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 0)) (toTree p215 f 4) = Tree.node (.leaf (.inc 0)) sTree4
    simp only [sTree4_eq f (by omega)]

def sTree6 : Tree := .node sTree3 sTree5

theorem sTree6_eq (f : Nat) (hf : 4 ≤ f) :
    toTree p215 f 6 = sTree6 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 3) (toTree p215 f 5) = Tree.node sTree3 sTree5
    simp only [sTree3_eq f (by omega), sTree5_eq f (by omega)]

def sTree7 : Tree := .node sTree0 sTree6

theorem sTree7_eq (f : Nat) (hf : 5 ≤ f) :
    toTree p215 f 7 = sTree7 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 0) (toTree p215 f 6) = Tree.node sTree0 sTree6
    simp only [sTree0_eq f (by omega), sTree6_eq f (by omega)]

def sTree8 : Tree := .node (.leaf (.decnz 6)) (.leaf (.brk 1))

theorem sTree8_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 8 = sTree8 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (.leaf (.brk 1)) = Tree.node (.leaf (.decnz 6)) (.leaf (.brk 1))
    rfl

def sTree9 : Tree := .node (.leaf (.inc 6)) (.leaf (.cont 2))

theorem sTree9_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 9 = sTree9 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 6)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 6)) (.leaf (.cont 2))
    rfl

def sTree10 : Tree := .node (.leaf (.decnz 7)) sTree9

theorem sTree10_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 10 = sTree10 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 7)) (toTree p215 f 9) = Tree.node (.leaf (.decnz 7)) sTree9
    simp only [sTree9_eq f (by omega)]

def sTree11 : Tree := .node sTree8 sTree10

theorem sTree11_eq (f : Nat) (hf : 3 ≤ f) :
    toTree p215 f 11 = sTree11 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 8) (toTree p215 f 10) = Tree.node sTree8 sTree10
    simp only [sTree8_eq f (by omega), sTree10_eq f (by omega)]

def sTree12 : Tree := .node sTree11 (.leaf (.cont 3))

theorem sTree12_eq (f : Nat) (hf : 4 ≤ f) :
    toTree p215 f 12 = sTree12 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 11) (.leaf (.cont 3)) = Tree.node sTree11 (.leaf (.cont 3))
    simp only [sTree11_eq f (by omega)]

def sTree13 : Tree := .node (.leaf (.inc 7)) sTree12

theorem sTree13_eq (f : Nat) (hf : 5 ≤ f) :
    toTree p215 f 13 = sTree13 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 7)) (toTree p215 f 12) = Tree.node (.leaf (.inc 7)) sTree12
    simp only [sTree12_eq f (by omega)]

def sTree14 : Tree := .node (.leaf (.decnz 8)) sTree13

theorem sTree14_eq (f : Nat) (hf : 6 ≤ f) :
    toTree p215 f 14 = sTree14 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 8)) (toTree p215 f 13) = Tree.node (.leaf (.decnz 8)) sTree13
    simp only [sTree13_eq f (by omega)]

def sTree15 : Tree := .node (.leaf (.inc 8)) (.leaf (.cont 2))

theorem sTree15_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 15 = sTree15 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 8)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 8)) (.leaf (.cont 2))
    rfl

def sTree16 : Tree := .node (.leaf (.decnz 7)) sTree15

theorem sTree16_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 16 = sTree16 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 7)) (toTree p215 f 15) = Tree.node (.leaf (.decnz 7)) sTree15
    simp only [sTree15_eq f (by omega)]

def sTree17 : Tree := .node sTree14 sTree16

theorem sTree17_eq (f : Nat) (hf : 7 ≤ f) :
    toTree p215 f 17 = sTree17 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 14) (toTree p215 f 16) = Tree.node sTree14 sTree16
    simp only [sTree14_eq f (by omega), sTree16_eq f (by omega)]

def sTree18 : Tree := .node (.leaf (.inc 3)) (.leaf (.cont 2))

theorem sTree18_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 18 = sTree18 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 3)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 3)) (.leaf (.cont 2))
    rfl

def sTree19 : Tree := .node (.leaf (.decnz 6)) sTree18

theorem sTree19_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 19 = sTree19 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (toTree p215 f 18) = Tree.node (.leaf (.decnz 6)) sTree18
    simp only [sTree18_eq f (by omega)]

def sTree20 : Tree := .node sTree17 sTree19

theorem sTree20_eq (f : Nat) (hf : 8 ≤ f) :
    toTree p215 f 20 = sTree20 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 17) (toTree p215 f 19) = Tree.node sTree17 sTree19
    simp only [sTree17_eq f (by omega), sTree19_eq f (by omega)]

def sTree21 : Tree := .node (.leaf (.decnz 1)) sTree9

theorem sTree21_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 21 = sTree21 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 1)) (toTree p215 f 9) = Tree.node (.leaf (.decnz 1)) sTree9
    simp only [sTree9_eq f (by omega)]

def sTree22 : Tree := .node (.leaf (.inc 1)) (.leaf (.cont 2))

theorem sTree22_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 22 = sTree22 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 1)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 1)) (.leaf (.cont 2))
    rfl

def sTree23 : Tree := .node (.leaf (.decnz 2)) sTree22

theorem sTree23_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 23 = sTree23 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 2)) (toTree p215 f 22) = Tree.node (.leaf (.decnz 2)) sTree22
    simp only [sTree22_eq f (by omega)]

def sTree24 : Tree := .node (.leaf (.inc 7)) sTree1

theorem sTree24_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 24 = sTree24 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 7)) (toTree p215 f 1) = Tree.node (.leaf (.inc 7)) sTree1
    simp only [sTree1_eq f (by omega)]

def sTree25 : Tree := .node (.leaf (.decnz 1)) sTree24

theorem sTree25_eq (f : Nat) (hf : 3 ≤ f) :
    toTree p215 f 25 = sTree25 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 1)) (toTree p215 f 24) = Tree.node (.leaf (.decnz 1)) sTree24
    simp only [sTree24_eq f (by omega)]

def sTree26 : Tree := .node (.leaf (.decnz 6)) sTree22

theorem sTree26_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 26 = sTree26 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (toTree p215 f 22) = Tree.node (.leaf (.decnz 6)) sTree22
    simp only [sTree22_eq f (by omega)]

def sTree27 : Tree := .node (.leaf (.inc 7)) sTree26

theorem sTree27_eq (f : Nat) (hf : 3 ≤ f) :
    toTree p215 f 27 = sTree27 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 7)) (toTree p215 f 26) = Tree.node (.leaf (.inc 7)) sTree26
    simp only [sTree26_eq f (by omega)]

def sTree28 : Tree := .node sTree27 (.leaf (.cont 3))

theorem sTree28_eq (f : Nat) (hf : 4 ≤ f) :
    toTree p215 f 28 = sTree28 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 27) (.leaf (.cont 3)) = Tree.node sTree27 (.leaf (.cont 3))
    simp only [sTree27_eq f (by omega)]

def sTree29 : Tree := .node (.leaf (.decnz 6)) sTree28

theorem sTree29_eq (f : Nat) (hf : 5 ≤ f) :
    toTree p215 f 29 = sTree29 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (toTree p215 f 28) = Tree.node (.leaf (.decnz 6)) sTree28
    simp only [sTree28_eq f (by omega)]

def sTree30 : Tree := .node sTree25 sTree29

theorem sTree30_eq (f : Nat) (hf : 6 ≤ f) :
    toTree p215 f 30 = sTree30 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 25) (toTree p215 f 29) = Tree.node sTree25 sTree29
    simp only [sTree25_eq f (by omega), sTree29_eq f (by omega)]

def sTree31 : Tree := .node (.leaf (.inc 2)) (.leaf (.cont 2))

theorem sTree31_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 31 = sTree31 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 2)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 2)) (.leaf (.cont 2))
    rfl

def sTree32 : Tree := .node (.leaf (.decnz 7)) sTree31

theorem sTree32_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 32 = sTree32 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 7)) (toTree p215 f 31) = Tree.node (.leaf (.decnz 7)) sTree31
    simp only [sTree31_eq f (by omega)]

def sTree33 : Tree := .node sTree30 sTree32

theorem sTree33_eq (f : Nat) (hf : 7 ≤ f) :
    toTree p215 f 33 = sTree33 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 30) (toTree p215 f 32) = Tree.node sTree30 sTree32
    simp only [sTree30_eq f (by omega), sTree32_eq f (by omega)]

def sTree34 : Tree := .node sTree23 sTree33

theorem sTree34_eq (f : Nat) (hf : 8 ≤ f) :
    toTree p215 f 34 = sTree34 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 23) (toTree p215 f 33) = Tree.node sTree23 sTree33
    simp only [sTree23_eq f (by omega), sTree33_eq f (by omega)]

def sTree35 : Tree := .node sTree21 sTree34

theorem sTree35_eq (f : Nat) (hf : 9 ≤ f) :
    toTree p215 f 35 = sTree35 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 21) (toTree p215 f 34) = Tree.node sTree21 sTree34
    simp only [sTree21_eq f (by omega), sTree34_eq f (by omega)]

def sTree36 : Tree := .node (.leaf (.inc 1)) sTree1

theorem sTree36_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 36 = sTree36 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 1)) (toTree p215 f 1) = Tree.node (.leaf (.inc 1)) sTree1
    simp only [sTree1_eq f (by omega)]

def sTree37 : Tree := .node (.leaf (.decnz 4)) sTree36

theorem sTree37_eq (f : Nat) (hf : 3 ≤ f) :
    toTree p215 f 37 = sTree37 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 4)) (toTree p215 f 36) = Tree.node (.leaf (.decnz 4)) sTree36
    simp only [sTree36_eq f (by omega)]

def sTree38 : Tree := .node (.leaf (.inc 4)) (.leaf (.cont 2))

theorem sTree38_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 38 = sTree38 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 4)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 4)) (.leaf (.cont 2))
    rfl

def sTree39 : Tree := .node (.leaf (.decnz 6)) sTree38

theorem sTree39_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 39 = sTree39 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (toTree p215 f 38) = Tree.node (.leaf (.decnz 6)) sTree38
    simp only [sTree38_eq f (by omega)]

def sTree40 : Tree := .node sTree37 sTree39

theorem sTree40_eq (f : Nat) (hf : 4 ≤ f) :
    toTree p215 f 40 = sTree40 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 37) (toTree p215 f 39) = Tree.node sTree37 sTree39
    simp only [sTree37_eq f (by omega), sTree39_eq f (by omega)]

def sTree41 : Tree := .node sTree35 sTree40

theorem sTree41_eq (f : Nat) (hf : 10 ≤ f) :
    toTree p215 f 41 = sTree41 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 35) (toTree p215 f 40) = Tree.node sTree35 sTree40
    simp only [sTree35_eq f (by omega), sTree40_eq f (by omega)]

def sTree42 : Tree := .node (.leaf (.decnz 5)) sTree36

theorem sTree42_eq (f : Nat) (hf : 3 ≤ f) :
    toTree p215 f 42 = sTree42 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 5)) (toTree p215 f 36) = Tree.node (.leaf (.decnz 5)) sTree36
    simp only [sTree36_eq f (by omega)]

def sTree43 : Tree := .node (.leaf (.inc 5)) (.leaf (.cont 2))

theorem sTree43_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 43 = sTree43 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 5)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 5)) (.leaf (.cont 2))
    rfl

def sTree44 : Tree := .node (.leaf (.decnz 6)) sTree43

theorem sTree44_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 44 = sTree44 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (toTree p215 f 43) = Tree.node (.leaf (.decnz 6)) sTree43
    simp only [sTree43_eq f (by omega)]

def sTree45 : Tree := .node sTree42 sTree44

theorem sTree45_eq (f : Nat) (hf : 4 ≤ f) :
    toTree p215 f 45 = sTree45 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 42) (toTree p215 f 44) = Tree.node sTree42 sTree44
    simp only [sTree42_eq f (by omega), sTree44_eq f (by omega)]

def sTree46 : Tree := .node sTree35 sTree45

theorem sTree46_eq (f : Nat) (hf : 10 ≤ f) :
    toTree p215 f 46 = sTree46 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 35) (toTree p215 f 45) = Tree.node sTree35 sTree45
    simp only [sTree35_eq f (by omega), sTree45_eq f (by omega)]

def sTree47 : Tree := .node sTree41 sTree46

theorem sTree47_eq (f : Nat) (hf : 11 ≤ f) :
    toTree p215 f 47 = sTree47 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 41) (toTree p215 f 46) = Tree.node sTree41 sTree46
    simp only [sTree41_eq f (by omega), sTree46_eq f (by omega)]

def sTree48 : Tree := .node (.leaf (.decnz 2)) sTree13

theorem sTree48_eq (f : Nat) (hf : 6 ≤ f) :
    toTree p215 f 48 = sTree48 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 2)) (toTree p215 f 13) = Tree.node (.leaf (.decnz 2)) sTree13
    simp only [sTree13_eq f (by omega)]

def sTree49 : Tree := .node sTree48 sTree32

theorem sTree49_eq (f : Nat) (hf : 7 ≤ f) :
    toTree p215 f 49 = sTree49 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 48) (toTree p215 f 32) = Tree.node sTree48 sTree32
    simp only [sTree48_eq f (by omega), sTree32_eq f (by omega)]

def sTree50 : Tree := .node (.leaf (.inc 1)) (.leaf (.inc 1))

theorem sTree50_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 50 = sTree50 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 1)) (.leaf (.inc 1)) = Tree.node (.leaf (.inc 1)) (.leaf (.inc 1))
    rfl

def sTree51 : Tree := .node sTree50 sTree50

theorem sTree51_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 51 = sTree51 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 50) (toTree p215 f 50) = Tree.node sTree50 sTree50
    simp only [sTree50_eq f (by omega)]

def sTree52 : Tree := .node sTree51 (.leaf (.cont 2))

theorem sTree52_eq (f : Nat) (hf : 3 ≤ f) :
    toTree p215 f 52 = sTree52 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 51) (.leaf (.cont 2)) = Tree.node sTree51 (.leaf (.cont 2))
    simp only [sTree51_eq f (by omega)]

def sTree53 : Tree := .node (.leaf (.decnz 7)) sTree52

theorem sTree53_eq (f : Nat) (hf : 4 ≤ f) :
    toTree p215 f 53 = sTree53 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 7)) (toTree p215 f 52) = Tree.node (.leaf (.decnz 7)) sTree52
    simp only [sTree52_eq f (by omega)]

def sTree54 : Tree := .node sTree30 sTree53

theorem sTree54_eq (f : Nat) (hf : 7 ≤ f) :
    toTree p215 f 54 = sTree54 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 30) (toTree p215 f 53) = Tree.node sTree30 sTree53
    simp only [sTree30_eq f (by omega), sTree53_eq f (by omega)]

def sTree55 : Tree := .node sTree49 sTree54

theorem sTree55_eq (f : Nat) (hf : 8 ≤ f) :
    toTree p215 f 55 = sTree55 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 49) (toTree p215 f 54) = Tree.node sTree49 sTree54
    simp only [sTree49_eq f (by omega), sTree54_eq f (by omega)]

def sTree56 : Tree := .node sTree55 sTree50

theorem sTree56_eq (f : Nat) (hf : 9 ≤ f) :
    toTree p215 f 56 = sTree56 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 55) (toTree p215 f 50) = Tree.node sTree55 sTree50
    simp only [sTree55_eq f (by omega), sTree50_eq f (by omega)]

def sTree57 : Tree := .node sTree47 sTree56

theorem sTree57_eq (f : Nat) (hf : 12 ≤ f) :
    toTree p215 f 57 = sTree57 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 47) (toTree p215 f 56) = Tree.node sTree47 sTree56
    simp only [sTree47_eq f (by omega), sTree56_eq f (by omega)]

def sTree58 : Tree := .node (.leaf (.decnz 3)) sTree36

theorem sTree58_eq (f : Nat) (hf : 3 ≤ f) :
    toTree p215 f 58 = sTree58 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 3)) (toTree p215 f 36) = Tree.node (.leaf (.decnz 3)) sTree36
    simp only [sTree36_eq f (by omega)]

def sTree59 : Tree := .node sTree58 sTree19

theorem sTree59_eq (f : Nat) (hf : 4 ≤ f) :
    toTree p215 f 59 = sTree59 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 58) (toTree p215 f 19) = Tree.node sTree58 sTree19
    simp only [sTree58_eq f (by omega), sTree19_eq f (by omega)]

def sTree60 : Tree := .node sTree35 sTree59

theorem sTree60_eq (f : Nat) (hf : 10 ≤ f) :
    toTree p215 f 60 = sTree60 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 35) (toTree p215 f 59) = Tree.node sTree35 sTree59
    simp only [sTree35_eq f (by omega), sTree59_eq f (by omega)]

def sTree61 : Tree := .node sTree60 sTree41

theorem sTree61_eq (f : Nat) (hf : 11 ≤ f) :
    toTree p215 f 61 = sTree61 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 60) (toTree p215 f 41) = Tree.node sTree60 sTree41
    simp only [sTree60_eq f (by omega), sTree41_eq f (by omega)]

def sTree62 : Tree := .node sTree17 sTree44

theorem sTree62_eq (f : Nat) (hf : 8 ≤ f) :
    toTree p215 f 62 = sTree62 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 17) (toTree p215 f 44) = Tree.node sTree17 sTree44
    simp only [sTree17_eq f (by omega), sTree44_eq f (by omega)]

def sTree63 : Tree := .node sTree39 sTree41

theorem sTree63_eq (f : Nat) (hf : 11 ≤ f) :
    toTree p215 f 63 = sTree63 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 39) (toTree p215 f 41) = Tree.node sTree39 sTree41
    simp only [sTree39_eq f (by omega), sTree41_eq f (by omega)]

def sTree64 : Tree := .node sTree17 sTree63

theorem sTree64_eq (f : Nat) (hf : 12 ≤ f) :
    toTree p215 f 64 = sTree64 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 17) (toTree p215 f 63) = Tree.node sTree17 sTree63
    simp only [sTree17_eq f (by omega), sTree63_eq f (by omega)]

def sTree65 : Tree := .node sTree64 sTree55

theorem sTree65_eq (f : Nat) (hf : 13 ≤ f) :
    toTree p215 f 65 = sTree65 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 64) (toTree p215 f 55) = Tree.node sTree64 sTree55
    simp only [sTree64_eq f (by omega), sTree55_eq f (by omega)]

def sTree66 : Tree := .node sTree41 sTree60

theorem sTree66_eq (f : Nat) (hf : 11 ≤ f) :
    toTree p215 f 66 = sTree66 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 41) (toTree p215 f 60) = Tree.node sTree41 sTree60
    simp only [sTree41_eq f (by omega), sTree60_eq f (by omega)]

def sTree67 : Tree := .node sTree65 sTree66

theorem sTree67_eq (f : Nat) (hf : 14 ≤ f) :
    toTree p215 f 67 = sTree67 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 65) (toTree p215 f 66) = Tree.node sTree65 sTree66
    simp only [sTree65_eq f (by omega), sTree66_eq f (by omega)]

def sTree68 : Tree := .node sTree55 sTree67

theorem sTree68_eq (f : Nat) (hf : 15 ≤ f) :
    toTree p215 f 68 = sTree68 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 55) (toTree p215 f 67) = Tree.node sTree55 sTree67
    simp only [sTree55_eq f (by omega), sTree67_eq f (by omega)]

def sTree69 : Tree := .node sTree62 sTree68

theorem sTree69_eq (f : Nat) (hf : 16 ≤ f) :
    toTree p215 f 69 = sTree69 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 62) (toTree p215 f 68) = Tree.node sTree62 sTree68
    simp only [sTree62_eq f (by omega), sTree68_eq f (by omega)]

def sTree70 : Tree := .node sTree46 sTree60

theorem sTree70_eq (f : Nat) (hf : 11 ≤ f) :
    toTree p215 f 70 = sTree70 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 46) (toTree p215 f 60) = Tree.node sTree46 sTree60
    simp only [sTree46_eq f (by omega), sTree60_eq f (by omega)]

def sTree71 : Tree := .node sTree55 sTree70

theorem sTree71_eq (f : Nat) (hf : 12 ≤ f) :
    toTree p215 f 71 = sTree71 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 55) (toTree p215 f 70) = Tree.node sTree55 sTree70
    simp only [sTree55_eq f (by omega), sTree70_eq f (by omega)]

def sTree72 : Tree := .node sTree55 sTree55

theorem sTree72_eq (f : Nat) (hf : 9 ≤ f) :
    toTree p215 f 72 = sTree72 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 55) (toTree p215 f 55) = Tree.node sTree55 sTree55
    simp only [sTree55_eq f (by omega)]

def sTree73 : Tree := .node sTree55 (.leaf (.inc 1))

theorem sTree73_eq (f : Nat) (hf : 9 ≤ f) :
    toTree p215 f 73 = sTree73 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 55) (.leaf (.inc 1)) = Tree.node sTree55 (.leaf (.inc 1))
    simp only [sTree55_eq f (by omega)]

def sTree74 : Tree := .node sTree61 sTree73

theorem sTree74_eq (f : Nat) (hf : 12 ≤ f) :
    toTree p215 f 74 = sTree74 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 61) (toTree p215 f 73) = Tree.node sTree61 sTree73
    simp only [sTree61_eq f (by omega), sTree73_eq f (by omega)]

def sTree75 : Tree := .node sTree60 sTree46

theorem sTree75_eq (f : Nat) (hf : 11 ≤ f) :
    toTree p215 f 75 = sTree75 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 60) (toTree p215 f 46) = Tree.node sTree60 sTree46
    simp only [sTree60_eq f (by omega), sTree46_eq f (by omega)]

def sTree76 : Tree := .node sTree75 sTree73

theorem sTree76_eq (f : Nat) (hf : 12 ≤ f) :
    toTree p215 f 76 = sTree76 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 75) (toTree p215 f 73) = Tree.node sTree75 sTree73
    simp only [sTree75_eq f (by omega), sTree73_eq f (by omega)]

def sTree77 : Tree := .node sTree50 sTree76

theorem sTree77_eq (f : Nat) (hf : 13 ≤ f) :
    toTree p215 f 77 = sTree77 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 50) (toTree p215 f 76) = Tree.node sTree50 sTree76
    simp only [sTree50_eq f (by omega), sTree76_eq f (by omega)]

def sTree78 : Tree := .node sTree74 sTree77

theorem sTree78_eq (f : Nat) (hf : 14 ≤ f) :
    toTree p215 f 78 = sTree78 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 74) (toTree p215 f 77) = Tree.node sTree74 sTree77
    simp only [sTree74_eq f (by omega), sTree77_eq f (by omega)]

def sTree79 : Tree := .node sTree55 sTree78

theorem sTree79_eq (f : Nat) (hf : 15 ≤ f) :
    toTree p215 f 79 = sTree79 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 55) (toTree p215 f 78) = Tree.node sTree55 sTree78
    simp only [sTree55_eq f (by omega), sTree78_eq f (by omega)]

def sTree80 : Tree := .node sTree47 sTree73

theorem sTree80_eq (f : Nat) (hf : 12 ≤ f) :
    toTree p215 f 80 = sTree80 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 47) (toTree p215 f 73) = Tree.node sTree47 sTree73
    simp only [sTree47_eq f (by omega), sTree73_eq f (by omega)]

def sTree81 : Tree := .node sTree57 (.leaf (.inc 1))

theorem sTree81_eq (f : Nat) (hf : 13 ≤ f) :
    toTree p215 f 81 = sTree81 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 57) (.leaf (.inc 1)) = Tree.node sTree57 (.leaf (.inc 1))
    simp only [sTree57_eq f (by omega)]

def sTree82 : Tree := .node sTree80 sTree81

theorem sTree82_eq (f : Nat) (hf : 14 ≤ f) :
    toTree p215 f 82 = sTree82 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 80) (toTree p215 f 81) = Tree.node sTree80 sTree81
    simp only [sTree80_eq f (by omega), sTree81_eq f (by omega)]

def sTree83 : Tree := .node sTree50 sTree82

theorem sTree83_eq (f : Nat) (hf : 15 ≤ f) :
    toTree p215 f 83 = sTree83 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 50) (toTree p215 f 82) = Tree.node sTree50 sTree82
    simp only [sTree50_eq f (by omega), sTree82_eq f (by omega)]

def sTree84 : Tree := .node sTree72 sTree41

theorem sTree84_eq (f : Nat) (hf : 11 ≤ f) :
    toTree p215 f 84 = sTree84 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 72) (toTree p215 f 41) = Tree.node sTree72 sTree41
    simp only [sTree72_eq f (by omega), sTree41_eq f (by omega)]

def sTree85 : Tree := .node sTree66 sTree56

theorem sTree85_eq (f : Nat) (hf : 12 ≤ f) :
    toTree p215 f 85 = sTree85 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 66) (toTree p215 f 56) = Tree.node sTree66 sTree56
    simp only [sTree66_eq f (by omega), sTree56_eq f (by omega)]

def sTree86 : Tree := .node sTree35 (.leaf (.inc 1))

theorem sTree86_eq (f : Nat) (hf : 10 ≤ f) :
    toTree p215 f 86 = sTree86 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 35) (.leaf (.inc 1)) = Tree.node sTree35 (.leaf (.inc 1))
    simp only [sTree35_eq f (by omega)]

def sTree87 : Tree := .node sTree55 sTree56

theorem sTree87_eq (f : Nat) (hf : 10 ≤ f) :
    toTree p215 f 87 = sTree87 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 55) (toTree p215 f 56) = Tree.node sTree55 sTree56
    simp only [sTree55_eq f (by omega), sTree56_eq f (by omega)]

def sTree88 : Tree := .node sTree86 sTree55

theorem sTree88_eq (f : Nat) (hf : 11 ≤ f) :
    toTree p215 f 88 = sTree88 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 86) (toTree p215 f 55) = Tree.node sTree86 sTree55
    simp only [sTree86_eq f (by omega), sTree55_eq f (by omega)]

def sTree89 : Tree := .node sTree87 sTree88

theorem sTree89_eq (f : Nat) (hf : 12 ≤ f) :
    toTree p215 f 89 = sTree89 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 87) (toTree p215 f 88) = Tree.node sTree87 sTree88
    simp only [sTree87_eq f (by omega), sTree88_eq f (by omega)]

def sTree90 : Tree := .node sTree86 sTree89

theorem sTree90_eq (f : Nat) (hf : 13 ≤ f) :
    toTree p215 f 90 = sTree90 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 86) (toTree p215 f 89) = Tree.node sTree86 sTree89
    simp only [sTree86_eq f (by omega), sTree89_eq f (by omega)]

def sTree91 : Tree := .node sTree90 sTree60

theorem sTree91_eq (f : Nat) (hf : 14 ≤ f) :
    toTree p215 f 91 = sTree91 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 90) (toTree p215 f 60) = Tree.node sTree90 sTree60
    simp only [sTree90_eq f (by omega), sTree60_eq f (by omega)]

def sTree92 : Tree := .node sTree85 sTree91

theorem sTree92_eq (f : Nat) (hf : 15 ≤ f) :
    toTree p215 f 92 = sTree92 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 85) (toTree p215 f 91) = Tree.node sTree85 sTree91
    simp only [sTree85_eq f (by omega), sTree91_eq f (by omega)]

def sTree93 : Tree := .node sTree84 sTree92

theorem sTree93_eq (f : Nat) (hf : 16 ≤ f) :
    toTree p215 f 93 = sTree93 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 84) (toTree p215 f 92) = Tree.node sTree84 sTree92
    simp only [sTree84_eq f (by omega), sTree92_eq f (by omega)]

def sTree94 : Tree := .node sTree56 sTree93

theorem sTree94_eq (f : Nat) (hf : 17 ≤ f) :
    toTree p215 f 94 = sTree94 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 56) (toTree p215 f 93) = Tree.node sTree56 sTree93
    simp only [sTree56_eq f (by omega), sTree93_eq f (by omega)]

def sTree95 : Tree := .node sTree83 sTree94

theorem sTree95_eq (f : Nat) (hf : 18 ≤ f) :
    toTree p215 f 95 = sTree95 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 83) (toTree p215 f 94) = Tree.node sTree83 sTree94
    simp only [sTree83_eq f (by omega), sTree94_eq f (by omega)]

def sTree96 : Tree := .node sTree84 sTree70

theorem sTree96_eq (f : Nat) (hf : 12 ≤ f) :
    toTree p215 f 96 = sTree96 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 84) (toTree p215 f 70) = Tree.node sTree84 sTree70
    simp only [sTree84_eq f (by omega), sTree70_eq f (by omega)]

def sTree97 : Tree := .node sTree80 sTree96

theorem sTree97_eq (f : Nat) (hf : 13 ≤ f) :
    toTree p215 f 97 = sTree97 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 80) (toTree p215 f 96) = Tree.node sTree80 sTree96
    simp only [sTree80_eq f (by omega), sTree96_eq f (by omega)]

def sTree98 : Tree := .node sTree79 sTree97

theorem sTree98_eq (f : Nat) (hf : 16 ≤ f) :
    toTree p215 f 98 = sTree98 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 79) (toTree p215 f 97) = Tree.node sTree79 sTree97
    simp only [sTree79_eq f (by omega), sTree97_eq f (by omega)]

def sTree99 : Tree := .node sTree56 sTree55

theorem sTree99_eq (f : Nat) (hf : 10 ≤ f) :
    toTree p215 f 99 = sTree99 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 56) (toTree p215 f 55) = Tree.node sTree56 sTree55
    simp only [sTree56_eq f (by omega), sTree55_eq f (by omega)]

def sTree100 : Tree := .node sTree99 sTree81

theorem sTree100_eq (f : Nat) (hf : 14 ≤ f) :
    toTree p215 f 100 = sTree100 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 99) (toTree p215 f 81) = Tree.node sTree99 sTree81
    simp only [sTree99_eq f (by omega), sTree81_eq f (by omega)]

def sTree101 : Tree := .node sTree85 sTree100

theorem sTree101_eq (f : Nat) (hf : 15 ≤ f) :
    toTree p215 f 101 = sTree101 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 85) (toTree p215 f 100) = Tree.node sTree85 sTree100
    simp only [sTree85_eq f (by omega), sTree100_eq f (by omega)]

def sTree102 : Tree := .node sTree46 sTree101

theorem sTree102_eq (f : Nat) (hf : 16 ≤ f) :
    toTree p215 f 102 = sTree102 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 46) (toTree p215 f 101) = Tree.node sTree46 sTree101
    simp only [sTree46_eq f (by omega), sTree101_eq f (by omega)]

def sTree103 : Tree := .node sTree74 sTree76

theorem sTree103_eq (f : Nat) (hf : 13 ≤ f) :
    toTree p215 f 103 = sTree103 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 74) (toTree p215 f 76) = Tree.node sTree74 sTree76
    simp only [sTree74_eq f (by omega), sTree76_eq f (by omega)]

def sTree104 : Tree := .node sTree102 sTree103

theorem sTree104_eq (f : Nat) (hf : 17 ≤ f) :
    toTree p215 f 104 = sTree104 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 102) (toTree p215 f 103) = Tree.node sTree102 sTree103
    simp only [sTree102_eq f (by omega), sTree103_eq f (by omega)]

def sTree105 : Tree := .node sTree104 sTree96

theorem sTree105_eq (f : Nat) (hf : 18 ≤ f) :
    toTree p215 f 105 = sTree105 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 104) (toTree p215 f 96) = Tree.node sTree104 sTree96
    simp only [sTree104_eq f (by omega), sTree96_eq f (by omega)]

def sTree106 : Tree := .node sTree50 sTree105

theorem sTree106_eq (f : Nat) (hf : 19 ≤ f) :
    toTree p215 f 106 = sTree106 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 50) (toTree p215 f 105) = Tree.node sTree50 sTree105
    simp only [sTree50_eq f (by omega), sTree105_eq f (by omega)]

def sTree107 : Tree := .node sTree84 sTree81

theorem sTree107_eq (f : Nat) (hf : 14 ≤ f) :
    toTree p215 f 107 = sTree107 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 84) (toTree p215 f 81) = Tree.node sTree84 sTree81
    simp only [sTree84_eq f (by omega), sTree81_eq f (by omega)]

def sTree108 : Tree := .node sTree85 sTree107

theorem sTree108_eq (f : Nat) (hf : 15 ≤ f) :
    toTree p215 f 108 = sTree108 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 85) (toTree p215 f 107) = Tree.node sTree85 sTree107
    simp only [sTree85_eq f (by omega), sTree107_eq f (by omega)]

def sTree109 : Tree := .node sTree57 sTree108

theorem sTree109_eq (f : Nat) (hf : 16 ≤ f) :
    toTree p215 f 109 = sTree109 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 57) (toTree p215 f 108) = Tree.node sTree57 sTree108
    simp only [sTree57_eq f (by omega), sTree108_eq f (by omega)]

def sTree110 : Tree := .node sTree87 sTree109

theorem sTree110_eq (f : Nat) (hf : 17 ≤ f) :
    toTree p215 f 110 = sTree110 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 87) (toTree p215 f 109) = Tree.node sTree87 sTree109
    simp only [sTree87_eq f (by omega), sTree109_eq f (by omega)]

def sTree111 : Tree := .node sTree106 sTree110

theorem sTree111_eq (f : Nat) (hf : 20 ≤ f) :
    toTree p215 f 111 = sTree111 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 106) (toTree p215 f 110) = Tree.node sTree106 sTree110
    simp only [sTree106_eq f (by omega), sTree110_eq f (by omega)]

def sTree112 : Tree := .node sTree111 sTree90

theorem sTree112_eq (f : Nat) (hf : 21 ≤ f) :
    toTree p215 f 112 = sTree112 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 111) (toTree p215 f 90) = Tree.node sTree111 sTree90
    simp only [sTree111_eq f (by omega), sTree90_eq f (by omega)]

def sTree113 : Tree := .node sTree80 sTree99

theorem sTree113_eq (f : Nat) (hf : 13 ≤ f) :
    toTree p215 f 113 = sTree113 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 80) (toTree p215 f 99) = Tree.node sTree80 sTree99
    simp only [sTree80_eq f (by omega), sTree99_eq f (by omega)]

def sTree114 : Tree := .node sTree60 sTree113

theorem sTree114_eq (f : Nat) (hf : 14 ≤ f) :
    toTree p215 f 114 = sTree114 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 60) (toTree p215 f 113) = Tree.node sTree60 sTree113
    simp only [sTree60_eq f (by omega), sTree113_eq f (by omega)]

def sTree115 : Tree := .node sTree70 sTree73

theorem sTree115_eq (f : Nat) (hf : 12 ≤ f) :
    toTree p215 f 115 = sTree115 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 70) (toTree p215 f 73) = Tree.node sTree70 sTree73
    simp only [sTree70_eq f (by omega), sTree73_eq f (by omega)]

def sTree116 : Tree := .node sTree75 sTree115

theorem sTree116_eq (f : Nat) (hf : 13 ≤ f) :
    toTree p215 f 116 = sTree116 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 75) (toTree p215 f 115) = Tree.node sTree75 sTree115
    simp only [sTree75_eq f (by omega), sTree115_eq f (by omega)]

def sTree117 : Tree := .node sTree114 sTree116

theorem sTree117_eq (f : Nat) (hf : 15 ≤ f) :
    toTree p215 f 117 = sTree117 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 114) (toTree p215 f 116) = Tree.node sTree114 sTree116
    simp only [sTree114_eq f (by omega), sTree116_eq f (by omega)]

def sTree118 : Tree := .node sTree66 sTree103

theorem sTree118_eq (f : Nat) (hf : 14 ≤ f) :
    toTree p215 f 118 = sTree118 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 66) (toTree p215 f 103) = Tree.node sTree66 sTree103
    simp only [sTree66_eq f (by omega), sTree103_eq f (by omega)]

def sTree119 : Tree := .node sTree66 sTree118

theorem sTree119_eq (f : Nat) (hf : 15 ≤ f) :
    toTree p215 f 119 = sTree119 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 66) (toTree p215 f 118) = Tree.node sTree66 sTree118
    simp only [sTree66_eq f (by omega), sTree118_eq f (by omega)]

def sTree120 : Tree := .node sTree70 sTree70

theorem sTree120_eq (f : Nat) (hf : 12 ≤ f) :
    toTree p215 f 120 = sTree120 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 70) (toTree p215 f 70) = Tree.node sTree70 sTree70
    simp only [sTree70_eq f (by omega)]

def sTree121 : Tree := .node sTree120 sTree115

theorem sTree121_eq (f : Nat) (hf : 13 ≤ f) :
    toTree p215 f 121 = sTree121 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 120) (toTree p215 f 115) = Tree.node sTree120 sTree115
    simp only [sTree120_eq f (by omega), sTree115_eq f (by omega)]

def sTree122 : Tree := .node sTree87 sTree121

theorem sTree122_eq (f : Nat) (hf : 14 ≤ f) :
    toTree p215 f 122 = sTree122 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 87) (toTree p215 f 121) = Tree.node sTree87 sTree121
    simp only [sTree87_eq f (by omega), sTree121_eq f (by omega)]

def sTree123 : Tree := .node sTree88 sTree89

theorem sTree123_eq (f : Nat) (hf : 13 ≤ f) :
    toTree p215 f 123 = sTree123 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 88) (toTree p215 f 89) = Tree.node sTree88 sTree89
    simp only [sTree88_eq f (by omega), sTree89_eq f (by omega)]

def sTree124 : Tree := .node sTree122 sTree123

theorem sTree124_eq (f : Nat) (hf : 15 ≤ f) :
    toTree p215 f 124 = sTree124 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 122) (toTree p215 f 123) = Tree.node sTree122 sTree123
    simp only [sTree122_eq f (by omega), sTree123_eq f (by omega)]

def sTree125 : Tree := .node sTree119 sTree124

theorem sTree125_eq (f : Nat) (hf : 16 ≤ f) :
    toTree p215 f 125 = sTree125 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 119) (toTree p215 f 124) = Tree.node sTree119 sTree124
    simp only [sTree119_eq f (by omega), sTree124_eq f (by omega)]

def sTree126 : Tree := .node sTree117 sTree125

theorem sTree126_eq (f : Nat) (hf : 17 ≤ f) :
    toTree p215 f 126 = sTree126 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 117) (toTree p215 f 125) = Tree.node sTree117 sTree125
    simp only [sTree117_eq f (by omega), sTree125_eq f (by omega)]

def sTree127 : Tree := .node sTree80 sTree126

theorem sTree127_eq (f : Nat) (hf : 18 ≤ f) :
    toTree p215 f 127 = sTree127 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 80) (toTree p215 f 126) = Tree.node sTree80 sTree126
    simp only [sTree80_eq f (by omega), sTree126_eq f (by omega)]

def sTree128 : Tree := .node sTree112 sTree127

theorem sTree128_eq (f : Nat) (hf : 22 ≤ f) :
    toTree p215 f 128 = sTree128 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 112) (toTree p215 f 127) = Tree.node sTree112 sTree127
    simp only [sTree112_eq f (by omega), sTree127_eq f (by omega)]

def sTree129 : Tree := .node sTree123 sTree124

theorem sTree129_eq (f : Nat) (hf : 16 ≤ f) :
    toTree p215 f 129 = sTree129 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 123) (toTree p215 f 124) = Tree.node sTree123 sTree124
    simp only [sTree123_eq f (by omega), sTree124_eq f (by omega)]

def sTree130 : Tree := .node sTree87 sTree129

theorem sTree130_eq (f : Nat) (hf : 17 ≤ f) :
    toTree p215 f 130 = sTree130 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 87) (toTree p215 f 129) = Tree.node sTree87 sTree129
    simp only [sTree87_eq f (by omega), sTree129_eq f (by omega)]

def sTree131 : Tree := .node sTree87 sTree130

theorem sTree131_eq (f : Nat) (hf : 18 ≤ f) :
    toTree p215 f 131 = sTree131 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 87) (toTree p215 f 130) = Tree.node sTree87 sTree130
    simp only [sTree87_eq f (by omega), sTree130_eq f (by omega)]

def sTree132 : Tree := .node sTree128 sTree131

theorem sTree132_eq (f : Nat) (hf : 23 ≤ f) :
    toTree p215 f 132 = sTree132 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 128) (toTree p215 f 131) = Tree.node sTree128 sTree131
    simp only [sTree128_eq f (by omega), sTree131_eq f (by omega)]

def sTree133 : Tree := .node sTree99 sTree132

theorem sTree133_eq (f : Nat) (hf : 24 ≤ f) :
    toTree p215 f 133 = sTree133 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 99) (toTree p215 f 132) = Tree.node sTree99 sTree132
    simp only [sTree99_eq f (by omega), sTree132_eq f (by omega)]

def sTree134 : Tree := .node sTree98 sTree133

theorem sTree134_eq (f : Nat) (hf : 25 ≤ f) :
    toTree p215 f 134 = sTree134 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 98) (toTree p215 f 133) = Tree.node sTree98 sTree133
    simp only [sTree98_eq f (by omega), sTree133_eq f (by omega)]

def sTree135 : Tree := .node sTree95 sTree134

theorem sTree135_eq (f : Nat) (hf : 26 ≤ f) :
    toTree p215 f 135 = sTree135 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 95) (toTree p215 f 134) = Tree.node sTree95 sTree134
    simp only [sTree95_eq f (by omega), sTree134_eq f (by omega)]

def sTree136 : Tree := .node sTree135 sTree89

theorem sTree136_eq (f : Nat) (hf : 27 ≤ f) :
    toTree p215 f 136 = sTree136 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 135) (toTree p215 f 89) = Tree.node sTree135 sTree89
    simp only [sTree135_eq f (by omega), sTree89_eq f (by omega)]

def sTree137 : Tree := .node sTree55 sTree88

theorem sTree137_eq (f : Nat) (hf : 12 ≤ f) :
    toTree p215 f 137 = sTree137 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 55) (toTree p215 f 88) = Tree.node sTree55 sTree88
    simp only [sTree55_eq f (by omega), sTree88_eq f (by omega)]

def sTree138 : Tree := .node (.leaf (.decnz 3)) sTree24

theorem sTree138_eq (f : Nat) (hf : 3 ≤ f) :
    toTree p215 f 138 = sTree138 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 3)) (toTree p215 f 24) = Tree.node (.leaf (.decnz 3)) sTree24
    simp only [sTree24_eq f (by omega)]

def sTree139 : Tree := .node sTree137 sTree138

theorem sTree139_eq (f : Nat) (hf : 13 ≤ f) :
    toTree p215 f 139 = sTree139 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 137) (toTree p215 f 138) = Tree.node sTree137 sTree138
    simp only [sTree137_eq f (by omega), sTree138_eq f (by omega)]

def sTree140 : Tree := .node sTree87 sTree139

theorem sTree140_eq (f : Nat) (hf : 14 ≤ f) :
    toTree p215 f 140 = sTree140 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 87) (toTree p215 f 139) = Tree.node sTree87 sTree139
    simp only [sTree87_eq f (by omega), sTree139_eq f (by omega)]

def sTree141 : Tree := .node sTree136 sTree140

theorem sTree141_eq (f : Nat) (hf : 28 ≤ f) :
    toTree p215 f 141 = sTree141 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 136) (toTree p215 f 140) = Tree.node sTree136 sTree140
    simp only [sTree136_eq f (by omega), sTree140_eq f (by omega)]

def sTree142 : Tree := .node sTree79 sTree141

theorem sTree142_eq (f : Nat) (hf : 29 ≤ f) :
    toTree p215 f 142 = sTree142 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 79) (toTree p215 f 141) = Tree.node sTree79 sTree141
    simp only [sTree79_eq f (by omega), sTree141_eq f (by omega)]

def sTree143 : Tree := .node sTree72 sTree142

theorem sTree143_eq (f : Nat) (hf : 30 ≤ f) :
    toTree p215 f 143 = sTree143 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 72) (toTree p215 f 142) = Tree.node sTree72 sTree142
    simp only [sTree72_eq f (by omega), sTree142_eq f (by omega)]

def sTree144 : Tree := .node sTree4 (.leaf (.brk 1))

theorem sTree144_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 144 = sTree144 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 4) (.leaf (.brk 1)) = Tree.node sTree4 (.leaf (.brk 1))
    simp only [sTree4_eq f (by omega)]

def sTree145 : Tree := .node (.leaf (.decnz 5)) sTree144

theorem sTree145_eq (f : Nat) (hf : 3 ≤ f) :
    toTree p215 f 145 = sTree145 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 5)) (toTree p215 f 144) = Tree.node (.leaf (.decnz 5)) sTree144
    simp only [sTree144_eq f (by omega)]

def sTree146 : Tree := .node sTree145 (.leaf (.decnz 6))

theorem sTree146_eq (f : Nat) (hf : 4 ≤ f) :
    toTree p215 f 146 = sTree146 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 145) (.leaf (.decnz 6)) = Tree.node sTree145 (.leaf (.decnz 6))
    simp only [sTree145_eq f (by omega)]

def sTree147 : Tree := .node (.leaf (.decnz 5)) (.leaf (.cont 1))

theorem sTree147_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 147 = sTree147 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 5)) (.leaf (.cont 1)) = Tree.node (.leaf (.decnz 5)) (.leaf (.cont 1))
    rfl

def sTree148 : Tree := .node sTree147 sTree144

theorem sTree148_eq (f : Nat) (hf : 3 ≤ f) :
    toTree p215 f 148 = sTree148 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 147) (toTree p215 f 144) = Tree.node sTree147 sTree144
    simp only [sTree147_eq f (by omega), sTree144_eq f (by omega)]

def sTree149 : Tree := .node sTree146 sTree148

theorem sTree149_eq (f : Nat) (hf : 5 ≤ f) :
    toTree p215 f 149 = sTree149 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 146) (toTree p215 f 148) = Tree.node sTree146 sTree148
    simp only [sTree146_eq f (by omega), sTree148_eq f (by omega)]

def sTree150 : Tree := .node (.leaf (.decnz 1)) (.leaf (.cont 1))

theorem sTree150_eq (f : Nat) (hf : 1 ≤ f) :
    toTree p215 f 150 = sTree150 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 1)) (.leaf (.cont 1)) = Tree.node (.leaf (.decnz 1)) (.leaf (.cont 1))
    rfl

def sTree151 : Tree := .node sTree149 sTree150

theorem sTree151_eq (f : Nat) (hf : 6 ≤ f) :
    toTree p215 f 151 = sTree151 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 149) (toTree p215 f 150) = Tree.node sTree149 sTree150
    simp only [sTree149_eq f (by omega), sTree150_eq f (by omega)]

def sTree152 : Tree := .node sTree143 sTree151

theorem sTree152_eq (f : Nat) (hf : 31 ≤ f) :
    toTree p215 f 152 = sTree152 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 143) (toTree p215 f 151) = Tree.node sTree143 sTree151
    simp only [sTree143_eq f (by omega), sTree151_eq f (by omega)]

def sTree153 : Tree := .node sTree71 sTree152

theorem sTree153_eq (f : Nat) (hf : 32 ≤ f) :
    toTree p215 f 153 = sTree153 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 71) (toTree p215 f 152) = Tree.node sTree71 sTree152
    simp only [sTree71_eq f (by omega), sTree152_eq f (by omega)]

def sTree154 : Tree := .node (.leaf (.decnz 4)) sTree43

theorem sTree154_eq (f : Nat) (hf : 2 ≤ f) :
    toTree p215 f 154 = sTree154 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 4)) (toTree p215 f 43) = Tree.node (.leaf (.decnz 4)) sTree43
    simp only [sTree43_eq f (by omega)]

def sTree155 : Tree := .node sTree10 sTree154

theorem sTree155_eq (f : Nat) (hf : 3 ≤ f) :
    toTree p215 f 155 = sTree155 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 10) (toTree p215 f 154) = Tree.node sTree10 sTree154
    simp only [sTree10_eq f (by omega), sTree154_eq f (by omega)]

def sTree156 : Tree := .node sTree153 sTree155

theorem sTree156_eq (f : Nat) (hf : 33 ≤ f) :
    toTree p215 f 156 = sTree156 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 153) (toTree p215 f 155) = Tree.node sTree153 sTree155
    simp only [sTree153_eq f (by omega), sTree155_eq f (by omega)]

def sTree157 : Tree := .node sTree69 sTree156

theorem sTree157_eq (f : Nat) (hf : 34 ≤ f) :
    toTree p215 f 157 = sTree157 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 69) (toTree p215 f 156) = Tree.node sTree69 sTree156
    simp only [sTree69_eq f (by omega), sTree156_eq f (by omega)]

def sTree158 : Tree := .node sTree151 (.leaf (.brk 1))

theorem sTree158_eq (f : Nat) (hf : 7 ≤ f) :
    toTree p215 f 158 = sTree158 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 151) (.leaf (.brk 1)) = Tree.node sTree151 (.leaf (.brk 1))
    simp only [sTree151_eq f (by omega)]

def sTree159 : Tree := .node sTree157 sTree158

theorem sTree159_eq (f : Nat) (hf : 35 ≤ f) :
    toTree p215 f 159 = sTree159 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 157) (toTree p215 f 158) = Tree.node sTree157 sTree158
    simp only [sTree157_eq f (by omega), sTree158_eq f (by omega)]

def sTree160 : Tree := .node sTree61 sTree159

theorem sTree160_eq (f : Nat) (hf : 36 ≤ f) :
    toTree p215 f 160 = sTree160 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 61) (toTree p215 f 159) = Tree.node sTree61 sTree159
    simp only [sTree61_eq f (by omega), sTree159_eq f (by omega)]

def sTree161 : Tree := .node sTree57 sTree160

theorem sTree161_eq (f : Nat) (hf : 37 ≤ f) :
    toTree p215 f 161 = sTree161 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 57) (toTree p215 f 160) = Tree.node sTree57 sTree160
    simp only [sTree57_eq f (by omega), sTree160_eq f (by omega)]

def sTree162 : Tree := .node (.leaf (.decnz 3)) sTree161

theorem sTree162_eq (f : Nat) (hf : 38 ≤ f) :
    toTree p215 f 162 = sTree162 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 3)) (toTree p215 f 161) = Tree.node (.leaf (.decnz 3)) sTree161
    simp only [sTree161_eq f (by omega)]

def sTree163 : Tree := .node sTree65 sTree21

theorem sTree163_eq (f : Nat) (hf : 14 ≤ f) :
    toTree p215 f 163 = sTree163 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 65) (toTree p215 f 21) = Tree.node sTree65 sTree21
    simp only [sTree65_eq f (by omega), sTree21_eq f (by omega)]

def sTree164 : Tree := .node sTree149 sTree41

theorem sTree164_eq (f : Nat) (hf : 11 ≤ f) :
    toTree p215 f 164 = sTree164 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 149) (toTree p215 f 41) = Tree.node sTree149 sTree41
    simp only [sTree149_eq f (by omega), sTree41_eq f (by omega)]

def sTree165 : Tree := .node sTree163 sTree164

theorem sTree165_eq (f : Nat) (hf : 15 ≤ f) :
    toTree p215 f 165 = sTree165 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 163) (toTree p215 f 164) = Tree.node sTree163 sTree164
    simp only [sTree163_eq f (by omega), sTree164_eq f (by omega)]

def sTree166 : Tree := .node sTree162 sTree165

theorem sTree166_eq (f : Nat) (hf : 39 ≤ f) :
    toTree p215 f 166 = sTree166 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 162) (toTree p215 f 165) = Tree.node sTree162 sTree165
    simp only [sTree162_eq f (by omega), sTree165_eq f (by omega)]

def sTree167 : Tree := .node sTree166 (.leaf (.brk 1))

theorem sTree167_eq (f : Nat) (hf : 40 ≤ f) :
    toTree p215 f 167 = sTree167 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 166) (.leaf (.brk 1)) = Tree.node sTree166 (.leaf (.brk 1))
    simp only [sTree166_eq f (by omega)]

def sTree168 : Tree := .node (.leaf (.decnz 3)) sTree167

theorem sTree168_eq (f : Nat) (hf : 41 ≤ f) :
    toTree p215 f 168 = sTree168 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 3)) (toTree p215 f 167) = Tree.node (.leaf (.decnz 3)) sTree167
    simp only [sTree167_eq f (by omega)]

def sTree169 : Tree := .node sTree168 sTree46

theorem sTree169_eq (f : Nat) (hf : 42 ≤ f) :
    toTree p215 f 169 = sTree169 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 168) (toTree p215 f 46) = Tree.node sTree168 sTree46
    simp only [sTree168_eq f (by omega), sTree46_eq f (by omega)]

def sTree170 : Tree := .node sTree169 (.leaf (.brk 1))

theorem sTree170_eq (f : Nat) (hf : 43 ≤ f) :
    toTree p215 f 170 = sTree170 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 169) (.leaf (.brk 1)) = Tree.node sTree169 (.leaf (.brk 1))
    simp only [sTree169_eq f (by omega)]

def sTree171 : Tree := .node (.leaf (.decnz 3)) sTree170

theorem sTree171_eq (f : Nat) (hf : 44 ≤ f) :
    toTree p215 f 171 = sTree171 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 3)) (toTree p215 f 170) = Tree.node (.leaf (.decnz 3)) sTree170
    simp only [sTree170_eq f (by omega)]

def sTree172 : Tree := .node sTree149 (.leaf (.halt))

theorem sTree172_eq (f : Nat) (hf : 6 ≤ f) :
    toTree p215 f 172 = sTree172 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 149) (.leaf (.halt)) = Tree.node sTree149 (.leaf (.halt))
    simp only [sTree149_eq f (by omega)]

def sTree173 : Tree := .node sTree49 sTree44

theorem sTree173_eq (f : Nat) (hf : 8 ≤ f) :
    toTree p215 f 173 = sTree173 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 49) (toTree p215 f 44) = Tree.node sTree49 sTree44
    simp only [sTree49_eq f (by omega), sTree44_eq f (by omega)]

def sTree174 : Tree := .node sTree172 sTree173

theorem sTree174_eq (f : Nat) (hf : 9 ≤ f) :
    toTree p215 f 174 = sTree174 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 172) (toTree p215 f 173) = Tree.node sTree172 sTree173
    simp only [sTree172_eq f (by omega), sTree173_eq f (by omega)]

def sTree175 : Tree := .node (.leaf (.inc 6)) sTree174

theorem sTree175_eq (f : Nat) (hf : 10 ≤ f) :
    toTree p215 f 175 = sTree175 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 6)) (toTree p215 f 174) = Tree.node (.leaf (.inc 6)) sTree174
    simp only [sTree174_eq f (by omega)]

def sTree176 : Tree := .node sTree171 sTree175

theorem sTree176_eq (f : Nat) (hf : 45 ≤ f) :
    toTree p215 f 176 = sTree176 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 171) (toTree p215 f 175) = Tree.node sTree171 sTree175
    simp only [sTree171_eq f (by omega), sTree175_eq f (by omega)]

def sTree177 : Tree := .node sTree20 sTree176

theorem sTree177_eq (f : Nat) (hf : 46 ≤ f) :
    toTree p215 f 177 = sTree177 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 20) (toTree p215 f 176) = Tree.node sTree20 sTree176
    simp only [sTree20_eq f (by omega), sTree176_eq f (by omega)]

def sTree178 : Tree := .node sTree7 sTree177

theorem sTree178_eq (f : Nat) (hf : 47 ≤ f) :
    toTree p215 f 178 = sTree178 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree p215 f 7) (toTree p215 f 177) = Tree.node sTree7 sTree177
    simp only [sTree7_eq f (by omega), sTree177_eq f (by omega)]

def dTree134 : Tree := .node (.leaf (.decnz 8)) (.leaf (.brk 1))

theorem dTree134_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 134 = dTree134 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 8)) (.leaf (.brk 1)) = Tree.node (.leaf (.decnz 8)) (.leaf (.brk 1))
    rfl

def dTree196 : Tree := .node (.leaf (.inc 8)) (.leaf (.inc 6))

theorem dTree196_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 196 = dTree196 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 8)) (.leaf (.inc 6)) = Tree.node (.leaf (.inc 8)) (.leaf (.inc 6))
    rfl

def dTree195 : Tree := .node dTree196 (.leaf (.cont 2))

theorem dTree195_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 195 = dTree195 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 196) (.leaf (.cont 2)) = Tree.node dTree196 (.leaf (.cont 2))
    simp only [dTree196_eq f (by omega)]

def dTree194 : Tree := .node (.leaf (.decnz 0)) dTree195

theorem dTree194_eq (f : Nat) (hf : 3 ≤ f) :
    toTree pathDagPerm f 194 = dTree194 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 0)) (toTree pathDagPerm f 195) = Tree.node (.leaf (.decnz 0)) dTree195
    simp only [dTree195_eq f (by omega)]

def dTree300 : Tree := .node (.leaf (.decnz 6)) (.leaf (.cont 2))

theorem dTree300_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 300 = dTree300 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (.leaf (.cont 2)) = Tree.node (.leaf (.decnz 6)) (.leaf (.cont 2))
    rfl

def dTree136 : Tree := .node (.leaf (.inc 0)) dTree300

theorem dTree136_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 136 = dTree136 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 0)) (toTree pathDagPerm f 300) = Tree.node (.leaf (.inc 0)) dTree300
    simp only [dTree300_eq f (by omega)]

def dTree135 : Tree := .node dTree194 dTree136

theorem dTree135_eq (f : Nat) (hf : 4 ≤ f) :
    toTree pathDagPerm f 135 = dTree135 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 194) (toTree pathDagPerm f 136) = Tree.node dTree194 dTree136
    simp only [dTree194_eq f (by omega), dTree136_eq f (by omega)]

def dTree133 : Tree := .node dTree134 dTree135

theorem dTree133_eq (f : Nat) (hf : 5 ≤ f) :
    toTree pathDagPerm f 133 = dTree133 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 134) (toTree pathDagPerm f 135) = Tree.node dTree134 dTree135
    simp only [dTree134_eq f (by omega), dTree135_eq f (by omega)]

def dTree138 : Tree := .node (.leaf (.decnz 6)) (.leaf (.brk 1))

theorem dTree138_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 138 = dTree138 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (.leaf (.brk 1)) = Tree.node (.leaf (.decnz 6)) (.leaf (.brk 1))
    rfl

def dTree185 : Tree := .node (.leaf (.inc 6)) (.leaf (.cont 2))

theorem dTree185_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 185 = dTree185 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 6)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 6)) (.leaf (.cont 2))
    rfl

def dTree211 : Tree := .node (.leaf (.decnz 7)) dTree185

theorem dTree211_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 211 = dTree211 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 7)) (toTree pathDagPerm f 185) = Tree.node (.leaf (.decnz 7)) dTree185
    simp only [dTree185_eq f (by omega)]

def dTree137 : Tree := .node dTree138 dTree211

theorem dTree137_eq (f : Nat) (hf : 3 ≤ f) :
    toTree pathDagPerm f 137 = dTree137 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 138) (toTree pathDagPerm f 211) = Tree.node dTree138 dTree211
    simp only [dTree138_eq f (by omega), dTree211_eq f (by omega)]

def dTree155 : Tree := .node (.leaf (.inc 7)) dTree137

theorem dTree155_eq (f : Nat) (hf : 4 ≤ f) :
    toTree pathDagPerm f 155 = dTree155 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 7)) (toTree pathDagPerm f 137) = Tree.node (.leaf (.inc 7)) dTree137
    simp only [dTree137_eq f (by omega)]

def dTree154 : Tree := .node dTree155 (.leaf (.cont 2))

theorem dTree154_eq (f : Nat) (hf : 5 ≤ f) :
    toTree pathDagPerm f 154 = dTree154 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 155) (.leaf (.cont 2)) = Tree.node dTree155 (.leaf (.cont 2))
    simp only [dTree155_eq f (by omega)]

def dTree115 : Tree := .node (.leaf (.decnz 8)) dTree154

theorem dTree115_eq (f : Nat) (hf : 6 ≤ f) :
    toTree pathDagPerm f 115 = dTree115 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 8)) (toTree pathDagPerm f 154) = Tree.node (.leaf (.decnz 8)) dTree154
    simp only [dTree154_eq f (by omega)]

def dTree210 : Tree := .node (.leaf (.inc 8)) (.leaf (.cont 2))

theorem dTree210_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 210 = dTree210 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 8)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 8)) (.leaf (.cont 2))
    rfl

def dTree209 : Tree := .node (.leaf (.decnz 7)) dTree210

theorem dTree209_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 209 = dTree209 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 7)) (toTree pathDagPerm f 210) = Tree.node (.leaf (.decnz 7)) dTree210
    simp only [dTree210_eq f (by omega)]

def dTree158 : Tree := .node dTree115 dTree209

theorem dTree158_eq (f : Nat) (hf : 7 ≤ f) :
    toTree pathDagPerm f 158 = dTree158 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 115) (toTree pathDagPerm f 209) = Tree.node dTree115 dTree209
    simp only [dTree115_eq f (by omega), dTree209_eq f (by omega)]

def dTree202 : Tree := .node (.leaf (.inc 3)) (.leaf (.cont 2))

theorem dTree202_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 202 = dTree202 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 3)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 3)) (.leaf (.cont 2))
    rfl

def dTree201 : Tree := .node (.leaf (.decnz 6)) dTree202

theorem dTree201_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 201 = dTree201 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (toTree pathDagPerm f 202) = Tree.node (.leaf (.decnz 6)) dTree202
    simp only [dTree202_eq f (by omega)]

def dTree174 : Tree := .node dTree158 dTree201

theorem dTree174_eq (f : Nat) (hf : 8 ≤ f) :
    toTree pathDagPerm f 174 = dTree174 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 158) (toTree pathDagPerm f 201) = Tree.node dTree158 dTree201
    simp only [dTree158_eq f (by omega), dTree201_eq f (by omega)]

def dTree216 : Tree := .node (.leaf (.decnz 1)) dTree185

theorem dTree216_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 216 = dTree216 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 1)) (toTree pathDagPerm f 185) = Tree.node (.leaf (.decnz 1)) dTree185
    simp only [dTree185_eq f (by omega)]

def dTree186 : Tree := .node (.leaf (.inc 1)) (.leaf (.cont 2))

theorem dTree186_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 186 = dTree186 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 1)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 1)) (.leaf (.cont 2))
    rfl

def dTree217 : Tree := .node (.leaf (.decnz 2)) dTree186

theorem dTree217_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 217 = dTree217 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 2)) (toTree pathDagPerm f 186) = Tree.node (.leaf (.decnz 2)) dTree186
    simp only [dTree186_eq f (by omega)]

def dTree188 : Tree := .node (.leaf (.inc 6)) (.leaf (.inc 7))

theorem dTree188_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 188 = dTree188 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 6)) (.leaf (.inc 7)) = Tree.node (.leaf (.inc 6)) (.leaf (.inc 7))
    rfl

def dTree187 : Tree := .node dTree188 (.leaf (.cont 2))

theorem dTree187_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 187 = dTree187 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 188) (.leaf (.cont 2)) = Tree.node dTree188 (.leaf (.cont 2))
    simp only [dTree188_eq f (by omega)]

def dTree215 : Tree := .node (.leaf (.decnz 1)) dTree187

theorem dTree215_eq (f : Nat) (hf : 3 ≤ f) :
    toTree pathDagPerm f 215 = dTree215 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 1)) (toTree pathDagPerm f 187) = Tree.node (.leaf (.decnz 1)) dTree187
    simp only [dTree187_eq f (by omega)]

def dTree208 : Tree := .node (.leaf (.decnz 6)) dTree186

theorem dTree208_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 208 = dTree208 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (toTree pathDagPerm f 186) = Tree.node (.leaf (.decnz 6)) dTree186
    simp only [dTree186_eq f (by omega)]

def dTree165 : Tree := .node (.leaf (.inc 7)) dTree208

theorem dTree165_eq (f : Nat) (hf : 3 ≤ f) :
    toTree pathDagPerm f 165 = dTree165 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 7)) (toTree pathDagPerm f 208) = Tree.node (.leaf (.inc 7)) dTree208
    simp only [dTree208_eq f (by omega)]

def dTree164 : Tree := .node dTree165 (.leaf (.cont 3))

theorem dTree164_eq (f : Nat) (hf : 4 ≤ f) :
    toTree pathDagPerm f 164 = dTree164 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 165) (.leaf (.cont 3)) = Tree.node dTree165 (.leaf (.cont 3))
    simp only [dTree165_eq f (by omega)]

def dTree163 : Tree := .node (.leaf (.decnz 6)) dTree164

theorem dTree163_eq (f : Nat) (hf : 5 ≤ f) :
    toTree pathDagPerm f 163 = dTree163 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (toTree pathDagPerm f 164) = Tree.node (.leaf (.decnz 6)) dTree164
    simp only [dTree164_eq f (by omega)]

def dTree162 : Tree := .node dTree215 dTree163

theorem dTree162_eq (f : Nat) (hf : 6 ≤ f) :
    toTree pathDagPerm f 162 = dTree162 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 215) (toTree pathDagPerm f 163) = Tree.node dTree215 dTree163
    simp only [dTree215_eq f (by omega), dTree163_eq f (by omega)]

def dTree213 : Tree := .node (.leaf (.inc 2)) (.leaf (.cont 2))

theorem dTree213_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 213 = dTree213 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 2)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 2)) (.leaf (.cont 2))
    rfl

def dTree212 : Tree := .node (.leaf (.decnz 7)) dTree213

theorem dTree212_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 212 = dTree212 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 7)) (toTree pathDagPerm f 213) = Tree.node (.leaf (.decnz 7)) dTree213
    simp only [dTree213_eq f (by omega)]

def dTree173 : Tree := .node dTree162 dTree212

theorem dTree173_eq (f : Nat) (hf : 7 ≤ f) :
    toTree pathDagPerm f 173 = dTree173 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 162) (toTree pathDagPerm f 212) = Tree.node dTree162 dTree212
    simp only [dTree162_eq f (by omega), dTree212_eq f (by omega)]

def dTree172 : Tree := .node dTree217 dTree173

theorem dTree172_eq (f : Nat) (hf : 8 ≤ f) :
    toTree pathDagPerm f 172 = dTree172 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 217) (toTree pathDagPerm f 173) = Tree.node dTree217 dTree173
    simp only [dTree217_eq f (by omega), dTree173_eq f (by omega)]

def dTree171 : Tree := .node dTree216 dTree172

theorem dTree171_eq (f : Nat) (hf : 9 ≤ f) :
    toTree pathDagPerm f 171 = dTree171 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 216) (toTree pathDagPerm f 172) = Tree.node dTree216 dTree172
    simp only [dTree216_eq f (by omega), dTree172_eq f (by omega)]

def dTree190 : Tree := .node (.leaf (.inc 6)) (.leaf (.inc 1))

theorem dTree190_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 190 = dTree190 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 6)) (.leaf (.inc 1)) = Tree.node (.leaf (.inc 6)) (.leaf (.inc 1))
    rfl

def dTree189 : Tree := .node dTree190 (.leaf (.cont 2))

theorem dTree189_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 189 = dTree189 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 190) (.leaf (.cont 2)) = Tree.node dTree190 (.leaf (.cont 2))
    simp only [dTree190_eq f (by omega)]

def dTree198 : Tree := .node (.leaf (.decnz 4)) dTree189

theorem dTree198_eq (f : Nat) (hf : 3 ≤ f) :
    toTree pathDagPerm f 198 = dTree198 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 4)) (toTree pathDagPerm f 189) = Tree.node (.leaf (.decnz 4)) dTree189
    simp only [dTree189_eq f (by omega)]

def dTree206 : Tree := .node (.leaf (.inc 4)) (.leaf (.cont 2))

theorem dTree206_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 206 = dTree206 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 4)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 4)) (.leaf (.cont 2))
    rfl

def dTree205 : Tree := .node (.leaf (.decnz 6)) dTree206

theorem dTree205_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 205 = dTree205 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (toTree pathDagPerm f 206) = Tree.node (.leaf (.decnz 6)) dTree206
    simp only [dTree206_eq f (by omega)]

def dTree167 : Tree := .node dTree198 dTree205

theorem dTree167_eq (f : Nat) (hf : 4 ≤ f) :
    toTree pathDagPerm f 167 = dTree167 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 198) (toTree pathDagPerm f 205) = Tree.node dTree198 dTree205
    simp only [dTree198_eq f (by omega), dTree205_eq f (by omega)]

def dTree166 : Tree := .node dTree171 dTree167

theorem dTree166_eq (f : Nat) (hf : 10 ≤ f) :
    toTree pathDagPerm f 166 = dTree166 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 171) (toTree pathDagPerm f 167) = Tree.node dTree171 dTree167
    simp only [dTree171_eq f (by omega), dTree167_eq f (by omega)]

def dTree200 : Tree := .node (.leaf (.decnz 5)) dTree189

theorem dTree200_eq (f : Nat) (hf : 3 ≤ f) :
    toTree pathDagPerm f 200 = dTree200 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 5)) (toTree pathDagPerm f 189) = Tree.node (.leaf (.decnz 5)) dTree189
    simp only [dTree189_eq f (by omega)]

def dTree191 : Tree := .node (.leaf (.inc 5)) (.leaf (.cont 2))

theorem dTree191_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 191 = dTree191 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 5)) (.leaf (.cont 2)) = Tree.node (.leaf (.inc 5)) (.leaf (.cont 2))
    rfl

def dTree207 : Tree := .node (.leaf (.decnz 6)) dTree191

theorem dTree207_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 207 = dTree207 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (toTree pathDagPerm f 191) = Tree.node (.leaf (.decnz 6)) dTree191
    simp only [dTree191_eq f (by omega)]

def dTree122 : Tree := .node dTree200 dTree207

theorem dTree122_eq (f : Nat) (hf : 4 ≤ f) :
    toTree pathDagPerm f 122 = dTree122 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 200) (toTree pathDagPerm f 207) = Tree.node dTree200 dTree207
    simp only [dTree200_eq f (by omega), dTree207_eq f (by omega)]

def dTree121 : Tree := .node dTree171 dTree122

theorem dTree121_eq (f : Nat) (hf : 10 ≤ f) :
    toTree pathDagPerm f 121 = dTree121 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 171) (toTree pathDagPerm f 122) = Tree.node dTree171 dTree122
    simp only [dTree171_eq f (by omega), dTree122_eq f (by omega)]

def dTree116 : Tree := .node (.leaf (.decnz 2)) dTree154

theorem dTree116_eq (f : Nat) (hf : 6 ≤ f) :
    toTree pathDagPerm f 116 = dTree116 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 2)) (toTree pathDagPerm f 154) = Tree.node (.leaf (.decnz 2)) dTree154
    simp only [dTree154_eq f (by omega)]

def dTree160 : Tree := .node dTree116 dTree212

theorem dTree160_eq (f : Nat) (hf : 7 ≤ f) :
    toTree pathDagPerm f 160 = dTree160 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 116) (toTree pathDagPerm f 212) = Tree.node dTree116 dTree212
    simp only [dTree116_eq f (by omega), dTree212_eq f (by omega)]

def dTree159 : Tree := .node (.leaf (.inc 1)) (.leaf (.inc 1))

theorem dTree159_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 159 = dTree159 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 1)) (.leaf (.inc 1)) = Tree.node (.leaf (.inc 1)) (.leaf (.inc 1))
    rfl

def dTree157 : Tree := .node dTree159 (.leaf (.inc 1))

theorem dTree157_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 157 = dTree157 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 159) (.leaf (.inc 1)) = Tree.node dTree159 (.leaf (.inc 1))
    simp only [dTree159_eq f (by omega)]

def dTree156 : Tree := .node dTree157 (.leaf (.inc 1))

theorem dTree156_eq (f : Nat) (hf : 3 ≤ f) :
    toTree pathDagPerm f 156 = dTree156 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 157) (.leaf (.inc 1)) = Tree.node dTree157 (.leaf (.inc 1))
    simp only [dTree157_eq f (by omega)]

def dTree118 : Tree := .node dTree156 (.leaf (.cont 2))

theorem dTree118_eq (f : Nat) (hf : 4 ≤ f) :
    toTree pathDagPerm f 118 = dTree118 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 156) (.leaf (.cont 2)) = Tree.node dTree156 (.leaf (.cont 2))
    simp only [dTree156_eq f (by omega)]

def dTree117 : Tree := .node (.leaf (.decnz 7)) dTree118

theorem dTree117_eq (f : Nat) (hf : 5 ≤ f) :
    toTree pathDagPerm f 117 = dTree117 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 7)) (toTree pathDagPerm f 118) = Tree.node (.leaf (.decnz 7)) dTree118
    simp only [dTree118_eq f (by omega)]

def dTree120 : Tree := .node dTree162 dTree117

theorem dTree120_eq (f : Nat) (hf : 7 ≤ f) :
    toTree pathDagPerm f 120 = dTree120 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 162) (toTree pathDagPerm f 117) = Tree.node dTree162 dTree117
    simp only [dTree162_eq f (by omega), dTree117_eq f (by omega)]

def dTree119 : Tree := .node dTree160 dTree120

theorem dTree119_eq (f : Nat) (hf : 8 ≤ f) :
    toTree pathDagPerm f 119 = dTree119 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 160) (toTree pathDagPerm f 120) = Tree.node dTree160 dTree120
    simp only [dTree160_eq f (by omega), dTree120_eq f (by omega)]

def dTree180 : Tree := .node dTree119 dTree159

theorem dTree180_eq (f : Nat) (hf : 9 ≤ f) :
    toTree pathDagPerm f 180 = dTree180 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 159) = Tree.node dTree119 dTree159
    simp only [dTree119_eq f (by omega), dTree159_eq f (by omega)]

def dTree193 : Tree := .node (.leaf (.decnz 3)) dTree189

theorem dTree193_eq (f : Nat) (hf : 3 ≤ f) :
    toTree pathDagPerm f 193 = dTree193 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 3)) (toTree pathDagPerm f 189) = Tree.node (.leaf (.decnz 3)) dTree189
    simp only [dTree189_eq f (by omega)]

def dTree169 : Tree := .node dTree193 dTree201

theorem dTree169_eq (f : Nat) (hf : 4 ≤ f) :
    toTree pathDagPerm f 169 = dTree169 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 193) (toTree pathDagPerm f 201) = Tree.node dTree193 dTree201
    simp only [dTree193_eq f (by omega), dTree201_eq f (by omega)]

def dTree168 : Tree := .node dTree171 dTree169

theorem dTree168_eq (f : Nat) (hf : 10 ≤ f) :
    toTree pathDagPerm f 168 = dTree168 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 171) (toTree pathDagPerm f 169) = Tree.node dTree171 dTree169
    simp only [dTree171_eq f (by omega), dTree169_eq f (by omega)]

def dTree176 : Tree := .node dTree158 dTree207

theorem dTree176_eq (f : Nat) (hf : 8 ≤ f) :
    toTree pathDagPerm f 176 = dTree176 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 158) (toTree pathDagPerm f 207) = Tree.node dTree158 dTree207
    simp only [dTree158_eq f (by omega), dTree207_eq f (by omega)]

def dTree175 : Tree := .node dTree158 dTree205

theorem dTree175_eq (f : Nat) (hf : 8 ≤ f) :
    toTree pathDagPerm f 175 = dTree175 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 158) (toTree pathDagPerm f 205) = Tree.node dTree158 dTree205
    simp only [dTree158_eq f (by omega), dTree205_eq f (by omega)]

def dTree182 : Tree := .node dTree119 dTree157

theorem dTree182_eq (f : Nat) (hf : 9 ≤ f) :
    toTree pathDagPerm f 182 = dTree182 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 157) = Tree.node dTree119 dTree157
    simp only [dTree119_eq f (by omega), dTree157_eq f (by omega)]

def dTree181 : Tree := .node dTree119 (.leaf (.inc 1))

theorem dTree181_eq (f : Nat) (hf : 9 ≤ f) :
    toTree pathDagPerm f 181 = dTree181 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (.leaf (.inc 1)) = Tree.node dTree119 (.leaf (.inc 1))
    simp only [dTree119_eq f (by omega)]

def dTree177 : Tree := .node dTree171 (.leaf (.inc 1))

theorem dTree177_eq (f : Nat) (hf : 10 ≤ f) :
    toTree pathDagPerm f 177 = dTree177 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 171) (.leaf (.inc 1)) = Tree.node dTree171 (.leaf (.inc 1))
    simp only [dTree171_eq f (by omega)]

def dTree218 : Tree := .node dTree177 dTree119

theorem dTree218_eq (f : Nat) (hf : 11 ≤ f) :
    toTree pathDagPerm f 218 = dTree218 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 177) (toTree pathDagPerm f 119) = Tree.node dTree177 dTree119
    simp only [dTree177_eq f (by omega), dTree119_eq f (by omega)]

def dTree184 : Tree := .node dTree180 dTree218

theorem dTree184_eq (f : Nat) (hf : 12 ≤ f) :
    toTree pathDagPerm f 184 = dTree184 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 218) = Tree.node dTree180 dTree218
    simp only [dTree180_eq f (by omega), dTree218_eq f (by omega)]

def dTree183 : Tree := .node dTree218 dTree184

theorem dTree183_eq (f : Nat) (hf : 13 ≤ f) :
    toTree pathDagPerm f 183 = dTree183 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 218) (toTree pathDagPerm f 184) = Tree.node dTree218 dTree184
    simp only [dTree218_eq f (by omega), dTree184_eq f (by omega)]

def dTree192 : Tree := .node (.leaf (.decnz 3)) dTree187

theorem dTree192_eq (f : Nat) (hf : 3 ≤ f) :
    toTree pathDagPerm f 192 = dTree192 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 3)) (toTree pathDagPerm f 187) = Tree.node (.leaf (.decnz 3)) dTree187
    simp only [dTree187_eq f (by omega)]

def dTree461 : Tree := .node (.leaf (.decnz 6)) (.leaf (.cont 2))

theorem dTree461_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 461 = dTree461 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 6)) (.leaf (.cont 2)) = Tree.node (.leaf (.decnz 6)) (.leaf (.cont 2))
    rfl

def dTree462 : Tree := .node dTree461 (.leaf (.brk 1))

theorem dTree462_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 462 = dTree462 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 461) (.leaf (.brk 1)) = Tree.node dTree461 (.leaf (.brk 1))
    simp only [dTree461_eq f (by omega)]

def dTree463 : Tree := .node (.leaf (.decnz 5)) dTree462

theorem dTree463_eq (f : Nat) (hf : 3 ≤ f) :
    toTree pathDagPerm f 463 = dTree463 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 5)) (toTree pathDagPerm f 462) = Tree.node (.leaf (.decnz 5)) dTree462
    simp only [dTree462_eq f (by omega)]

def dTree464 : Tree := .node dTree463 (.leaf (.decnz 6))

theorem dTree464_eq (f : Nat) (hf : 4 ≤ f) :
    toTree pathDagPerm f 464 = dTree464 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 463) (.leaf (.decnz 6)) = Tree.node dTree463 (.leaf (.decnz 6))
    simp only [dTree463_eq f (by omega)]

def dTree465 : Tree := .node (.leaf (.decnz 5)) (.leaf (.cont 1))

theorem dTree465_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 465 = dTree465 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 5)) (.leaf (.cont 1)) = Tree.node (.leaf (.decnz 5)) (.leaf (.cont 1))
    rfl

def dTree466 : Tree := .node dTree465 dTree462

theorem dTree466_eq (f : Nat) (hf : 3 ≤ f) :
    toTree pathDagPerm f 466 = dTree466 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 465) (toTree pathDagPerm f 462) = Tree.node dTree465 dTree462
    simp only [dTree465_eq f (by omega), dTree462_eq f (by omega)]

def dTree123 : Tree := .node dTree464 dTree466

theorem dTree123_eq (f : Nat) (hf : 5 ≤ f) :
    toTree pathDagPerm f 123 = dTree123 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 464) (toTree pathDagPerm f 466) = Tree.node dTree464 dTree466
    simp only [dTree464_eq f (by omega), dTree466_eq f (by omega)]

def dTree214 : Tree := .node (.leaf (.decnz 1)) (.leaf (.cont 1))

theorem dTree214_eq (f : Nat) (hf : 1 ≤ f) :
    toTree pathDagPerm f 214 = dTree214 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 1)) (.leaf (.cont 1)) = Tree.node (.leaf (.decnz 1)) (.leaf (.cont 1))
    rfl

def dTree131 : Tree := .node dTree123 dTree214

theorem dTree131_eq (f : Nat) (hf : 6 ≤ f) :
    toTree pathDagPerm f 131 = dTree131 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 123) (toTree pathDagPerm f 214) = Tree.node dTree123 dTree214
    simp only [dTree123_eq f (by omega), dTree214_eq f (by omega)]

def dTree197 : Tree := .node (.leaf (.decnz 4)) dTree191

theorem dTree197_eq (f : Nat) (hf : 2 ≤ f) :
    toTree pathDagPerm f 197 = dTree197 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 4)) (toTree pathDagPerm f 191) = Tree.node (.leaf (.decnz 4)) dTree191
    simp only [dTree191_eq f (by omega)]

def dTree460 : Tree := .node dTree197 dTree131

theorem dTree460_eq (f : Nat) (hf : 7 ≤ f) :
    toTree pathDagPerm f 460 = dTree460 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 197) (toTree pathDagPerm f 131) = Tree.node dTree197 dTree131
    simp only [dTree197_eq f (by omega), dTree131_eq f (by omega)]

def dTree459 : Tree := .node dTree211 dTree460

theorem dTree459_eq (f : Nat) (hf : 8 ≤ f) :
    toTree pathDagPerm f 459 = dTree459 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 211) (toTree pathDagPerm f 460) = Tree.node dTree211 dTree460
    simp only [dTree211_eq f (by omega), dTree460_eq f (by omega)]

def dTree458 : Tree := .node dTree131 dTree459

theorem dTree458_eq (f : Nat) (hf : 9 ≤ f) :
    toTree pathDagPerm f 458 = dTree458 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 131) (toTree pathDagPerm f 459) = Tree.node dTree131 dTree459
    simp only [dTree131_eq f (by omega), dTree459_eq f (by omega)]

def dTree457 : Tree := .node dTree192 dTree458

theorem dTree457_eq (f : Nat) (hf : 10 ≤ f) :
    toTree pathDagPerm f 457 = dTree457 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 192) (toTree pathDagPerm f 458) = Tree.node dTree192 dTree458
    simp only [dTree192_eq f (by omega), dTree458_eq f (by omega)]

def dTree456 : Tree := .node dTree218 dTree457

theorem dTree456_eq (f : Nat) (hf : 12 ≤ f) :
    toTree pathDagPerm f 456 = dTree456 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 218) (toTree pathDagPerm f 457) = Tree.node dTree218 dTree457
    simp only [dTree218_eq f (by omega), dTree457_eq f (by omega)]

def dTree455 : Tree := .node dTree119 dTree456

theorem dTree455_eq (f : Nat) (hf : 13 ≤ f) :
    toTree pathDagPerm f 455 = dTree455 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 456) = Tree.node dTree119 dTree456
    simp only [dTree119_eq f (by omega), dTree456_eq f (by omega)]

def dTree454 : Tree := .node dTree180 dTree455

theorem dTree454_eq (f : Nat) (hf : 14 ≤ f) :
    toTree pathDagPerm f 454 = dTree454 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 455) = Tree.node dTree180 dTree455
    simp only [dTree180_eq f (by omega), dTree455_eq f (by omega)]

def dTree453 : Tree := .node dTree119 dTree454

theorem dTree453_eq (f : Nat) (hf : 15 ≤ f) :
    toTree pathDagPerm f 453 = dTree453 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 454) = Tree.node dTree119 dTree454
    simp only [dTree119_eq f (by omega), dTree454_eq f (by omega)]

def dTree452 : Tree := .node dTree218 dTree453

theorem dTree452_eq (f : Nat) (hf : 16 ≤ f) :
    toTree pathDagPerm f 452 = dTree452 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 218) (toTree pathDagPerm f 453) = Tree.node dTree218 dTree453
    simp only [dTree218_eq f (by omega), dTree453_eq f (by omega)]

def dTree451 : Tree := .node dTree180 dTree452

theorem dTree451_eq (f : Nat) (hf : 17 ≤ f) :
    toTree pathDagPerm f 451 = dTree451 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 452) = Tree.node dTree180 dTree452
    simp only [dTree180_eq f (by omega), dTree452_eq f (by omega)]

def dTree450 : Tree := .node dTree119 dTree451

theorem dTree450_eq (f : Nat) (hf : 18 ≤ f) :
    toTree pathDagPerm f 450 = dTree450 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 451) = Tree.node dTree119 dTree451
    simp only [dTree119_eq f (by omega), dTree451_eq f (by omega)]

def dTree449 : Tree := .node dTree218 dTree450

theorem dTree449_eq (f : Nat) (hf : 19 ≤ f) :
    toTree pathDagPerm f 449 = dTree449 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 218) (toTree pathDagPerm f 450) = Tree.node dTree218 dTree450
    simp only [dTree218_eq f (by omega), dTree450_eq f (by omega)]

def dTree448 : Tree := .node dTree180 dTree449

theorem dTree448_eq (f : Nat) (hf : 20 ≤ f) :
    toTree pathDagPerm f 448 = dTree448 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 449) = Tree.node dTree180 dTree449
    simp only [dTree180_eq f (by omega), dTree449_eq f (by omega)]

def dTree447 : Tree := .node dTree119 dTree448

theorem dTree447_eq (f : Nat) (hf : 21 ≤ f) :
    toTree pathDagPerm f 447 = dTree447 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 448) = Tree.node dTree119 dTree448
    simp only [dTree119_eq f (by omega), dTree448_eq f (by omega)]

def dTree446 : Tree := .node dTree218 dTree447

theorem dTree446_eq (f : Nat) (hf : 22 ≤ f) :
    toTree pathDagPerm f 446 = dTree446 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 218) (toTree pathDagPerm f 447) = Tree.node dTree218 dTree447
    simp only [dTree218_eq f (by omega), dTree447_eq f (by omega)]

def dTree445 : Tree := .node dTree181 dTree446

theorem dTree445_eq (f : Nat) (hf : 23 ≤ f) :
    toTree pathDagPerm f 445 = dTree445 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 181) (toTree pathDagPerm f 446) = Tree.node dTree181 dTree446
    simp only [dTree181_eq f (by omega), dTree446_eq f (by omega)]

def dTree444 : Tree := .node dTree168 dTree445

theorem dTree444_eq (f : Nat) (hf : 24 ≤ f) :
    toTree pathDagPerm f 444 = dTree444 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 445) = Tree.node dTree168 dTree445
    simp only [dTree168_eq f (by omega), dTree445_eq f (by omega)]

def dTree443 : Tree := .node dTree121 dTree444

theorem dTree443_eq (f : Nat) (hf : 25 ≤ f) :
    toTree pathDagPerm f 443 = dTree443 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 444) = Tree.node dTree121 dTree444
    simp only [dTree121_eq f (by omega), dTree444_eq f (by omega)]

def dTree442 : Tree := .node dTree168 dTree443

theorem dTree442_eq (f : Nat) (hf : 26 ≤ f) :
    toTree pathDagPerm f 442 = dTree442 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 443) = Tree.node dTree168 dTree443
    simp only [dTree168_eq f (by omega), dTree443_eq f (by omega)]

def dTree441 : Tree := .node dTree121 dTree442

theorem dTree441_eq (f : Nat) (hf : 27 ≤ f) :
    toTree pathDagPerm f 441 = dTree441 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 442) = Tree.node dTree121 dTree442
    simp only [dTree121_eq f (by omega), dTree442_eq f (by omega)]

def dTree440 : Tree := .node dTree168 dTree441

theorem dTree440_eq (f : Nat) (hf : 28 ≤ f) :
    toTree pathDagPerm f 440 = dTree440 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 441) = Tree.node dTree168 dTree441
    simp only [dTree168_eq f (by omega), dTree441_eq f (by omega)]

def dTree439 : Tree := .node dTree121 dTree440

theorem dTree439_eq (f : Nat) (hf : 29 ≤ f) :
    toTree pathDagPerm f 439 = dTree439 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 440) = Tree.node dTree121 dTree440
    simp only [dTree121_eq f (by omega), dTree440_eq f (by omega)]

def dTree438 : Tree := .node dTree180 dTree439

theorem dTree438_eq (f : Nat) (hf : 30 ≤ f) :
    toTree pathDagPerm f 438 = dTree438 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 439) = Tree.node dTree180 dTree439
    simp only [dTree180_eq f (by omega), dTree439_eq f (by omega)]

def dTree437 : Tree := .node dTree119 dTree438

theorem dTree437_eq (f : Nat) (hf : 31 ≤ f) :
    toTree pathDagPerm f 437 = dTree437 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 438) = Tree.node dTree119 dTree438
    simp only [dTree119_eq f (by omega), dTree438_eq f (by omega)]

def dTree436 : Tree := .node dTree218 dTree437

theorem dTree436_eq (f : Nat) (hf : 32 ≤ f) :
    toTree pathDagPerm f 436 = dTree436 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 218) (toTree pathDagPerm f 437) = Tree.node dTree218 dTree437
    simp only [dTree218_eq f (by omega), dTree437_eq f (by omega)]

def dTree435 : Tree := .node dTree180 dTree436

theorem dTree435_eq (f : Nat) (hf : 33 ≤ f) :
    toTree pathDagPerm f 435 = dTree435 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 436) = Tree.node dTree180 dTree436
    simp only [dTree180_eq f (by omega), dTree436_eq f (by omega)]

def dTree434 : Tree := .node dTree119 dTree435

theorem dTree434_eq (f : Nat) (hf : 34 ≤ f) :
    toTree pathDagPerm f 434 = dTree434 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 435) = Tree.node dTree119 dTree435
    simp only [dTree119_eq f (by omega), dTree435_eq f (by omega)]

def dTree433 : Tree := .node dTree218 dTree434

theorem dTree433_eq (f : Nat) (hf : 35 ≤ f) :
    toTree pathDagPerm f 433 = dTree433 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 218) (toTree pathDagPerm f 434) = Tree.node dTree218 dTree434
    simp only [dTree218_eq f (by omega), dTree434_eq f (by omega)]

def dTree432 : Tree := .node dTree180 dTree433

theorem dTree432_eq (f : Nat) (hf : 36 ≤ f) :
    toTree pathDagPerm f 432 = dTree432 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 433) = Tree.node dTree180 dTree433
    simp only [dTree180_eq f (by omega), dTree433_eq f (by omega)]

def dTree431 : Tree := .node dTree119 dTree432

theorem dTree431_eq (f : Nat) (hf : 37 ≤ f) :
    toTree pathDagPerm f 431 = dTree431 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 432) = Tree.node dTree119 dTree432
    simp only [dTree119_eq f (by omega), dTree432_eq f (by omega)]

def dTree430 : Tree := .node dTree180 dTree431

theorem dTree430_eq (f : Nat) (hf : 38 ≤ f) :
    toTree pathDagPerm f 430 = dTree430 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 431) = Tree.node dTree180 dTree431
    simp only [dTree180_eq f (by omega), dTree431_eq f (by omega)]

def dTree429 : Tree := .node dTree119 dTree430

theorem dTree429_eq (f : Nat) (hf : 39 ≤ f) :
    toTree pathDagPerm f 429 = dTree429 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 430) = Tree.node dTree119 dTree430
    simp only [dTree119_eq f (by omega), dTree430_eq f (by omega)]

def dTree428 : Tree := .node dTree218 dTree429

theorem dTree428_eq (f : Nat) (hf : 40 ≤ f) :
    toTree pathDagPerm f 428 = dTree428 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 218) (toTree pathDagPerm f 429) = Tree.node dTree218 dTree429
    simp only [dTree218_eq f (by omega), dTree429_eq f (by omega)]

def dTree427 : Tree := .node dTree180 dTree428

theorem dTree427_eq (f : Nat) (hf : 41 ≤ f) :
    toTree pathDagPerm f 427 = dTree427 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 428) = Tree.node dTree180 dTree428
    simp only [dTree180_eq f (by omega), dTree428_eq f (by omega)]

def dTree426 : Tree := .node dTree119 dTree427

theorem dTree426_eq (f : Nat) (hf : 42 ≤ f) :
    toTree pathDagPerm f 426 = dTree426 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 427) = Tree.node dTree119 dTree427
    simp only [dTree119_eq f (by omega), dTree427_eq f (by omega)]

def dTree425 : Tree := .node dTree218 dTree426

theorem dTree425_eq (f : Nat) (hf : 43 ≤ f) :
    toTree pathDagPerm f 425 = dTree425 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 218) (toTree pathDagPerm f 426) = Tree.node dTree218 dTree426
    simp only [dTree218_eq f (by omega), dTree426_eq f (by omega)]

def dTree424 : Tree := .node dTree181 dTree425

theorem dTree424_eq (f : Nat) (hf : 44 ≤ f) :
    toTree pathDagPerm f 424 = dTree424 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 181) (toTree pathDagPerm f 425) = Tree.node dTree181 dTree425
    simp only [dTree181_eq f (by omega), dTree425_eq f (by omega)]

def dTree423 : Tree := .node dTree168 dTree424

theorem dTree423_eq (f : Nat) (hf : 45 ≤ f) :
    toTree pathDagPerm f 423 = dTree423 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 424) = Tree.node dTree168 dTree424
    simp only [dTree168_eq f (by omega), dTree424_eq f (by omega)]

def dTree422 : Tree := .node dTree121 dTree423

theorem dTree422_eq (f : Nat) (hf : 46 ≤ f) :
    toTree pathDagPerm f 422 = dTree422 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 423) = Tree.node dTree121 dTree423
    simp only [dTree121_eq f (by omega), dTree423_eq f (by omega)]

def dTree421 : Tree := .node dTree168 dTree422

theorem dTree421_eq (f : Nat) (hf : 47 ≤ f) :
    toTree pathDagPerm f 421 = dTree421 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 422) = Tree.node dTree168 dTree422
    simp only [dTree168_eq f (by omega), dTree422_eq f (by omega)]

def dTree420 : Tree := .node dTree121 dTree421

theorem dTree420_eq (f : Nat) (hf : 48 ≤ f) :
    toTree pathDagPerm f 420 = dTree420 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 421) = Tree.node dTree121 dTree421
    simp only [dTree121_eq f (by omega), dTree421_eq f (by omega)]

def dTree419 : Tree := .node dTree168 dTree420

theorem dTree419_eq (f : Nat) (hf : 49 ≤ f) :
    toTree pathDagPerm f 419 = dTree419 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 420) = Tree.node dTree168 dTree420
    simp only [dTree168_eq f (by omega), dTree420_eq f (by omega)]

def dTree418 : Tree := .node dTree121 dTree419

theorem dTree418_eq (f : Nat) (hf : 50 ≤ f) :
    toTree pathDagPerm f 418 = dTree418 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 419) = Tree.node dTree121 dTree419
    simp only [dTree121_eq f (by omega), dTree419_eq f (by omega)]

def dTree417 : Tree := .node dTree180 dTree418

theorem dTree417_eq (f : Nat) (hf : 51 ≤ f) :
    toTree pathDagPerm f 417 = dTree417 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 418) = Tree.node dTree180 dTree418
    simp only [dTree180_eq f (by omega), dTree418_eq f (by omega)]

def dTree416 : Tree := .node dTree119 dTree417

theorem dTree416_eq (f : Nat) (hf : 52 ≤ f) :
    toTree pathDagPerm f 416 = dTree416 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 417) = Tree.node dTree119 dTree417
    simp only [dTree119_eq f (by omega), dTree417_eq f (by omega)]

def dTree415 : Tree := .node dTree181 dTree416

theorem dTree415_eq (f : Nat) (hf : 53 ≤ f) :
    toTree pathDagPerm f 415 = dTree415 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 181) (toTree pathDagPerm f 416) = Tree.node dTree181 dTree416
    simp only [dTree181_eq f (by omega), dTree416_eq f (by omega)]

def dTree414 : Tree := .node dTree121 dTree415

theorem dTree414_eq (f : Nat) (hf : 54 ≤ f) :
    toTree pathDagPerm f 414 = dTree414 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 415) = Tree.node dTree121 dTree415
    simp only [dTree121_eq f (by omega), dTree415_eq f (by omega)]

def dTree413 : Tree := .node dTree168 dTree414

theorem dTree413_eq (f : Nat) (hf : 55 ≤ f) :
    toTree pathDagPerm f 413 = dTree413 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 414) = Tree.node dTree168 dTree414
    simp only [dTree168_eq f (by omega), dTree414_eq f (by omega)]

def dTree412 : Tree := .node dTree181 dTree413

theorem dTree412_eq (f : Nat) (hf : 56 ≤ f) :
    toTree pathDagPerm f 412 = dTree412 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 181) (toTree pathDagPerm f 413) = Tree.node dTree181 dTree413
    simp only [dTree181_eq f (by omega), dTree413_eq f (by omega)]

def dTree411 : Tree := .node dTree166 dTree412

theorem dTree411_eq (f : Nat) (hf : 57 ≤ f) :
    toTree pathDagPerm f 411 = dTree411 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 412) = Tree.node dTree166 dTree412
    simp only [dTree166_eq f (by omega), dTree412_eq f (by omega)]

def dTree410 : Tree := .node dTree168 dTree411

theorem dTree410_eq (f : Nat) (hf : 58 ≤ f) :
    toTree pathDagPerm f 410 = dTree410 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 411) = Tree.node dTree168 dTree411
    simp only [dTree168_eq f (by omega), dTree411_eq f (by omega)]

def dTree409 : Tree := .node dTree168 dTree410

theorem dTree409_eq (f : Nat) (hf : 59 ≤ f) :
    toTree pathDagPerm f 409 = dTree409 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 410) = Tree.node dTree168 dTree410
    simp only [dTree168_eq f (by omega), dTree410_eq f (by omega)]

def dTree408 : Tree := .node dTree166 dTree409

theorem dTree408_eq (f : Nat) (hf : 60 ≤ f) :
    toTree pathDagPerm f 408 = dTree408 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 409) = Tree.node dTree166 dTree409
    simp only [dTree166_eq f (by omega), dTree409_eq f (by omega)]

def dTree407 : Tree := .node dTree168 dTree408

theorem dTree407_eq (f : Nat) (hf : 61 ≤ f) :
    toTree pathDagPerm f 407 = dTree407 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 408) = Tree.node dTree168 dTree408
    simp only [dTree168_eq f (by omega), dTree408_eq f (by omega)]

def dTree406 : Tree := .node dTree166 dTree407

theorem dTree406_eq (f : Nat) (hf : 62 ≤ f) :
    toTree pathDagPerm f 406 = dTree406 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 407) = Tree.node dTree166 dTree407
    simp only [dTree166_eq f (by omega), dTree407_eq f (by omega)]

def dTree405 : Tree := .node dTree181 dTree406

theorem dTree405_eq (f : Nat) (hf : 63 ≤ f) :
    toTree pathDagPerm f 405 = dTree405 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 181) (toTree pathDagPerm f 406) = Tree.node dTree181 dTree406
    simp only [dTree181_eq f (by omega), dTree406_eq f (by omega)]

def dTree404 : Tree := .node dTree168 dTree405

theorem dTree404_eq (f : Nat) (hf : 64 ≤ f) :
    toTree pathDagPerm f 404 = dTree404 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 405) = Tree.node dTree168 dTree405
    simp only [dTree168_eq f (by omega), dTree405_eq f (by omega)]

def dTree403 : Tree := .node dTree121 dTree404

theorem dTree403_eq (f : Nat) (hf : 65 ≤ f) :
    toTree pathDagPerm f 403 = dTree403 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 404) = Tree.node dTree121 dTree404
    simp only [dTree121_eq f (by omega), dTree404_eq f (by omega)]

def dTree402 : Tree := .node dTree121 dTree403

theorem dTree402_eq (f : Nat) (hf : 66 ≤ f) :
    toTree pathDagPerm f 402 = dTree402 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 403) = Tree.node dTree121 dTree403
    simp only [dTree121_eq f (by omega), dTree403_eq f (by omega)]

def dTree401 : Tree := .node dTree168 dTree402

theorem dTree401_eq (f : Nat) (hf : 67 ≤ f) :
    toTree pathDagPerm f 401 = dTree401 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 402) = Tree.node dTree168 dTree402
    simp only [dTree168_eq f (by omega), dTree402_eq f (by omega)]

def dTree400 : Tree := .node dTree119 dTree401

theorem dTree400_eq (f : Nat) (hf : 68 ≤ f) :
    toTree pathDagPerm f 400 = dTree400 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 401) = Tree.node dTree119 dTree401
    simp only [dTree119_eq f (by omega), dTree401_eq f (by omega)]

def dTree399 : Tree := .node dTree180 dTree400

theorem dTree399_eq (f : Nat) (hf : 69 ≤ f) :
    toTree pathDagPerm f 399 = dTree399 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 400) = Tree.node dTree180 dTree400
    simp only [dTree180_eq f (by omega), dTree400_eq f (by omega)]

def dTree398 : Tree := .node dTree181 dTree399

theorem dTree398_eq (f : Nat) (hf : 70 ≤ f) :
    toTree pathDagPerm f 398 = dTree398 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 181) (toTree pathDagPerm f 399) = Tree.node dTree181 dTree399
    simp only [dTree181_eq f (by omega), dTree399_eq f (by omega)]

def dTree397 : Tree := .node dTree121 dTree398

theorem dTree397_eq (f : Nat) (hf : 71 ≤ f) :
    toTree pathDagPerm f 397 = dTree397 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 398) = Tree.node dTree121 dTree398
    simp only [dTree121_eq f (by omega), dTree398_eq f (by omega)]

def dTree396 : Tree := .node dTree166 dTree397

theorem dTree396_eq (f : Nat) (hf : 72 ≤ f) :
    toTree pathDagPerm f 396 = dTree396 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 397) = Tree.node dTree166 dTree397
    simp only [dTree166_eq f (by omega), dTree397_eq f (by omega)]

def dTree395 : Tree := .node dTree168 dTree396

theorem dTree395_eq (f : Nat) (hf : 73 ≤ f) :
    toTree pathDagPerm f 395 = dTree395 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 396) = Tree.node dTree168 dTree396
    simp only [dTree168_eq f (by omega), dTree396_eq f (by omega)]

def dTree394 : Tree := .node dTree181 dTree395

theorem dTree394_eq (f : Nat) (hf : 74 ≤ f) :
    toTree pathDagPerm f 394 = dTree394 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 181) (toTree pathDagPerm f 395) = Tree.node dTree181 dTree395
    simp only [dTree181_eq f (by omega), dTree395_eq f (by omega)]

def dTree393 : Tree := .node dTree121 dTree394

theorem dTree393_eq (f : Nat) (hf : 75 ≤ f) :
    toTree pathDagPerm f 393 = dTree393 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 394) = Tree.node dTree121 dTree394
    simp only [dTree121_eq f (by omega), dTree394_eq f (by omega)]

def dTree392 : Tree := .node dTree166 dTree393

theorem dTree392_eq (f : Nat) (hf : 76 ≤ f) :
    toTree pathDagPerm f 392 = dTree392 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 393) = Tree.node dTree166 dTree393
    simp only [dTree166_eq f (by omega), dTree393_eq f (by omega)]

def dTree391 : Tree := .node dTree183 dTree392

theorem dTree391_eq (f : Nat) (hf : 77 ≤ f) :
    toTree pathDagPerm f 391 = dTree391 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 183) (toTree pathDagPerm f 392) = Tree.node dTree183 dTree392
    simp only [dTree183_eq f (by omega), dTree392_eq f (by omega)]

def dTree390 : Tree := .node dTree182 dTree391

theorem dTree390_eq (f : Nat) (hf : 78 ≤ f) :
    toTree pathDagPerm f 390 = dTree390 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 182) (toTree pathDagPerm f 391) = Tree.node dTree182 dTree391
    simp only [dTree182_eq f (by omega), dTree391_eq f (by omega)]

def dTree389 : Tree := .node dTree121 dTree390

theorem dTree389_eq (f : Nat) (hf : 79 ≤ f) :
    toTree pathDagPerm f 389 = dTree389 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 390) = Tree.node dTree121 dTree390
    simp only [dTree121_eq f (by omega), dTree390_eq f (by omega)]

def dTree388 : Tree := .node dTree166 dTree389

theorem dTree388_eq (f : Nat) (hf : 80 ≤ f) :
    toTree pathDagPerm f 388 = dTree388 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 389) = Tree.node dTree166 dTree389
    simp only [dTree166_eq f (by omega), dTree389_eq f (by omega)]

def dTree387 : Tree := .node dTree166 dTree388

theorem dTree387_eq (f : Nat) (hf : 81 ≤ f) :
    toTree pathDagPerm f 387 = dTree387 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 388) = Tree.node dTree166 dTree388
    simp only [dTree166_eq f (by omega), dTree388_eq f (by omega)]

def dTree386 : Tree := .node dTree119 dTree387

theorem dTree386_eq (f : Nat) (hf : 82 ≤ f) :
    toTree pathDagPerm f 386 = dTree386 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 387) = Tree.node dTree119 dTree387
    simp only [dTree119_eq f (by omega), dTree387_eq f (by omega)]

def dTree385 : Tree := .node dTree119 dTree386

theorem dTree385_eq (f : Nat) (hf : 83 ≤ f) :
    toTree pathDagPerm f 385 = dTree385 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 386) = Tree.node dTree119 dTree386
    simp only [dTree119_eq f (by omega), dTree386_eq f (by omega)]

def dTree384 : Tree := .node dTree180 dTree385

theorem dTree384_eq (f : Nat) (hf : 84 ≤ f) :
    toTree pathDagPerm f 384 = dTree384 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 385) = Tree.node dTree180 dTree385
    simp only [dTree180_eq f (by omega), dTree385_eq f (by omega)]

def dTree383 : Tree := .node dTree168 dTree384

theorem dTree383_eq (f : Nat) (hf : 85 ≤ f) :
    toTree pathDagPerm f 383 = dTree383 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 384) = Tree.node dTree168 dTree384
    simp only [dTree168_eq f (by omega), dTree384_eq f (by omega)]

def dTree382 : Tree := .node dTree166 dTree383

theorem dTree382_eq (f : Nat) (hf : 86 ≤ f) :
    toTree pathDagPerm f 382 = dTree382 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 383) = Tree.node dTree166 dTree383
    simp only [dTree166_eq f (by omega), dTree383_eq f (by omega)]

def dTree381 : Tree := .node dTree180 dTree382

theorem dTree381_eq (f : Nat) (hf : 87 ≤ f) :
    toTree pathDagPerm f 381 = dTree381 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 382) = Tree.node dTree180 dTree382
    simp only [dTree180_eq f (by omega), dTree382_eq f (by omega)]

def dTree380 : Tree := .node dTree121 dTree381

theorem dTree380_eq (f : Nat) (hf : 88 ≤ f) :
    toTree pathDagPerm f 380 = dTree380 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 381) = Tree.node dTree121 dTree381
    simp only [dTree121_eq f (by omega), dTree381_eq f (by omega)]

def dTree379 : Tree := .node dTree166 dTree380

theorem dTree379_eq (f : Nat) (hf : 89 ≤ f) :
    toTree pathDagPerm f 379 = dTree379 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 380) = Tree.node dTree166 dTree380
    simp only [dTree166_eq f (by omega), dTree380_eq f (by omega)]

def dTree378 : Tree := .node dTree180 dTree379

theorem dTree378_eq (f : Nat) (hf : 90 ≤ f) :
    toTree pathDagPerm f 378 = dTree378 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 379) = Tree.node dTree180 dTree379
    simp only [dTree180_eq f (by omega), dTree379_eq f (by omega)]

def dTree377 : Tree := .node dTree119 dTree378

theorem dTree377_eq (f : Nat) (hf : 91 ≤ f) :
    toTree pathDagPerm f 377 = dTree377 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 378) = Tree.node dTree119 dTree378
    simp only [dTree119_eq f (by omega), dTree378_eq f (by omega)]

def dTree376 : Tree := .node dTree168 dTree377

theorem dTree376_eq (f : Nat) (hf : 92 ≤ f) :
    toTree pathDagPerm f 376 = dTree376 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 377) = Tree.node dTree168 dTree377
    simp only [dTree168_eq f (by omega), dTree377_eq f (by omega)]

def dTree375 : Tree := .node dTree121 dTree376

theorem dTree375_eq (f : Nat) (hf : 93 ≤ f) :
    toTree pathDagPerm f 375 = dTree375 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 376) = Tree.node dTree121 dTree376
    simp only [dTree121_eq f (by omega), dTree376_eq f (by omega)]

def dTree374 : Tree := .node dTree166 dTree375

theorem dTree374_eq (f : Nat) (hf : 94 ≤ f) :
    toTree pathDagPerm f 374 = dTree374 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 375) = Tree.node dTree166 dTree375
    simp only [dTree166_eq f (by omega), dTree375_eq f (by omega)]

def dTree373 : Tree := .node dTree119 dTree374

theorem dTree373_eq (f : Nat) (hf : 95 ≤ f) :
    toTree pathDagPerm f 373 = dTree373 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 374) = Tree.node dTree119 dTree374
    simp only [dTree119_eq f (by omega), dTree374_eq f (by omega)]

def dTree372 : Tree := .node dTree119 dTree373

theorem dTree372_eq (f : Nat) (hf : 96 ≤ f) :
    toTree pathDagPerm f 372 = dTree372 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 373) = Tree.node dTree119 dTree373
    simp only [dTree119_eq f (by omega), dTree373_eq f (by omega)]

def dTree371 : Tree := .node dTree181 dTree372

theorem dTree371_eq (f : Nat) (hf : 97 ≤ f) :
    toTree pathDagPerm f 371 = dTree371 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 181) (toTree pathDagPerm f 372) = Tree.node dTree181 dTree372
    simp only [dTree181_eq f (by omega), dTree372_eq f (by omega)]

def dTree370 : Tree := .node dTree121 dTree371

theorem dTree370_eq (f : Nat) (hf : 98 ≤ f) :
    toTree pathDagPerm f 370 = dTree370 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 371) = Tree.node dTree121 dTree371
    simp only [dTree121_eq f (by omega), dTree371_eq f (by omega)]

def dTree369 : Tree := .node dTree168 dTree370

theorem dTree369_eq (f : Nat) (hf : 99 ≤ f) :
    toTree pathDagPerm f 369 = dTree369 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 370) = Tree.node dTree168 dTree370
    simp only [dTree168_eq f (by omega), dTree370_eq f (by omega)]

def dTree368 : Tree := .node dTree181 dTree369

theorem dTree368_eq (f : Nat) (hf : 100 ≤ f) :
    toTree pathDagPerm f 368 = dTree368 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 181) (toTree pathDagPerm f 369) = Tree.node dTree181 dTree369
    simp only [dTree181_eq f (by omega), dTree369_eq f (by omega)]

def dTree367 : Tree := .node dTree166 dTree368

theorem dTree367_eq (f : Nat) (hf : 101 ≤ f) :
    toTree pathDagPerm f 367 = dTree367 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 368) = Tree.node dTree166 dTree368
    simp only [dTree166_eq f (by omega), dTree368_eq f (by omega)]

def dTree366 : Tree := .node dTree168 dTree367

theorem dTree366_eq (f : Nat) (hf : 102 ≤ f) :
    toTree pathDagPerm f 366 = dTree366 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 367) = Tree.node dTree168 dTree367
    simp only [dTree168_eq f (by omega), dTree367_eq f (by omega)]

def dTree365 : Tree := .node dTree182 dTree366

theorem dTree365_eq (f : Nat) (hf : 103 ≤ f) :
    toTree pathDagPerm f 365 = dTree365 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 182) (toTree pathDagPerm f 366) = Tree.node dTree182 dTree366
    simp only [dTree182_eq f (by omega), dTree366_eq f (by omega)]

def dTree364 : Tree := .node dTree121 dTree365

theorem dTree364_eq (f : Nat) (hf : 104 ≤ f) :
    toTree pathDagPerm f 364 = dTree364 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 365) = Tree.node dTree121 dTree365
    simp only [dTree121_eq f (by omega), dTree365_eq f (by omega)]

def dTree363 : Tree := .node dTree166 dTree364

theorem dTree363_eq (f : Nat) (hf : 105 ≤ f) :
    toTree pathDagPerm f 363 = dTree363 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 364) = Tree.node dTree166 dTree364
    simp only [dTree166_eq f (by omega), dTree364_eq f (by omega)]

def dTree362 : Tree := .node dTree119 dTree363

theorem dTree362_eq (f : Nat) (hf : 106 ≤ f) :
    toTree pathDagPerm f 362 = dTree362 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 363) = Tree.node dTree119 dTree363
    simp only [dTree119_eq f (by omega), dTree363_eq f (by omega)]

def dTree361 : Tree := .node dTree180 dTree362

theorem dTree361_eq (f : Nat) (hf : 107 ≤ f) :
    toTree pathDagPerm f 361 = dTree361 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 362) = Tree.node dTree180 dTree362
    simp only [dTree180_eq f (by omega), dTree362_eq f (by omega)]

def dTree360 : Tree := .node dTree180 dTree361

theorem dTree360_eq (f : Nat) (hf : 108 ≤ f) :
    toTree pathDagPerm f 360 = dTree360 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 361) = Tree.node dTree180 dTree361
    simp only [dTree180_eq f (by omega), dTree361_eq f (by omega)]

def dTree359 : Tree := .node dTree168 dTree360

theorem dTree359_eq (f : Nat) (hf : 109 ≤ f) :
    toTree pathDagPerm f 359 = dTree359 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 360) = Tree.node dTree168 dTree360
    simp only [dTree168_eq f (by omega), dTree360_eq f (by omega)]

def dTree358 : Tree := .node dTree166 dTree359

theorem dTree358_eq (f : Nat) (hf : 110 ≤ f) :
    toTree pathDagPerm f 358 = dTree358 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 359) = Tree.node dTree166 dTree359
    simp only [dTree166_eq f (by omega), dTree359_eq f (by omega)]

def dTree357 : Tree := .node dTree121 dTree358

theorem dTree357_eq (f : Nat) (hf : 111 ≤ f) :
    toTree pathDagPerm f 357 = dTree357 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 358) = Tree.node dTree121 dTree358
    simp only [dTree121_eq f (by omega), dTree358_eq f (by omega)]

def dTree356 : Tree := .node dTree180 dTree357

theorem dTree356_eq (f : Nat) (hf : 112 ≤ f) :
    toTree pathDagPerm f 356 = dTree356 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 357) = Tree.node dTree180 dTree357
    simp only [dTree180_eq f (by omega), dTree357_eq f (by omega)]

def dTree355 : Tree := .node dTree180 dTree356

theorem dTree355_eq (f : Nat) (hf : 113 ≤ f) :
    toTree pathDagPerm f 355 = dTree355 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 356) = Tree.node dTree180 dTree356
    simp only [dTree180_eq f (by omega), dTree356_eq f (by omega)]

def dTree354 : Tree := .node dTree168 dTree355

theorem dTree354_eq (f : Nat) (hf : 114 ≤ f) :
    toTree pathDagPerm f 354 = dTree354 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 355) = Tree.node dTree168 dTree355
    simp only [dTree168_eq f (by omega), dTree355_eq f (by omega)]

def dTree353 : Tree := .node dTree121 dTree354

theorem dTree353_eq (f : Nat) (hf : 115 ≤ f) :
    toTree pathDagPerm f 353 = dTree353 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 354) = Tree.node dTree121 dTree354
    simp only [dTree121_eq f (by omega), dTree354_eq f (by omega)]

def dTree352 : Tree := .node dTree166 dTree353

theorem dTree352_eq (f : Nat) (hf : 116 ≤ f) :
    toTree pathDagPerm f 352 = dTree352 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 353) = Tree.node dTree166 dTree353
    simp only [dTree166_eq f (by omega), dTree353_eq f (by omega)]

def dTree351 : Tree := .node dTree119 dTree352

theorem dTree351_eq (f : Nat) (hf : 117 ≤ f) :
    toTree pathDagPerm f 351 = dTree351 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 352) = Tree.node dTree119 dTree352
    simp only [dTree119_eq f (by omega), dTree352_eq f (by omega)]

def dTree350 : Tree := .node dTree119 dTree351

theorem dTree350_eq (f : Nat) (hf : 118 ≤ f) :
    toTree pathDagPerm f 350 = dTree350 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 351) = Tree.node dTree119 dTree351
    simp only [dTree119_eq f (by omega), dTree351_eq f (by omega)]

def dTree349 : Tree := .node dTree181 dTree350

theorem dTree349_eq (f : Nat) (hf : 119 ≤ f) :
    toTree pathDagPerm f 349 = dTree349 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 181) (toTree pathDagPerm f 350) = Tree.node dTree181 dTree350
    simp only [dTree181_eq f (by omega), dTree350_eq f (by omega)]

def dTree348 : Tree := .node dTree121 dTree349

theorem dTree348_eq (f : Nat) (hf : 120 ≤ f) :
    toTree pathDagPerm f 348 = dTree348 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 349) = Tree.node dTree121 dTree349
    simp only [dTree121_eq f (by omega), dTree349_eq f (by omega)]

def dTree347 : Tree := .node dTree166 dTree348

theorem dTree347_eq (f : Nat) (hf : 121 ≤ f) :
    toTree pathDagPerm f 347 = dTree347 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 348) = Tree.node dTree166 dTree348
    simp only [dTree166_eq f (by omega), dTree348_eq f (by omega)]

def dTree346 : Tree := .node dTree181 dTree347

theorem dTree346_eq (f : Nat) (hf : 122 ≤ f) :
    toTree pathDagPerm f 346 = dTree346 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 181) (toTree pathDagPerm f 347) = Tree.node dTree181 dTree347
    simp only [dTree181_eq f (by omega), dTree347_eq f (by omega)]

def dTree345 : Tree := .node dTree121 dTree346

theorem dTree345_eq (f : Nat) (hf : 123 ≤ f) :
    toTree pathDagPerm f 345 = dTree345 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 346) = Tree.node dTree121 dTree346
    simp only [dTree121_eq f (by omega), dTree346_eq f (by omega)]

def dTree344 : Tree := .node dTree168 dTree345

theorem dTree344_eq (f : Nat) (hf : 124 ≤ f) :
    toTree pathDagPerm f 344 = dTree344 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 345) = Tree.node dTree168 dTree345
    simp only [dTree168_eq f (by omega), dTree345_eq f (by omega)]

def dTree343 : Tree := .node dTree182 dTree344

theorem dTree343_eq (f : Nat) (hf : 125 ≤ f) :
    toTree pathDagPerm f 343 = dTree343 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 182) (toTree pathDagPerm f 344) = Tree.node dTree182 dTree344
    simp only [dTree182_eq f (by omega), dTree344_eq f (by omega)]

def dTree342 : Tree := .node dTree166 dTree343

theorem dTree342_eq (f : Nat) (hf : 126 ≤ f) :
    toTree pathDagPerm f 342 = dTree342 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 343) = Tree.node dTree166 dTree343
    simp only [dTree166_eq f (by omega), dTree343_eq f (by omega)]

def dTree341 : Tree := .node dTree168 dTree342

theorem dTree341_eq (f : Nat) (hf : 127 ≤ f) :
    toTree pathDagPerm f 341 = dTree341 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 342) = Tree.node dTree168 dTree342
    simp only [dTree168_eq f (by omega), dTree342_eq f (by omega)]

def dTree340 : Tree := .node dTree119 dTree341

theorem dTree340_eq (f : Nat) (hf : 128 ≤ f) :
    toTree pathDagPerm f 340 = dTree340 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 341) = Tree.node dTree119 dTree341
    simp only [dTree119_eq f (by omega), dTree341_eq f (by omega)]

def dTree339 : Tree := .node dTree168 dTree340

theorem dTree339_eq (f : Nat) (hf : 129 ≤ f) :
    toTree pathDagPerm f 339 = dTree339 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 340) = Tree.node dTree168 dTree340
    simp only [dTree168_eq f (by omega), dTree340_eq f (by omega)]

def dTree338 : Tree := .node dTree183 dTree339

theorem dTree338_eq (f : Nat) (hf : 130 ≤ f) :
    toTree pathDagPerm f 338 = dTree338 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 183) (toTree pathDagPerm f 339) = Tree.node dTree183 dTree339
    simp only [dTree183_eq f (by omega), dTree339_eq f (by omega)]

def dTree337 : Tree := .node dTree180 dTree338

theorem dTree337_eq (f : Nat) (hf : 131 ≤ f) :
    toTree pathDagPerm f 337 = dTree337 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 338) = Tree.node dTree180 dTree338
    simp only [dTree180_eq f (by omega), dTree338_eq f (by omega)]

def dTree336 : Tree := .node dTree168 dTree337

theorem dTree336_eq (f : Nat) (hf : 132 ≤ f) :
    toTree pathDagPerm f 336 = dTree336 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 337) = Tree.node dTree168 dTree337
    simp only [dTree168_eq f (by omega), dTree337_eq f (by omega)]

def dTree335 : Tree := .node dTree166 dTree336

theorem dTree335_eq (f : Nat) (hf : 133 ≤ f) :
    toTree pathDagPerm f 335 = dTree335 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 336) = Tree.node dTree166 dTree336
    simp only [dTree166_eq f (by omega), dTree336_eq f (by omega)]

def dTree334 : Tree := .node dTree166 dTree335

theorem dTree334_eq (f : Nat) (hf : 134 ≤ f) :
    toTree pathDagPerm f 334 = dTree334 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 335) = Tree.node dTree166 dTree335
    simp only [dTree166_eq f (by omega), dTree335_eq f (by omega)]

def dTree333 : Tree := .node dTree119 dTree334

theorem dTree333_eq (f : Nat) (hf : 135 ≤ f) :
    toTree pathDagPerm f 333 = dTree333 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 334) = Tree.node dTree119 dTree334
    simp only [dTree119_eq f (by omega), dTree334_eq f (by omega)]

def dTree332 : Tree := .node dTree119 dTree333

theorem dTree332_eq (f : Nat) (hf : 136 ≤ f) :
    toTree pathDagPerm f 332 = dTree332 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 333) = Tree.node dTree119 dTree333
    simp only [dTree119_eq f (by omega), dTree333_eq f (by omega)]

def dTree331 : Tree := .node dTree180 dTree332

theorem dTree331_eq (f : Nat) (hf : 137 ≤ f) :
    toTree pathDagPerm f 331 = dTree331 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 332) = Tree.node dTree180 dTree332
    simp only [dTree180_eq f (by omega), dTree332_eq f (by omega)]

def dTree330 : Tree := .node dTree182 dTree331

theorem dTree330_eq (f : Nat) (hf : 138 ≤ f) :
    toTree pathDagPerm f 330 = dTree330 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 182) (toTree pathDagPerm f 331) = Tree.node dTree182 dTree331
    simp only [dTree182_eq f (by omega), dTree331_eq f (by omega)]

def dTree329 : Tree := .node dTree121 dTree330

theorem dTree329_eq (f : Nat) (hf : 139 ≤ f) :
    toTree pathDagPerm f 329 = dTree329 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 330) = Tree.node dTree121 dTree330
    simp only [dTree121_eq f (by omega), dTree330_eq f (by omega)]

def dTree328 : Tree := .node dTree166 dTree329

theorem dTree328_eq (f : Nat) (hf : 140 ≤ f) :
    toTree pathDagPerm f 328 = dTree328 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 329) = Tree.node dTree166 dTree329
    simp only [dTree166_eq f (by omega), dTree329_eq f (by omega)]

def dTree327 : Tree := .node dTree181 dTree328

theorem dTree327_eq (f : Nat) (hf : 141 ≤ f) :
    toTree pathDagPerm f 327 = dTree327 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 181) (toTree pathDagPerm f 328) = Tree.node dTree181 dTree328
    simp only [dTree181_eq f (by omega), dTree328_eq f (by omega)]

def dTree326 : Tree := .node dTree121 dTree327

theorem dTree326_eq (f : Nat) (hf : 142 ≤ f) :
    toTree pathDagPerm f 326 = dTree326 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 327) = Tree.node dTree121 dTree327
    simp only [dTree121_eq f (by omega), dTree327_eq f (by omega)]

def dTree325 : Tree := .node dTree166 dTree326

theorem dTree325_eq (f : Nat) (hf : 143 ≤ f) :
    toTree pathDagPerm f 325 = dTree325 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 326) = Tree.node dTree166 dTree326
    simp only [dTree166_eq f (by omega), dTree326_eq f (by omega)]

def dTree324 : Tree := .node dTree182 dTree325

theorem dTree324_eq (f : Nat) (hf : 144 ≤ f) :
    toTree pathDagPerm f 324 = dTree324 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 182) (toTree pathDagPerm f 325) = Tree.node dTree182 dTree325
    simp only [dTree182_eq f (by omega), dTree325_eq f (by omega)]

def dTree323 : Tree := .node dTree121 dTree324

theorem dTree323_eq (f : Nat) (hf : 145 ≤ f) :
    toTree pathDagPerm f 323 = dTree323 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 324) = Tree.node dTree121 dTree324
    simp only [dTree121_eq f (by omega), dTree324_eq f (by omega)]

def dTree322 : Tree := .node dTree168 dTree323

theorem dTree322_eq (f : Nat) (hf : 146 ≤ f) :
    toTree pathDagPerm f 322 = dTree322 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 323) = Tree.node dTree168 dTree323
    simp only [dTree168_eq f (by omega), dTree323_eq f (by omega)]

def dTree321 : Tree := .node dTree182 dTree322

theorem dTree321_eq (f : Nat) (hf : 147 ≤ f) :
    toTree pathDagPerm f 321 = dTree321 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 182) (toTree pathDagPerm f 322) = Tree.node dTree182 dTree322
    simp only [dTree182_eq f (by omega), dTree322_eq f (by omega)]

def dTree320 : Tree := .node dTree166 dTree321

theorem dTree320_eq (f : Nat) (hf : 148 ≤ f) :
    toTree pathDagPerm f 320 = dTree320 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 321) = Tree.node dTree166 dTree321
    simp only [dTree166_eq f (by omega), dTree321_eq f (by omega)]

def dTree319 : Tree := .node dTree168 dTree320

theorem dTree319_eq (f : Nat) (hf : 149 ≤ f) :
    toTree pathDagPerm f 319 = dTree319 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 320) = Tree.node dTree168 dTree320
    simp only [dTree168_eq f (by omega), dTree320_eq f (by omega)]

def dTree483 : Tree := .node dTree119 dTree319

theorem dTree483_eq (f : Nat) (hf : 150 ≤ f) :
    toTree pathDagPerm f 483 = dTree483 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 319) = Tree.node dTree119 dTree319
    simp only [dTree119_eq f (by omega), dTree319_eq f (by omega)]

def dTree482 : Tree := .node dTree119 dTree483

theorem dTree482_eq (f : Nat) (hf : 151 ≤ f) :
    toTree pathDagPerm f 482 = dTree482 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 483) = Tree.node dTree119 dTree483
    simp only [dTree119_eq f (by omega), dTree483_eq f (by omega)]

def dTree481 : Tree := .node dTree119 dTree482

theorem dTree481_eq (f : Nat) (hf : 152 ≤ f) :
    toTree pathDagPerm f 481 = dTree481 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 482) = Tree.node dTree119 dTree482
    simp only [dTree119_eq f (by omega), dTree482_eq f (by omega)]

def dTree480 : Tree := .node dTree168 dTree481

theorem dTree480_eq (f : Nat) (hf : 153 ≤ f) :
    toTree pathDagPerm f 480 = dTree480 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 481) = Tree.node dTree168 dTree481
    simp only [dTree168_eq f (by omega), dTree481_eq f (by omega)]

def dTree479 : Tree := .node dTree121 dTree480

theorem dTree479_eq (f : Nat) (hf : 154 ≤ f) :
    toTree pathDagPerm f 479 = dTree479 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 480) = Tree.node dTree121 dTree480
    simp only [dTree121_eq f (by omega), dTree480_eq f (by omega)]

def dTree478 : Tree := .node dTree119 dTree479

theorem dTree478_eq (f : Nat) (hf : 155 ≤ f) :
    toTree pathDagPerm f 478 = dTree478 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 479) = Tree.node dTree119 dTree479
    simp only [dTree119_eq f (by omega), dTree479_eq f (by omega)]

def dTree477 : Tree := .node dTree168 dTree478

theorem dTree477_eq (f : Nat) (hf : 156 ≤ f) :
    toTree pathDagPerm f 477 = dTree477 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 478) = Tree.node dTree168 dTree478
    simp only [dTree168_eq f (by omega), dTree478_eq f (by omega)]

def dTree476 : Tree := .node dTree166 dTree477

theorem dTree476_eq (f : Nat) (hf : 157 ≤ f) :
    toTree pathDagPerm f 476 = dTree476 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 477) = Tree.node dTree166 dTree477
    simp only [dTree166_eq f (by omega), dTree477_eq f (by omega)]

def dTree475 : Tree := .node dTree119 dTree476

theorem dTree475_eq (f : Nat) (hf : 158 ≤ f) :
    toTree pathDagPerm f 475 = dTree475 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 476) = Tree.node dTree119 dTree476
    simp only [dTree119_eq f (by omega), dTree476_eq f (by omega)]

def dTree474 : Tree := .node dTree166 dTree475

theorem dTree474_eq (f : Nat) (hf : 159 ≤ f) :
    toTree pathDagPerm f 474 = dTree474 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 475) = Tree.node dTree166 dTree475
    simp only [dTree166_eq f (by omega), dTree475_eq f (by omega)]

def dTree486 : Tree := .node dTree175 dTree474

theorem dTree486_eq (f : Nat) (hf : 160 ≤ f) :
    toTree pathDagPerm f 486 = dTree486 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 175) (toTree pathDagPerm f 474) = Tree.node dTree175 dTree474
    simp only [dTree175_eq f (by omega), dTree474_eq f (by omega)]

def dTree485 : Tree := .node dTree119 dTree486

theorem dTree485_eq (f : Nat) (hf : 161 ≤ f) :
    toTree pathDagPerm f 485 = dTree485 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 119) (toTree pathDagPerm f 486) = Tree.node dTree119 dTree486
    simp only [dTree119_eq f (by omega), dTree486_eq f (by omega)]

def dTree471 : Tree := .node dTree176 dTree485

theorem dTree471_eq (f : Nat) (hf : 162 ≤ f) :
    toTree pathDagPerm f 471 = dTree471 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 176) (toTree pathDagPerm f 485) = Tree.node dTree176 dTree485
    simp only [dTree176_eq f (by omega), dTree485_eq f (by omega)]

def dTree470 : Tree := .node dTree166 dTree471

theorem dTree470_eq (f : Nat) (hf : 163 ≤ f) :
    toTree pathDagPerm f 470 = dTree470 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 471) = Tree.node dTree166 dTree471
    simp only [dTree166_eq f (by omega), dTree471_eq f (by omega)]

def dTree469 : Tree := .node dTree168 dTree470

theorem dTree469_eq (f : Nat) (hf : 164 ≤ f) :
    toTree pathDagPerm f 469 = dTree469 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 168) (toTree pathDagPerm f 470) = Tree.node dTree168 dTree470
    simp only [dTree168_eq f (by omega), dTree470_eq f (by omega)]

def dTree468 : Tree := .node dTree180 dTree469

theorem dTree468_eq (f : Nat) (hf : 165 ≤ f) :
    toTree pathDagPerm f 468 = dTree468 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 180) (toTree pathDagPerm f 469) = Tree.node dTree180 dTree469
    simp only [dTree180_eq f (by omega), dTree469_eq f (by omega)]

def dTree467 : Tree := .node dTree121 dTree468

theorem dTree467_eq (f : Nat) (hf : 166 ≤ f) :
    toTree pathDagPerm f 467 = dTree467 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 121) (toTree pathDagPerm f 468) = Tree.node dTree121 dTree468
    simp only [dTree121_eq f (by omega), dTree468_eq f (by omega)]

def dTree236 : Tree := .node dTree166 dTree467

theorem dTree236_eq (f : Nat) (hf : 167 ≤ f) :
    toTree pathDagPerm f 236 = dTree236 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 467) = Tree.node dTree166 dTree467
    simp only [dTree166_eq f (by omega), dTree467_eq f (by omega)]

def dTree149 : Tree := .node dTree236 (.leaf (.brk 1))

theorem dTree149_eq (f : Nat) (hf : 168 ≤ f) :
    toTree pathDagPerm f 149 = dTree149 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 236) (.leaf (.brk 1)) = Tree.node dTree236 (.leaf (.brk 1))
    simp only [dTree236_eq f (by omega)]

def dTree148 : Tree := .node (.leaf (.decnz 3)) dTree149

theorem dTree148_eq (f : Nat) (hf : 169 ≤ f) :
    toTree pathDagPerm f 148 = dTree148 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 3)) (toTree pathDagPerm f 149) = Tree.node (.leaf (.decnz 3)) dTree149
    simp only [dTree149_eq f (by omega)]

def dTree161 : Tree := .node dTree166 dTree119

theorem dTree161_eq (f : Nat) (hf : 11 ≤ f) :
    toTree pathDagPerm f 161 = dTree161 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 166) (toTree pathDagPerm f 119) = Tree.node dTree166 dTree119
    simp only [dTree166_eq f (by omega), dTree119_eq f (by omega)]

def dTree130 : Tree := .node dTree123 dTree166

theorem dTree130_eq (f : Nat) (hf : 11 ≤ f) :
    toTree pathDagPerm f 130 = dTree130 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 123) (toTree pathDagPerm f 166) = Tree.node dTree123 dTree166
    simp only [dTree123_eq f (by omega), dTree166_eq f (by omega)]

def dTree151 : Tree := .node dTree216 dTree130

theorem dTree151_eq (f : Nat) (hf : 12 ≤ f) :
    toTree pathDagPerm f 151 = dTree151 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 216) (toTree pathDagPerm f 130) = Tree.node dTree216 dTree130
    simp only [dTree216_eq f (by omega), dTree130_eq f (by omega)]

def dTree150 : Tree := .node dTree161 dTree151

theorem dTree150_eq (f : Nat) (hf : 13 ≤ f) :
    toTree pathDagPerm f 150 = dTree150 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 161) (toTree pathDagPerm f 151) = Tree.node dTree161 dTree151
    simp only [dTree161_eq f (by omega), dTree151_eq f (by omega)]

def dTree484 : Tree := .node dTree175 dTree150

theorem dTree484_eq (f : Nat) (hf : 14 ≤ f) :
    toTree pathDagPerm f 484 = dTree484 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 175) (toTree pathDagPerm f 150) = Tree.node dTree175 dTree150
    simp only [dTree175_eq f (by omega), dTree150_eq f (by omega)]

def dTree147 : Tree := .node dTree148 dTree484

theorem dTree147_eq (f : Nat) (hf : 170 ≤ f) :
    toTree pathDagPerm f 147 = dTree147 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 148) (toTree pathDagPerm f 484) = Tree.node dTree148 dTree484
    simp only [dTree148_eq f (by omega), dTree484_eq f (by omega)]

def dTree146 : Tree := .node dTree147 (.leaf (.brk 1))

theorem dTree146_eq (f : Nat) (hf : 171 ≤ f) :
    toTree pathDagPerm f 146 = dTree146 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 147) (.leaf (.brk 1)) = Tree.node dTree147 (.leaf (.brk 1))
    simp only [dTree147_eq f (by omega)]

def dTree145 : Tree := .node (.leaf (.decnz 3)) dTree146

theorem dTree145_eq (f : Nat) (hf : 172 ≤ f) :
    toTree pathDagPerm f 145 = dTree145 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 3)) (toTree pathDagPerm f 146) = Tree.node (.leaf (.decnz 3)) dTree146
    simp only [dTree146_eq f (by omega)]

def dTree144 : Tree := .node dTree145 dTree121

theorem dTree144_eq (f : Nat) (hf : 173 ≤ f) :
    toTree pathDagPerm f 144 = dTree144 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 145) (toTree pathDagPerm f 121) = Tree.node dTree145 dTree121
    simp only [dTree145_eq f (by omega), dTree121_eq f (by omega)]

def dTree143 : Tree := .node dTree144 (.leaf (.brk 1))

theorem dTree143_eq (f : Nat) (hf : 174 ≤ f) :
    toTree pathDagPerm f 143 = dTree143 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 144) (.leaf (.brk 1)) = Tree.node dTree144 (.leaf (.brk 1))
    simp only [dTree144_eq f (by omega)]

def dTree142 : Tree := .node (.leaf (.decnz 3)) dTree143

theorem dTree142_eq (f : Nat) (hf : 175 ≤ f) :
    toTree pathDagPerm f 142 = dTree142 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.decnz 3)) (toTree pathDagPerm f 143) = Tree.node (.leaf (.decnz 3)) dTree143
    simp only [dTree143_eq f (by omega)]

def dTree132 : Tree := .node dTree123 (.leaf (.halt))

theorem dTree132_eq (f : Nat) (hf : 6 ≤ f) :
    toTree pathDagPerm f 132 = dTree132 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 123) (.leaf (.halt)) = Tree.node dTree123 (.leaf (.halt))
    simp only [dTree123_eq f (by omega)]

def dTree170 : Tree := .node dTree160 dTree207

theorem dTree170_eq (f : Nat) (hf : 8 ≤ f) :
    toTree pathDagPerm f 170 = dTree170 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 160) (toTree pathDagPerm f 207) = Tree.node dTree160 dTree207
    simp only [dTree160_eq f (by omega), dTree207_eq f (by omega)]

def dTree153 : Tree := .node dTree132 dTree170

theorem dTree153_eq (f : Nat) (hf : 9 ≤ f) :
    toTree pathDagPerm f 153 = dTree153 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 132) (toTree pathDagPerm f 170) = Tree.node dTree132 dTree170
    simp only [dTree132_eq f (by omega), dTree170_eq f (by omega)]

def dTree152 : Tree := .node (.leaf (.inc 6)) dTree153

theorem dTree152_eq (f : Nat) (hf : 10 ≤ f) :
    toTree pathDagPerm f 152 = dTree152 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (.leaf (.inc 6)) (toTree pathDagPerm f 153) = Tree.node (.leaf (.inc 6)) dTree153
    simp only [dTree153_eq f (by omega)]

def dTree141 : Tree := .node dTree142 dTree152

theorem dTree141_eq (f : Nat) (hf : 176 ≤ f) :
    toTree pathDagPerm f 141 = dTree141 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 142) (toTree pathDagPerm f 152) = Tree.node dTree142 dTree152
    simp only [dTree142_eq f (by omega), dTree152_eq f (by omega)]

def dTree139 : Tree := .node dTree174 dTree141

theorem dTree139_eq (f : Nat) (hf : 177 ≤ f) :
    toTree pathDagPerm f 139 = dTree139 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 174) (toTree pathDagPerm f 141) = Tree.node dTree174 dTree141
    simp only [dTree174_eq f (by omega), dTree141_eq f (by omega)]

def dTree0 : Tree := .node dTree133 dTree139

theorem dTree0_eq (f : Nat) (hf : 178 ≤ f) :
    toTree pathDagPerm f 0 = dTree0 := by
  cases f with
  | zero => omega
  | succ f =>
    rw [toTree_succ]
    change Tree.node (toTree pathDagPerm f 133) (toTree pathDagPerm f 139) = Tree.node dTree133 dTree139
    simp only [dTree133_eq f (by omega), dTree139_eq f (by omega)]

def t215 : Tree := sTree178
def tD : Tree := dTree0

theorem t215_eq : ptree p215 = t215 := sTree178_eq 180 (by decide)
theorem tD_eq : ptree pathDagPerm = tD := dTree0_eq 488 (by decide)

#print axioms t215_eq
#print axioms tD_eq

end SetTheory.BusyBeaver.ZFC.KSource215
