import BusyBeaver.ZFC.ProgramRotation244
import BusyBeaver.ZFC.RMDagLoopRotation
import BusyBeaver.ZFC.RMDagContextSubstitution

/-!
Exact logical QT rotation in the shared203-row routed program. The only changed
rows are5 and6. Structured loop replacement preserves every complete register
file and exit at the admitted context; finite WF certificates connect it to
RegisterPath halting from the empty pointer for arbitrary register functions.
This source theorem does not establish a binary runtime or blank startup.
-/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.SourceRotation244
open RMDag

def toDagEdge : RegisterPath.Edge → RMDag.Edge
  | .node n => .node n
  | .inc r => .inc r
  | .decnz r => .decnz r
  | .brk k => .brk k
  | .cont k => .cont k
  | .halt => .halt

theorem toPath_toDagEdge (e : RegisterPath.Edge) :
    RMEquiv.toPath (toDagEdge e) = e := by
  cases e <;> rfl

def ofProgram (p : RegisterPath.Program) : RMDag.Prog where
  nodes := fun n => (toDagEdge (p.nodes n).1, toDagEdge (p.nodes n).2)
  root := p.root

theorem ofDag_ofProgram (p : RegisterPath.Program) :
    RMEquiv.ofDag (ofProgram p) p.nnodes = p := by
  cases p with
  | mk nodes root nnodes =>
      have hn : (fun n =>
          (RMEquiv.toPath (toDagEdge (nodes n).1),
           RMEquiv.toPath (toDagEdge (nodes n).2))) = nodes := by
        funext n
        simp only [toPath_toDagEdge]
      change (⟨_, root, nnodes⟩ : RegisterPath.Program) = ⟨nodes, root, nnodes⟩
      dsimp only [ofProgram]
      rw [hn]

def oldDag : RMDag.Prog := ofProgram ProgramRouting245.program
def newDag : RMDag.Prog := ofProgram ProgramRotation244.program

theorem old_program_eq : RMEquiv.ofDag oldDag 203 = ProgramRouting245.program :=
  ofDag_ofProgram ProgramRouting245.program

theorem new_program_eq : RMEquiv.ofDag newDag 203 = ProgramRotation244.program :=
  ofDag_ofProgram ProgramRotation244.program

/- The old height and escape bounds work unchanged except continue bound5.
   The balanced lookup keeps the certificate reduction depth bounded. -/
private def bounds (n : Nat) : Nat × Nat × Nat :=
  if n < 101 then
    if n < 50 then
      if n < 25 then
        if n < 12 then
          if n < 6 then
            if n < 3 then
              if n < 1 then
                (1,1,0)
              else
                if n < 2 then
                  (1,0,2)
                else
                  (2,0,1)
            else
              if n < 4 then
                (3,0,0)
              else
                if n < 5 then
                  (1,0,1)
                else
                  (2,0,0)
          else
            if n < 9 then
              if n < 7 then
                (3,0,0)
              else
                if n < 8 then
                  (4,0,0)
                else
                  (5,0,0)
            else
              if n < 10 then
                (1,1,0)
              else
                if n < 11 then
                  (1,0,1)
                else
                  (2,0,0)
        else
          if n < 18 then
            if n < 15 then
              if n < 13 then
                (3,0,0)
              else
                if n < 14 then
                  (4,0,2)
                else
                  (5,0,1)
            else
              if n < 16 then
                (6,0,0)
              else
                if n < 17 then
                  (1,0,1)
                else
                  (2,0,0)
          else
            if n < 21 then
              if n < 19 then
                (7,0,0)
              else
                if n < 20 then
                  (1,0,1)
                else
                  (2,0,0)
            else
              if n < 23 then
                if n < 22 then
                  (8,0,0)
                else
                  (1,0,1)
              else
                if n < 24 then
                  (2,0,0)
                else
                  (8,0,0)
      else
        if n < 37 then
          if n < 31 then
            if n < 28 then
              if n < 26 then
                (2,0,0)
              else
                if n < 27 then
                  (1,0,1)
                else
                  (2,0,0)
            else
              if n < 29 then
                (2,0,1)
              else
                if n < 30 then
                  (3,0,0)
                else
                  (2,0,0)
          else
            if n < 34 then
              if n < 32 then
                (3,0,0)
              else
                if n < 33 then
                  (4,0,2)
                else
                  (5,0,1)
            else
              if n < 35 then
                (6,0,0)
              else
                if n < 36 then
                  (1,0,1)
                else
                  (2,0,0)
        else
          if n < 43 then
            if n < 40 then
              if n < 38 then
                (7,0,0)
              else
                if n < 39 then
                  (8,0,0)
                else
                  (9,0,0)
            else
              if n < 41 then
                (2,0,1)
              else
                if n < 42 then
                  (3,0,0)
                else
                  (4,0,0)
          else
            if n < 46 then
              if n < 44 then
                (3,0,0)
              else
                if n < 45 then
                  (1,0,1)
                else
                  (2,0,0)
            else
              if n < 48 then
                if n < 47 then
                  (4,0,0)
                else
                  (10,0,0)
              else
                if n < 49 then
                  (11,0,0)
                else
                  (12,0,0)
    else
      if n < 75 then
        if n < 62 then
          if n < 56 then
            if n < 53 then
              if n < 51 then
                (6,0,0)
              else
                if n < 52 then
                  (7,0,0)
                else
                  (1,0,0)
            else
              if n < 54 then
                (2,0,0)
              else
                if n < 55 then
                  (3,0,1)
                else
                  (4,0,0)
          else
            if n < 59 then
              if n < 57 then
                (7,0,0)
              else
                if n < 58 then
                  (8,0,0)
                else
                  (9,0,0)
            else
              if n < 60 then
                (13,0,0)
              else
                if n < 61 then
                  (8,0,0)
                else
                  (3,0,0)
        else
          if n < 68 then
            if n < 65 then
              if n < 63 then
                (4,0,0)
              else
                if n < 64 then
                  (10,0,0)
                else
                  (11,0,0)
            else
              if n < 66 then
                (8,0,0)
              else
                if n < 67 then
                  (9,0,0)
                else
                  (12,0,0)
          else
            if n < 71 then
              if n < 69 then
                (10,0,0)
              else
                if n < 70 then
                  (11,0,0)
                else
                  (13,0,0)
            else
              if n < 73 then
                if n < 72 then
                  (14,0,0)
                else
                  (11,0,0)
              else
                if n < 74 then
                  (12,0,0)
                else
                  (11,0,0)
      else
        if n < 88 then
          if n < 81 then
            if n < 78 then
              if n < 76 then
                (9,0,0)
              else
                if n < 77 then
                  (9,0,0)
                else
                  (11,0,0)
            else
              if n < 79 then
                (12,0,0)
              else
                if n < 80 then
                  (12,0,0)
                else
                  (13,0,0)
          else
            if n < 84 then
              if n < 82 then
                (14,0,0)
              else
                if n < 83 then
                  (15,0,0)
                else
                  (16,0,0)
            else
              if n < 86 then
                if n < 85 then
                  (14,0,0)
                else
                  (11,0,0)
              else
                if n < 87 then
                  (15,0,0)
                else
                  (16,0,0)
        else
          if n < 94 then
            if n < 91 then
              if n < 89 then
                (10,0,0)
              else
                if n < 90 then
                  (11,0,0)
                else
                  (12,0,0)
            else
              if n < 92 then
                (13,0,0)
              else
                if n < 93 then
                  (14,0,0)
                else
                  (15,0,0)
          else
            if n < 97 then
              if n < 95 then
                (13,0,0)
              else
                if n < 96 then
                  (12,0,0)
                else
                  (14,0,0)
            else
              if n < 99 then
                if n < 98 then
                  (10,0,0)
                else
                  (12,0,0)
              else
                if n < 100 then
                  (15,0,0)
                else
                  (16,0,0)
  else
    if n < 152 then
      if n < 126 then
        if n < 113 then
          if n < 107 then
            if n < 104 then
              if n < 102 then
                (17,0,0)
              else
                if n < 103 then
                  (14,0,0)
                else
                  (15,0,0)
            else
              if n < 105 then
                (18,0,0)
              else
                if n < 106 then
                  (19,0,0)
                else
                  (10,0,0)
          else
            if n < 110 then
              if n < 108 then
                (20,0,0)
              else
                if n < 109 then
                  (21,0,0)
                else
                  (22,0,0)
            else
              if n < 111 then
                (23,0,0)
              else
                if n < 112 then
                  (13,0,0)
                else
                  (14,0,0)
        else
          if n < 119 then
            if n < 116 then
              if n < 114 then
                (15,0,0)
              else
                if n < 115 then
                  (16,0,0)
                else
                  (24,0,0)
            else
              if n < 117 then
                (25,0,0)
              else
                if n < 118 then
                  (26,0,0)
                else
                  (14,0,0)
          else
            if n < 122 then
              if n < 120 then
                (12,0,0)
              else
                if n < 121 then
                  (14,0,0)
                else
                  (13,0,0)
            else
              if n < 124 then
                if n < 123 then
                  (12,0,0)
                else
                  (14,0,0)
              else
                if n < 125 then
                  (15,0,0)
                else
                  (16,0,0)
      else
        if n < 139 then
          if n < 132 then
            if n < 129 then
              if n < 127 then
                (12,0,0)
              else
                if n < 128 then
                  (13,0,0)
                else
                  (14,0,0)
            else
              if n < 130 then
                (15,0,0)
              else
                if n < 131 then
                  (16,0,0)
                else
                  (17,0,0)
          else
            if n < 135 then
              if n < 133 then
                (18,0,0)
              else
                if n < 134 then
                  (19,0,0)
                else
                  (27,0,0)
            else
              if n < 137 then
                if n < 136 then
                  (14,0,0)
                else
                  (12,0,0)
              else
                if n < 138 then
                  (13,0,0)
                else
                  (15,0,0)
        else
          if n < 145 then
            if n < 142 then
              if n < 140 then
                (16,0,0)
              else
                if n < 141 then
                  (18,0,0)
                else
                  (19,0,0)
            else
              if n < 143 then
                (28,0,0)
              else
                if n < 144 then
                  (29,0,0)
                else
                  (30,0,0)
          else
            if n < 148 then
              if n < 146 then
                (13,0,0)
              else
                if n < 147 then
                  (14,0,0)
                else
                  (15,0,0)
            else
              if n < 150 then
                if n < 149 then
                  (16,0,0)
                else
                  (17,0,0)
              else
                if n < 151 then
                  (14,0,0)
                else
                  (15,0,0)
    else
      if n < 177 then
        if n < 164 then
          if n < 158 then
            if n < 155 then
              if n < 153 then
                (18,0,0)
              else
                if n < 154 then
                  (31,0,0)
                else
                  (32,0,0)
            else
              if n < 156 then
                (16,0,0)
              else
                if n < 157 then
                  (17,0,0)
                else
                  (33,0,0)
          else
            if n < 161 then
              if n < 159 then
                (34,0,0)
              else
                if n < 160 then
                  (15,0,0)
                else
                  (3,0,0)
            else
              if n < 162 then
                (14,0,0)
              else
                if n < 163 then
                  (15,0,0)
                else
                  (16,0,0)
        else
          if n < 170 then
            if n < 167 then
              if n < 165 then
                (17,0,0)
              else
                if n < 166 then
                  (35,0,0)
                else
                  (36,0,0)
            else
              if n < 168 then
                (37,0,0)
              else
                if n < 169 then
                  (1,0,1)
                else
                  (3,0,0)
          else
            if n < 173 then
              if n < 171 then
                (4,0,1)
              else
                if n < 172 then
                  (5,0,0)
                else
                  (1,0,0)
            else
              if n < 175 then
                if n < 174 then
                  (2,1,0)
                else
                  (3,1,0)
              else
                if n < 176 then
                  (6,1,0)
                else
                  (1,0,0)
      else
        if n < 190 then
          if n < 183 then
            if n < 180 then
              if n < 178 then
                (7,0,0)
              else
                if n < 179 then
                  (2,0,0)
                else
                  (3,0,0)
            else
              if n < 181 then
                (8,0,0)
              else
                if n < 182 then
                  (9,0,0)
                else
                  (38,0,0)
          else
            if n < 186 then
              if n < 184 then
                (39,0,0)
              else
                if n < 185 then
                  (40,1,0)
                else
                  (41,1,0)
            else
              if n < 188 then
                if n < 187 then
                  (7,0,0)
                else
                  (8,0,0)
              else
                if n < 189 then
                  (9,0,0)
                else
                  (10,0,0)
        else
          if n < 196 then
            if n < 193 then
              if n < 191 then
                (42,0,0)
              else
                if n < 192 then
                  (43,1,0)
                else
                  (44,1,0)
            else
              if n < 194 then
                (45,0,0)
              else
                if n < 195 then
                  (46,1,0)
                else
                  (47,1,0)
          else
            if n < 199 then
              if n < 197 then
                (12,0,0)
              else
                if n < 198 then
                  (11,0,0)
                else
                  (13,0,0)
            else
              if n < 201 then
                if n < 200 then
                  (48,0,0)
                else
                  (49,0,0)
              else
                if n < 202 then
                  (50,0,0)
                else
                  (51,0,0)

private def H (n : Nat) : Nat := (bounds n).1
private def B (n : Nat) : Nat := (bounds n).2.1
private def C (n : Nat) : Nat := (bounds n).2.2
private def rotatedC (n : Nat) : Nat := if n = 5 then 1 else C n

private theorem old_wf_check : RMEquiv.wfCheck oldDag 203 H B C = true := by
  decide +kernel

private theorem new_wf_check : RMEquiv.wfCheck newDag 203 H B rotatedC = true := by
  decide +kernel

theorem old_wf : RMEquiv.WF oldDag 203 := RMEquiv.wfCheck_sound old_wf_check
theorem new_wf : RMEquiv.WF newDag 203 := RMEquiv.wfCheck_sound new_wf_check

def safe : RMDag.Edge → Prop
  | .node n => n ≠ 4 ∧ n ≠ 5
  | _ => True

instance (e : RMDag.Edge) : Decidable (safe e) := by
  cases e <;> unfold safe <;> infer_instance

private theorem safe_children_finite :
    ∀ n : Fin 203, n.val ≠ 4 → n.val ≠ 5 → n.val ≠ 6 →
      safe (oldDag.nodes n.val).1 ∧ safe (oldDag.nodes n.val).2 := by
  decide +kernel

theorem replacement : RMDagContextSubstitution.Replacement oldDag newDag safe 6 := by
  constructor
  · intro R R' x
    exact RMDagLoopRotation.run_iff (p := oldDag) (q := newDag)
      (n := 6) (l := 5) (b := 4) (n' := 6) (l' := 5) (src := 6) (dst := 0)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by decide) R R' x
  · intro n hs hn
    change n ≠ 4 ∧ n ≠ 5 at hs
    change (toDagEdge (ProgramRouting245.program.nodes n).1,
        toDagEdge (ProgramRouting245.program.nodes n).2) =
      (toDagEdge (ProgramRotation244.program.nodes n).1,
        toDagEdge (ProgramRotation244.program.nodes n).2)
    rw [ProgramRotation244.nodes_unmodified n hs.2 hn]
  · intro n hs hn
    change n ≠ 4 ∧ n ≠ 5 at hs
    by_cases hlt : n < 203
    · exact safe_children_finite ⟨n, hlt⟩ hs.1 hs.2 hn
    · have he := ProgramRouting245.nodes_default n (Nat.le_of_not_gt hlt)
      change safe (toDagEdge (ProgramRouting245.program.nodes n).1) ∧
        safe (toDagEdge (ProgramRouting245.program.nodes n).2)
      rw [he]
      exact ⟨True.intro, True.intro⟩

theorem iterHalts_iff (R : RMDag.Regs) :
    RMDag.IterHalts oldDag R ↔ RMDag.IterHalts newDag R :=
  RMDagContextSubstitution.iterHalts_iff replacement rfl (by decide) R

theorem program_halts_iff (R : RegisterPath.Registers) :
    RegisterPath.Halts ProgramRotation244.program ⟨[], R⟩ ↔
      RegisterPath.Halts ProgramRouting245.program ⟨[], R⟩ := by
  rw [← new_program_eq, ← old_program_eq]
  exact (RMEquiv.halts_iff_iterHalts new_wf R).trans
    ((iterHalts_iff R).symm.trans (RMEquiv.halts_iff_iterHalts old_wf R).symm)

end SetTheory.BusyBeaver.ZFC.SourceRotation244
