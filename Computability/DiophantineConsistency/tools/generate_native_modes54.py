from pathlib import Path
import argparse,hashlib,json,itertools
args=argparse.ArgumentParser()
args.add_argument('--check',action='store_true')
args=args.parse_args()
root=Path(__file__).resolve().parents[3]
src=root/'Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/coefficients/k215_transitions.json'
if hashlib.sha256(src.read_bytes()).hexdigest()!='880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755':
    raise ValueError('Pinned transition JSON changed')
actions=json.loads(src.read_text())['transitions']
tiles=set()
for state,bit,write,direction,next_state in actions:
    head=512+2*state+bit
    if direction==1:tiles.add((0,head,256+next_state,write))
    elif direction==-1:tiles.add((512+next_state,head,0,write))
    else:raise ValueError(direction)
for bit in [0,1]:
    tiles.add((0,942+bit,0,942+bit));tiles.add((0,bit,0,bit))
for top in [0,1,942,943]:tiles.add((0,top,0,6))
tiles.update([(2,2,2,0),(2,3,3,1),(3,4,4,698),(4,4,4,0)])
for bottom in [2,3,4]:tiles.add((1,6,1,bottom))
for west,east in itertools.product([0,1,4],[0,1,2]):tiles.add((west,5,east,5))
start,forbidden=(2,3,3,1),(5,0,0,0)
right,left=(256,0,0,512),(0,0,512,512)
tiles.update([forbidden,right,left])
modes=[start,forbidden]+sorted(tiles-{start,forbidden})
if len(modes)!=457:
    raise ValueError('Expected 457 modes')
lines=[]
for t in modes:
    kind='rightReceiver' if t==right else 'leftReceiver' if t==left else 'ordinary'
    lines.append(f'  (⟨{t[0]},{t[1]},{t[2]},{t[3]}⟩,.{kind})')
header='''import DiophantineConsistency.NativeClauseModes54

/-!
# The literal compact54 selector modes

Generated from the inert 430-transition JSON SHA256
880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755,
using the compact54 declarative families and ordering. This finite binding
is separate from a Lean theorem interpreting these labels as K215 runs.
-/

namespace DiophantineConsistency.NativeModesData54

open NativeClauseModes54

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def modeList : List (Label × Kind) := [
'''
footer='''
]

theorem modeList_length : modeList.length = 457 := by decide

private def checkMode (p : Label × Kind) : Bool :=
  match p.2 with
  | .ordinary => decide (p.1.west < 1024 ∧ p.1.north < 1024 ∧ p.1.east < 1024 ∧ p.1.south < 1024)
  | .rightReceiver => decide (p.1 = rightLabel)
  | .leftReceiver => decide (p.1 = leftLabel)

private theorem checkMode_iff (p : Label × Kind) : checkMode p = true ↔ ValidMode p.2 p.1 := by
  obtain ⟨t,k⟩ := p
  cases k with
  | ordinary =>
    simp only [checkMode,decide_eq_true_eq,ValidMode]
    constructor
    · rintro ⟨hw,hn,he,hs⟩
      exact ⟨hw,hn,he,hs⟩
    · intro h
      exact ⟨h.west_lt,h.north_lt,h.east_lt,h.south_lt⟩
  | rightReceiver => simp [checkMode,ValidMode]
  | leftReceiver => simp [checkMode,ValidMode]

private theorem all_valid : modeList.all checkMode = true := by decide

def mode (i : Fin 457) : Label × Kind :=
  modeList[i.val]'(by rw [modeList_length]; exact i.isLt)

theorem mode_mem (i : Fin 457) : mode i ∈ modeList := by
  unfold mode
  exact List.getElem_mem _

theorem mode_valid (i : Fin 457) : ValidMode (mode i).2 (mode i).1 := by
  exact (checkMode_iff (mode i)).mp ((List.all_eq_true.mp all_valid) _ (mode_mem i))

theorem mode_zero : mode 0 = (⟨2,3,3,1⟩,.ordinary) := by decide

theorem mode_one : mode 1 = (⟨5,0,0,0⟩,.ordinary) := by decide

'''
footer+=f'theorem right_mode : mode {modes.index(right)} = (rightLabel,.rightReceiver) := by decide\n\n'
footer+=f'theorem left_mode : mode {modes.index(left)} = (leftLabel,.leftReceiver) := by decide\n\n'
footer+='end DiophantineConsistency.NativeModesData54\n'
p=root/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeModesData54.lean'
result=header+',\n'.join(lines)+footer
if args.check:
    if p.read_text()!=result:
        raise ValueError('Generated Lean mode data differs')
else:
    p.write_text(result)
print({'modes':len(modes),'right_index':modes.index(right),'left_index':modes.index(left),'file':str(p)})
