from pathlib import Path
import hashlib,json
B=Path(__file__).resolve().parent
T=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-prefix246/zfc_prefix246.tm')
assert hashlib.sha256(T.read_bytes()).hexdigest()=='89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc'
rows={}
for line in T.read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,t=line.split();rows[int(q),int(b)]=int(w),d,int(t)
assert len(rows)==500
start_at=410735-16384; end_at=410735
q=h=0;left=[];right=[];ones=set();saved={};maxleft=maxright=0
for elapsed in range(1,end_at+1):
 b=right[0] if right else 0
 assert b==int(h in ones)
 w,d,q=rows[q,b]; assert q!=246
 if w:ones.add(h)
 else:ones.discard(h)
 if d=='R':left,right,h=[w]+left,right[1:],h+1
 else:right,left,h=[left[0] if left else 0,w]+right[1:],left[1:],h-1
 maxleft=max(maxleft,len(left));maxright=max(maxright,len(right))
 if elapsed in [1024,start_at,end_at]:
  expected={h-i-1 for i,b in enumerate(left) if b}|{h+i for i,b in enumerate(right) if b}
  assert expected==ones
  saved[elapsed]=dict(state=q,head=h,left=left.copy(),right=right.copy(),ones=sorted(ones))
def bits(xs):
 groups=['['+', '.join('true' if x else 'false' for x in xs[i:i+96])+']' for i in range(0,len(xs),96)]
 return ' ++\n      '.join(groups) if groups else '[]'
def conf(name,z):return f'''def {name} : ZipConfig 246 :=
  {{ state := some ⟨{z['state']}, by decide⟩, head := {z['head']},
    left := {bits(z['left'])},
    right := {bits(z['right'])} }}
'''
s='''import BusyBeaver.ZFC.FastTablePrefix246
import BusyBeaver.ZFC.FiniteZipper

/-!
A local 16384-step exact246 calculation on a long generated tape.
The input data were generated from putative blank-run steps394351 and410735,
but this module proves only the transition from the explicit start tape to
the explicit finish tape. No assertion identifies start with the actual blank
run. This bounded experiment selects a practical chunk size under default
proof limits; complete blank-start composition remains separate.
-/
namespace SetTheory.BusyBeaver.ZFC.BootPrefix246Probe16384
open FiniteZipper FastTablePrefix246

'''+conf('start',saved[start_at])+'\n'+conf('finish',saved[end_at])+'''
theorem local16384 : zipBlock fastMachine 14 start = finish := by decide +kernel

theorem transfer16384 {c : Config 246} (h : ZipRep c start) :
    ZipRep (machinePrefix246.runFrom c 16384) finish := by
  have hs := zipBlock_sound fastMachine 14 h
  rw [local16384, fastMachine_eq] at hs
  exact hs

end SetTheory.BusyBeaver.ZFC.BootPrefix246Probe16384
'''
(B/'BootPrefix246Probe16384.lean').write_text(s)
record=dict(status='UNTRUSTED_GENERATED_LOCAL_INPUTS',canonical_sha256=hashlib.sha256(T.read_bytes()).hexdigest(),start_generation_step=start_at,finish_generation_step=end_at,local_steps=16384,maximum_left_length=maxleft,maximum_right_length=maxright,checkpoints=saved,full_blank_start_proof=False)
(B/'data.json').write_text(json.dumps(record,indent=2)+'\n')
for n,z in saved.items():print(n,z['state'],z['head'],len(z['left']),len(z['right']),len(z['ones']))
print('source',hashlib.sha256(s.encode()).hexdigest(),'bytes',len(s))
