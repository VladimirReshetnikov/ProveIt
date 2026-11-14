import re
import sys
from pathlib import Path
if len(sys.argv) != 2:
 raise SystemExit('usage: generate.py OUTPUT_DIRECTORY')
p=Path(sys.argv[1])
p.mkdir(parents=True, exist_ok=True)
source=Path('Computability/BusyBeaver/Research/PA/pa194-ax-source/PA194AXSource.lean').read_text()
match=re.search(r'def tokens : List Token := \[(.*?)\]',source,re.S)
if not match: raise SystemExit('token list not found')
toks=re.findall(r'\.([A-Za-z]+)',match.group(1))
assert len(toks)==190 and toks[-3:]==['copyGuard','compareGuard','close']
mapping={'push':['push'],'copyD':['push','copyD'],'copyH':['push','copyH'],'copyA':['push','copyA'],'cons':['cons'],'incT':['incT'],'readH':['readH'],'readDCons':['readD','push','copyD','cons']}
ops=sum((mapping[t] for t in toks[:187]),[])
width={'push':19,'copyD':7,'copyH':7,'copyA':7,'cons':27,'incT':1,'readH':14,'readD':14}
start=50; blocks=[]
for op in ops:
 i=start; j=i+width[op]; start=j
 def bound(suffix,typ):
  return f'private theorem bound{i}{suffix} : {typ} := by\n  unfold {typ.split(" sites")[0]}\n  simp only [PA194SourceProgram.resolve_tree]\n  decide +kernel\n'
 if op=='push':
  code=bound('p',f'AXPushParam.Bound sites {i-25}')+f'theorem block{i} : AXMacro.Realizes sites .push {i} {j} := AXMacro.push_realizes bound{i}p\n'
 elif op=='cons':
  code=(bound('u',f'UnpairPartial.Bound sites {i}')+bound('p',f'AXPair.Bound sites {i-20}')+bound('t',f'AXTimes4.Bound sites {i+21}')+f'theorem block{i} : AXMacro.Realizes sites .cons {i} {j} := AXMacro.cons_realizes bound{i}u bound{i}p bound{i}t\n')
 elif op.startswith('copy'):
  r={'copyA':3,'copyD':4,'copyH':5}[op]
  code=bound('c',f'CopyToT.Bound sites {r} {i}')+f'theorem block{i} : AXMacro.Realizes sites .{op} {i} {j} := AXMacro.{op}_realizes bound{i}c\n'
 elif op in ('readH','readD'):
  code=bound('r',f'Readers.Bound sites (AXMacro.reader{op[-1]} {i})')+f'theorem block{i} : AXMacro.Realizes sites .{op} {i} {j} := Readers.{op}_realizes {i} bound{i}r\n'
 else:
  code=f'private theorem bound{i} : resolveAt sites {i} = some (.inc 1 (some {j})) := by\n  rw [PA194SourceProgram.resolve_tree]\n  decide +kernel\ntheorem block{i} : AXMacro.Realizes sites .incT {i} {j} := AXMacro.inc_realizes bound{i}\n'
 blocks.append((i,j,op,code))
assert len(blocks)==251 and start==3519
header='''import PA194SourceProgram\nimport M6.Source.AXMacroPlan\nimport PA196.Source.Readers\nset_option autoImplicit false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace PA194AXPlan\nopen M6.Source PA194SourceProgram PA196.Source\n'''
for n in range(0,len(blocks),10):
 batch=blocks[n:n+10]
 (p/f'PA194AXBatch{n:03}.lean').write_text(header+'\n'.join(x[3] for x in batch)+'end PA194AXPlan\n')
(p/'block-data.txt').write_text('\n'.join(f'{i} {j} {op}' for i,j,op,_ in blocks))

imports='\n'.join('import '+x.stem for x in sorted(p.glob('PA194AXBatch*.lean')))
ops_text=', '.join('.'+op for _,_,op,_ in blocks)
proof='(AXMacro.Plan.nil 3519)'
for i,j,op,_ in reversed(blocks):
 proof=f'(AXMacro.Plan.cons block{i} {proof})'
aggregate=f"""{imports}
import PA194AXSymbolic
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194AXPlan
open M6.Source PA194SourceProgram PA194AXSymbolic PA196.Commands.Code

theorem source_plan : AXMacro.Plan sites 50 3519 core := by
  change AXMacro.Plan sites 50 3519 [{ops_text}]
  exact {proof}

theorem source_core (t c d h y x tail bottom : Nat) (f : Registers) :
    ∃ n, Steps sites n
      (AXMacro.configAt 50 ⟨t,c,d,h,Cantor.pair y (Cantor.pair x tail),[]⟩ bottom f)
      (AXMacro.configAt 3519
        ⟨oldBundle (h+y) (d+x) c,c,d+x,h+y,tail,
          [diagonal c] ++ heads (d+x) (h+y) c d h ++ [t]⟩ bottom f) :=
  AXMacro.Plan.sound source_plan _ _ (macro_result t c d h y x tail) bottom f

#print axioms source_plan
#print axioms source_core
end PA194AXPlan
"""
(p/'PA194AXPlan.lean').write_text(aggregate)
