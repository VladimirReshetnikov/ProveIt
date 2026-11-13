#!/usr/bin/env python3
"""Create source snapshots only; no Lean invocation."""
import hashlib,json,re,shutil,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];source=D/'research/nine-sharing-norm38-slot-extraction-draft/Norm38SlotExtraction.lean'; seed=D/'research/nine-sharing-quartic65-norm38-candidate/seed.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(source)=='7afacc8c1f2b9b0e1b443f346653c21dde511fe200e8296daf2ec2afd4ea38fc' and sha(seed)=='312ab65ec472f01339c41dab93859e368ec0b9a2213b906856526263dd68eb23'
s=source.read_text(); data=json.loads(seed.read_text());chunks=re.findall(r'^/-- Slot \d+:.*?(?=^/-- Slot \d+:|^/-- The sum-of-squares)',s,re.M|re.S);assert len(chunks)==len(data['residuals'])==29
src=P/'src/DiophantineConsistency';src.mkdir(parents=True,exist_ok=True);head=s[:s.index('/-- Slot 0:')];end='\nend DiophantineConsistency.Norm38SlotExtraction\n';(src/'Norm38SlotsBase.lean').write_text(head+end)
header='''import DiophantineConsistency.Norm38SlotsBase
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

'''
def indices(t):
 if t[0]=='var':return {t[1]}
 if t[0] in ('num','port'):return set()
 return indices(t[1])|indices(t[2])
for group in range(10):
 output=header
 for i in range(3*group,min(3*group+3,29)):
  body=chunks[i]; ids=sorted(indices(data['residuals'][i]['expr'])); assert 0 not in ids and all(1<=x<=38 for x in ids)
  have=''
  for n in ids:
   have+=f'''  have h{n:02d} : (Fin.cons (1 : V) w : Fin 39 → V) {n} = w {n-1} := by
    have hindex : ({n-1} : Fin 38).succ = ({n} : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w ({n-1} : Fin 38)
'''
  assert body.count(':= by\n  simp [residualAt')==1
  body=body.replace(':= by\n  simp [residualAt',':= by\n'+have+'  simp [residualAt',1)
  marker='Expr.evalRing_constant, hp, map_add, map_mul] <;> ring';assert body.count(marker)==1
  body=body.replace(marker,'Expr.evalRing_constant, hp, map_add, map_mul, '+', '.join(f'h{n:02d}' for n in ids)+'] <;> ring')
  output+=body
 (src/f'Norm38Slots{group:02d}.lean').write_text(output+end)
assembly=s[s.index('/-- The sum-of-squares theorem'):s.rindex('end DiophantineConsistency.Norm38SlotExtraction')]
imports=''.join(f'import DiophantineConsistency.Norm38Slots{i:02d}\n' for i in range(10))
(src/'Norm38SlotsAssembly.lean').write_text(imports+header.split('\n',1)[1]+assembly+end)
names=['Norm38SlotsBase']+[f'Norm38Slots{i:02d}' for i in range(10)]+['Norm38SlotsAssembly'];rows=[]
for name in names:
 p=src/(name+'.lean');rows.append({'module':'DiophantineConsistency.'+name,'source':'Computability/DiophantineConsistency/'+str(p.relative_to(D)),'source_sha256':sha(p),'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',p.read_text(),re.M)})
man=P/'source-manifest.json';man.write_text(json.dumps({'rows':rows},indent=2)+'\n')
old=(D/'research/nine-sharing-norm38-slot-extraction-check/run.py').read_text();old=old.replace('/tmp/nine-sharing-norm38-slot-check-20261105','/tmp/nine-sharing-norm38-slots-batched-20261105').replace('4936a8eaa5b3b0fdc03f825dcbdf5fb6621e4dff8d88f7547d441dde8238d32f',sha(man)).replace('single-module unverified norm38 slot-extraction experiment','twelve-module batched norm38 slot experiment').replace('PASS norm38 slot-extraction check','PASS batched norm38 slot check');(P/'run.py').write_text(old)
print(json.dumps({'status':'SOURCE_GENERATED_ONLY','slots':29,'groups':10,'stages':len(rows),'manifest_sha256':sha(man),'runner_sha256':sha(P/'run.py')},indent=2,sort_keys=True))
