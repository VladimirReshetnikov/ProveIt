from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parent
AX=ROOT
sys.path.insert(0,str(AX));sys.path.insert(0,str(AX/'search'))
import compiler as c
from support import bestcompatible_all,apply,localvalid,encode
orig_raw=c.raw_nodes
orig_machine=c.machine
base,labels=orig_machine()
# Imported Combined196 physical edits, converted by the pinned conjugacy.
dense_edits={(115,1):(1,True,108),(37,0):(0,True,11),(37,1):(1,True,101),(127,0):(0,True,133),(127,1):(1,True,20),(133,0):(0,True,120)}
edits={(labels[q],b):(w,d,labels[n])for(q,b),(w,d,n)in dense_edits.items()}

def patched_machine():
 rows,lab=orig_machine();rows.update(edits);return rows,lab

def patched_raw():
 ns=orig_raw();ns['node163']=('node6','node147');ns['node170']=(('node36',('node167','node145')),'node57');return ns

c.machine=patched_machine
c.raw_nodes=patched_raw
pair=(('leaf','inc',1),('leaf','inc',1));c.MACROS[pair]=99;c.MACROS[(pair,pair)]=190

def table_text(rows):return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'for(q,b),(w,d,n)in sorted(rows.items()))

def startup(rows,path,bound=100000):
 head=-2;physical=[0,0,0,0,0,0,2,0,0]+[1]*26;expected={head-1,head+48}|{head+i for i,b in enumerate(path)if b};pos=head+49
 for v in physical:pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
 tape=set();q=74;h=0
 for step in range(1,bound+1):
  w,d,q=rows[q,int(h in tape)];(tape.add if w else tape.discard)(h);h+=1 if d else -1
  if q==84 and h==head and tape==expected:return step
  if q==254:return {'halt':step}
 return None

def run(family):
 p=AX/family;t=c.read_grammar(p/'grammar.json');rows,idx,sh=c.build(t)
 chosen=bestcompatible_all(rows,sh);folded,alias=apply(rows,chosen)
 assert localvalid(rows,folded,alias,chosen)
 sites,ins,cs=c.source(t)
 print(family,'prepared',len(rows)//2,len(folded)//2,len(sites),flush=True)
 val=c.validate(folded,cs)
 st=startup(folded,sites[25][0])
 out=ROOT/family;out.mkdir(exist_ok=True)
 (out/'machine.native.tm').write_text(table_text(folded));(out/'grammar.json').write_text(json.dumps(encode(t),indent=2)+'\n')
 (out/'folds.json').write_text(json.dumps(chosen,indent=2)+'\n');(out/'sites.json').write_text(json.dumps([[''.join(map(str,p)),op,a]for p,op,a in sites])+'\n')
 rec={'family':family,'working_states':len(folded)//2,'raw_working_states':len(rows)//2,'source_sites':len(sites),'folds':len(chosen),'validation':val,'startup_steps':st,'edits':[[q,b,*v]for(q,b),v in sorted(edits.items())],'sha256':hashlib.sha256(table_text(folded).encode()).hexdigest()}
 (out/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)
if __name__=='__main__':
 for x in ('diagonal196','separate196'):run(x)
