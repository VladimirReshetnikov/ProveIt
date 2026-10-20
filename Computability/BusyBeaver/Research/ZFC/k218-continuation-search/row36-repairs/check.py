"""Own bounded exact first-interface diagnostics; no submitted code imports."""
from pathlib import Path
import json,hashlib,gzip
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs');P=ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-k218';OUT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
T={}
for l in (P/'k218.native.tm').read_text().splitlines():
 if l and not l.startswith('#'):
  q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
S=json.loads((P/'sites218.json').read_text());assert S[0]==['000','CD',8]
boot=json.loads((P/'evidence/blank-startup.json').read_text());seed=boot['first_well_formed_root_pc_frame'];assert seed['logical_registers']==[3,0,0,0,3,0,0,0,0]and seed['head']==-5
PHY=[6,2,0,4,3,7,8,5,1]

def frame(h,ones):
 if not ones or min(ones)!=h-1:return None
 headers=[x for x in ones if x>=h+64]
 if not headers:return None
 header=min(headers)
 if any(h+38<=x<header for x in ones):return None
 vals=[];p=header+1
 while p<=max(ones):
  if p in ones or p+1 not in ones:return None
  p+=1;n=0
  while p in ones:n+=1;p+=1
  vals.append(n-1)
 if len(vals)<10:return None
 bits=''.join('1'if h+i in ones else'0'for i in range(38))
 candidates=[(j,row)for j,row in enumerate(S)if bits.startswith(row[0])]
 if len(candidates)!=1:return None
 j,row=candidates[0]
 if '1'in bits[len(row[0]):]:return None
 return {'head':h,'header':header,'gap':header-h-64,'pc_one_offsets':[i for i,b in enumerate(bits)if b=='1'],'ordinal':j,'site':row,'registers':[vals[x]for x in PHY],'spares':vals[9:]}

def one(t,which,startq,starth,startones):
 q,h,ones=startq,starth,set(startones);trace=[];row36=[]
 for tick in range(1,10001):
  b=int(h in ones);w,d,z=t[q,b]
  if(q,b)==(36,0):row36.append({'tick':tick-1,'head':h,'nearby_ones':[x for x in sorted(ones)if h-10<=x<=h+10]})
  trace.append([q,h,b,w,d,z])
  if w:ones.add(h)
  else:ones.discard(h)
  q,h=z,h+d
  assert q!=254,'unexpected halt'
  if q==84:
   f=frame(h,ones)
   if f is not None:
    f.update({'steps':tick,'row36_0_uses':row36,'end_state':q,'end_one_cells':sorted(ones),'trace_file':which+'.json.gz'})
    with gzip.open(OUT/(which+'.json.gz'),'wt')as out:json.dump(trace,out,separators=(',',':'))
    return f
 raise AssertionError('first full source frame not reached within explicit cap')

core={k:v for k,v in T.items()if k[0]!=301};core.update({(87,0):(0,1,88),(88,0):(0,-1,51),(51,0):(0,1,122)})
assert len(core)==434 and T[36,0]==(0,1,51)
tables={'accepted218':T,'core217':core}
for dest in[6,10]:t=dict(core);t[36,0]=(1,-1,dest);tables[f'core217_boot36to{dest}']=t
records={}
for name,t in tables.items():
 records[name]=one(t,name,84,-5,boot['final_one_cells'])
# Independent source-successor calculation for first CD8-zero: consume nearest left ancestor.
p=S[0][0];at=p.rfind('0');prefix=p[:at];bits=format((int(prefix,2)+1)%(1<<len(prefix)),f'0{len(prefix)}b');target=next(i for i,row in enumerate(S)if(bits+'0'*38).startswith(row[0]));assert target==2 and S[target]==['0100','CD',0]
assert records['accepted218']['ordinal']==records['core217']['ordinal']==target
for name in['core217_boot36to6','core217_boot36to10']:
 assert records[name]['ordinal']!=target and records[name]['row36_0_uses']
 # Inspect the subsequent CB1 boundary too, without a whole runtime/search.
 f=records[name];records[name+'_following']=one(tables[name],name+'_following',84,f['head'],f['end_one_cells'])
result={'status':'ACTUALLY_REACHABLE_FIRST_SOURCE_INTERFACE_COUNTEREXAMPLES','scope':'Exact first source interface from the accepted initialized frame. This refutes exclusion of CD8-zero by source reachability and the unchanged per-primitive contract for these two row36 repairs. It is not a complete impossibility result for a redesigned source/runtime relation.','inputs':{str(p):sha(p)for p in[P/'k218.native.tm',P/'sites218.json',P/'evidence/blank-startup.json',Path(__file__)]},'initial_state':84,'initial_head':-5,'initial_one_cells':boot['final_one_cells'],'source_first_instruction':S[0],'initial_R8':0,'required_next_ordinal':target,'required_next_site':S[target],'tables':{name:{'working_states':len(t)//2,'row36_0':t[36,0]}for name,t in tables.items()},'records':records}
(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n')
for name,f in records.items():print(name,{k:v for k,v in f.items()if k not in['end_one_cells','spares']},'spares',len(f['spares']))
