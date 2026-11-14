#!/usr/bin/env python3
"""Literal complete-tape checker, independent of the optimizing compiler."""
from pathlib import Path
import sys,json,hashlib,time
PACKAGE=Path(__file__).resolve().parent.parent
BASE=Path(__file__).resolve().parent/'reference'
sys.path.insert(0,str(BASE))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source
sym.HEADER_BASE=48
PHY=(6,2,0,4,3,7,8,5,1)
if not __debug__:raise RuntimeError('Assertions required')
def sha(data):return hashlib.sha256(data).hexdigest()
def read(path,halt,count):
 rows={}
 for ln in path.read_text().splitlines():
  q,b,w,d,t=ln.split();q,b,w,t=map(int,(q,b,w,t))
  assert b in(0,1) and w in(0,1) and d in('L','R') and(q,b)not in rows
  rows[q,b]=(w,1 if d=='R'else-1,t)
 states={q for q,b in rows}
 assert len(states)==count and halt not in states
 assert set(rows)=={(q,b)for q in states for b in(0,1)}
 assert {t for w,d,t in rows.values()}-states=={halt}
 return rows,states

def main(folder):
 root=PACKAGE/'machine';out=PACKAGE/'evidence/independent';out.mkdir(exist_ok=True)
 rec=json.loads((PACKAGE/'evidence/construction.json').read_text());count=rec['states'];steps=rec['seed']['steps']
 table,states=read(root/'pa194q.native.tm',254,count)
 dense,ds=read(root/'pa194q.tm',count,count);assert ds==set(range(count))
 labels=json.loads((root/'labels.json').read_text())
 assert len(labels)==count+1 and len(set(labels))==count+1 and labels[0]==74 and labels[-1]==254
 assert {(labels[q],b):(w,d,labels[t])for(q,b),(w,d,t)in dense.items()}==table
 seen={74};reach=[74]
 for q in reach:
  for b in(0,1):
   t=table[q,b][2]
   if t!=254 and t not in seen:seen.add(t);reach.append(t)
 assert reach+[254]==labels
 sites=json.loads((root/'sites.json').read_text())
 opmap={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
 mapped=[[p,opmap[op],a]for p,op,a in sites]
 graph,_=source.graph_arithmetic(mapped);assert graph==source.graph_intervals(mapped)
 names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
 ins=[[names[e[0]]]+e[1:]+targets for e,targets in graph]
 assert ins==json.loads((root/'instructions.json').read_text())
 assert max(len(p)for p,op,a in sites)<=48
 mapping={int(k):v for k,v in json.loads((BASE/'legacy_mapping.json').read_text()).items()}
 for q in states|{254}:mapping.setdefault(q,q+10000)
 assert len({mapping[q]for q in states|{254}})==count+1
 assert mapping[84]==96 and mapping[254]==254
 symbolic={(mapping[q],b):(w,d,mapping[t])for(q,b),(w,d,t)in table.items()}
 runtime.PHY=PHY
 lemmas,blocks=sym.prove_blocks(symbolic);assert len(blocks)==4
 contracts=[];total=maximum=0
 for i,site in enumerate(mapped):
  for positive in([False,True]if site[1]=='CD'else[False]):
   r=sym.case(symbolic,lemmas,site,positive)
   total+=r['symbolic_steps'];maximum=max(maximum,r['symbolic_steps'])
   contracts.append({'site':i,'positive':positive,'duration':r['duration'],'motion':r['motion'],'symbolic_steps':r['symbolic_steps']})
  if(i+1)%500==0:print('checked source sites',i+1,flush=True)
 assert len(contracts)==rec['contracts']
 # Independent finite blank execution and equality of every tape cell.
 tape=bytearray(20000);origin=10000;head=origin;q=74
 for step in range(steps):
  assert q!=254 and 0<=head<len(tape)
  w,d,q=table[q,tape[head]];tape[head]=w;head+=d
 assert q==84 and head-origin==-2
 path=sites[25][0];frame=bytearray([1]+[int(b)for b in path]+[0]*(48-len(path))+[1])
 logical=[2]+[0]*8;physical=[None]*9
 for i,j in enumerate(PHY):physical[j]=logical[i]
 for v in physical+[1]*26:frame.extend([0]+[1]*(v+1))
 expected=bytearray(len(tape));a=head-1;expected[a:a+len(frame)]=frame;assert tape==expected
 enc=(json.dumps(contracts,separators=(',',':'))+'\n').encode();(out/'contracts.json').write_bytes(enc)
 (out/'list_lemmas.json').write_text(json.dumps(blocks,indent=2)+'\n')
 min_duration=min(c['duration'][0]for c in contracts);assert min_duration>0
 r={'status':'PASS','states':count,'transition_rows':2*count,'sha256':sha((root/'pa194q.tm').read_bytes()),
 'source_sites':len(sites),'universal_source_outcomes':len(contracts),'independent_resolvers_agree':True,
 'dense_conjugacy_exact':True,'symbolic_steps':total,'maximum_symbolic_steps':maximum,
 'minimum_positive_duration_constant':min_duration,'four_list_lemmas_rederived_from_literal_table':True,
 'arithmetic_box_oracles':False,'register_scope':'nine arbitrary naturals and both decrement branches',
 'spare_scope':'arbitrary finite nonempty list of arbitrary natural values','startup_steps':steps,
 'complete_blank_tape_equal':True,'contracts_sha256':sha(enc),'kernel_checked':False}
 (out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2),flush=True)
if __name__=='__main__':main(PACKAGE)
