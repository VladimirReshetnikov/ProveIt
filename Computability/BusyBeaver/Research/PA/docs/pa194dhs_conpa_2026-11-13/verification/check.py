#!/usr/bin/env python3
"""Independent literal-tape and source-splice verification of PA194DHS.
No construction compiler, no arithmetic-box oracle, and no bounded run
assumption enters the universal source-outcome contracts.
"""
from pathlib import Path
import sys,json,hashlib,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'verification/reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source
PHY=(6,2,0,4,3,7,8,5,1)
def sha(x):return hashlib.sha256(x).hexdigest()
def read(path):
 rows={}
 for ln in path.read_text().splitlines():
  q,b,w,d,t=ln.split();q,b,w,t=map(int,(q,b,w,t));assert(q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R');rows[q,b]=w,1 if d=='R'else-1,t
 return rows

def main():
 if not __debug__:raise RuntimeError('Run verification without Python -O')
 start=time.monotonic();M=ROOT/'machine';E=ROOT/'evidence';inp=ROOT/'inputs'
 rows=read(M/'machine.native.tm');states={q for q,_ in rows};assert len(states)==194 and len(rows)==388
 assert set(rows)=={(q,b)for q in states for b in(0,1)}and {t for w,d,t in rows.values()}-states=={254}
 labels=json.loads((M/'labels.json').read_text());dense=read(M/'machine.tm')
 assert labels[0]==74 and labels[-1]==254 and len(set(labels))==195
 assert{(labels[q],b):(w,d,labels[t])for(q,b),(w,d,t)in dense.items()}==rows
 # Reconstruct source independently from the pinned Gamma-D cached source.
 old=json.loads((inp/'pa194d.sites.json').read_text());p='1001010111'
 before=[[p+'0','dec',4],[p+'10','inc',5],[p+'11','continueTo',2]]
 assert [s for s in old if s[0].startswith(p)]==before
 patch=[['00','dec',4],['010','inc',1],['0110','inc',6],['0111','continueTo',3],['10','dec',6],['110','inc',4],['111','continueTo',2]]
 at=old.index(before[0]);sites=old[:at]+[[p+x,op,a]for x,op,a in patch]+old[at+3:]
 p='101';before=[['00','dec',5],['010','inc',1],['0110','inc',6],['0111','continueTo',3],['10','dec',6],['110','inc',5],['111','continueTo',2]]
 assert [s for s in sites if s[0].startswith(p)]==[[p+x,op,a]for x,op,a in before]
 at=next(i for i,s in enumerate(sites)if s[0].startswith(p))
 patch=[['0','dec',5],['10','inc',1],['110','inc',6],['111','continueTo',3]]
 sites=sites[:at]+[[p+x,op,a]for x,op,a in patch]+sites[at+7:]
 i=next(i for i,s in enumerate(sites)if s[0]=='110');assert sites[i]==['110','inc',6];sites[i]=['110','inc',5]
 assert sites==json.loads((M/'sites.json').read_text())and len(sites)==3650
 opcode={'inc':'CI','dec':'CD','continueTo':'CC','breakTo':'CB','halt':'CH'}
 mapped=[[p,opcode[op],a]for p,op,a in sites];graph,_=source.graph_arithmetic(mapped);assert graph==source.graph_intervals(mapped)
 names={'increment':'inc','decrement':'dec','identity':'jump','halt':'halt'}
 code=[[names[e[0]]]+e[1:]+ts for e,ts in graph];assert code==json.loads((M/'instructions.json').read_text())
 mapping={int(k):v for k,v in json.loads((ROOT/'verification/reference/legacy_mapping.json').read_text()).items()}
 for q in states|{254}:mapping.setdefault(q,q+10000)
 assert len({mapping[q]for q in states|{254}})==195 and mapping[84]==96 and mapping[254]==254
 table={(mapping[q],b):(w,d,mapping[t])for(q,b),(w,d,t)in rows.items()};runtime.PHY=PHY;sym.HEADER_BASE=48
 lemmas,blocks=sym.prove_blocks(table);assert len(blocks)==4
 contracts=[];total=maximum=0
 for i,site in enumerate(mapped):
  for positive in([False,True]if site[1]=='CD'else[False]):
   z=sym.case(table,lemmas,site,positive);total+=z['symbolic_steps'];maximum=max(maximum,z['symbolic_steps']);contracts.append({'site':i,'positive':positive,**{k:z[k]for k in('duration','motion','symbolic_steps')}})
  if(i+1)%500==0:print('Checked',i+1,'source sites',flush=True)
 assert len(contracts)==4752
 # Independent bytearray whole-tape seed check at the claimed exact time.
 seed=json.loads((E/'seed.json').read_text());assert seed['steps']==58014
 tape=bytearray(20000);origin=10000;head=origin;q=74
 for k in range(58014):
  assert q!=254 and 0<=head<len(tape)
  w,d,q=rows[q,tape[head]];tape[head]=w;head+=d
 assert(q,head-origin)==(84,-2)
 path=sites[25][0];frame=bytearray([1]+[int(x)for x in path]+[0]*(48-len(path))+[1])
 logical=[2]+[0]*8;physical=[None]*9
 for i,j in enumerate(PHY):physical[j]=logical[i]
 for v in physical+[1]*26:frame.extend([0]+[1]*(v+1))
 want=bytearray(len(tape));want[head-1:head-1+len(frame)]=frame;assert tape==want
 enc=(json.dumps(contracts,separators=(',',':'))+'\n').encode();(E/'independent_contracts.json').write_bytes(enc)
 receipt={'status':'PASS','source_sites':len(sites),'source_outcomes':len(contracts),'independent_source_splice_from_D':True,'two_CFG_resolvers_agree':True,'arithmetic_box_oracle':False,'list_lemmas':len(blocks),'symbolic_steps':total,'maximum_symbolic_steps':maximum,'minimum_duration_constant':min(x['duration'][0]for x in contracts),'whole_blank_tape_equality':True,'startup_steps':58014,'dense_sha256':sha((M/'machine.tm').read_bytes()),'native_sha256':sha((M/'machine.native.tm').read_bytes()),'contracts_sha256':sha(enc),'kernel_checked':False,'seconds':round(time.monotonic()-start,3)}
 for name,obj in [('independent_receipt.json',receipt),('independent_list_lemmas.json',blocks)]:(E/name).write_text(json.dumps(obj,indent=2)+'\n')
 print(json.dumps(receipt,indent=2),flush=True)
 return receipt
if __name__=='__main__':main()
