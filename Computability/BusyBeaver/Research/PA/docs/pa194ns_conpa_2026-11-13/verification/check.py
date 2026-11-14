#!/usr/bin/env python3
"""Independent literal-tape audit for PA194NS.

No construction compiler or arithmetic-box oracle is imported. Reconstructs
both source and table from pinned PA194CS inputs using separate edits, checks
two CFG resolvers, derives list lemmas from literal rows, executes all symbolic
source outcomes, and compares the whole blank-start tape with its exact seed.
"""
from pathlib import Path
import argparse,hashlib,json,sys,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(Path(__file__).resolve().parent/'reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source
PHY=(6,2,0,4,3,7,8,5,1)
sha=lambda b:hashlib.sha256(b).hexdigest()

def read(path):
 rows={}
 for line in path.read_text().splitlines():
  q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t));assert (q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R');rows[q,b]=w,1 if d=='R' else -1,t
 states={q for q,b in rows};assert len(states)==194 and len(rows)==388
 assert set(rows)=={(q,b) for q in states for b in (0,1)}
 assert {t for w,d,t in rows.values()}-states=={254}
 return rows,states

def format_table(rows):return ''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n' for (q,b),(w,d,t) in sorted(rows.items()))

def run(out):
 assert __debug__,'Run without -O'
 started=time.monotonic();out.mkdir(parents=True,exist_ok=True)
 inp=ROOT/'inputs'
 assert sha((inp/'pa194CS.native.tm').read_bytes())=='00446d08d3c35909a11460a9e19507d53e8526ad822b94ce9a04c73951eb447b'
 assert sha((inp/'pa194CS.instructions.json').read_bytes())=='e2f74c0fad95734738788b98e76dc3e11748c0819ad7ef2b2998f81e0140da87'
 rows,states=read(inp/'pa194CS.native.tm');assert rows[164,1]==(1,1,130);rows[164,1]=1,1,114
 assert format_table(rows)==(ROOT/'machine/machine.native.tm').read_text()
 order=[74];seen={74}
 for q in order:
  for b in (0,1):
   t=rows[q,b][2]
   if t!=254 and t not in seen:seen.add(t);order.append(t)
 assert seen==states;order.append(254);inverse={q:i for i,q in enumerate(order)}
 dense={(inverse[q],b):(w,d,inverse[t]) for (q,b),(w,d,t) in rows.items()}
 assert format_table(dense)==(ROOT/'machine/machine.tm').read_text()
 assert order==json.loads((ROOT/'machine/labels.json').read_text())

 # Source splice is specified independently by address, without tree compiler.
 old=json.loads((inp/'pa194CS.sites.json').read_text());prefix='1001010111'
 before=[row for row in old if row[0].startswith(prefix)]
 assert before==[[prefix+'0','dec',4],[prefix+'10','inc',5],[prefix+'11','continueTo',2]]
 patch=[['00','dec',4],['010','inc',1],['0110','inc',6],['0111','continueTo',3],['10','dec',6],['110','inc',4],['111','continueTo',2]]
 at=old.index(before[0]);assert at==3634
 sites=old[:at]+[[prefix+p,op,a] for p,op,a in patch]+old[at+3:]
 assert len(sites)==3650 and sites==json.loads((ROOT/'machine/sites.json').read_text())
 opcode={'inc':'CI','dec':'CD','continueTo':'CC','breakTo':'CB','halt':'CH'}
 mapped=[[p,opcode[op],a] for p,op,a in sites]
 graph,_=source.graph_arithmetic(mapped);assert graph==source.graph_intervals(mapped)
 names={'increment':'inc','decrement':'dec','identity':'jump','halt':'halt'}
 code=[[names[e[0]]]+e[1:]+targets for e,targets in graph]
 assert code==json.loads((ROOT/'machine/instructions.json').read_text())
 oldcode=json.loads((inp/'pa194CS.instructions.json').read_text())
 def relocate(i):
  assert not 3634<i<3637
  return i if i<=3634 else i+4
 for pc,row in enumerate(oldcode):
  if 3634<=pc<3637:continue
  k=2 if row[0] in ('inc','dec') else 1
  assert code[relocate(pc)]==row[:k]+[relocate(x) for x in row[k:]]
 incoming=[(pc,t) for pc,row in enumerate(oldcode) if not 3634<=pc<3637 for t in row[2 if row[0] in ('inc','dec') else 1:] if 3634<=t<3637]
 assert incoming==[(3628,3634)]
 # Both success routines are entered only after the destructive comparison
 # has cleared H and X. T has just been moved completely into X, hence T=0.
 suffix=code[3634:3641]
 expected=[['dec',4,3638,3635],['inc',1,3636],['inc',6,3637],['jump',3634],['dec',6,3641,3639],['inc',4,3640],['jump',3638]]
 assert suffix==expected

 mapping={int(k):v for k,v in json.loads((Path(__file__).resolve().parent/'reference/legacy_mapping.json').read_text()).items()}
 for q in states|{254}:mapping.setdefault(q,q+10000)
 assert len({mapping[q] for q in states|{254}})==195 and mapping[84]==96 and mapping[254]==254
 table={(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in rows.items()}
 runtime.PHY=PHY;sym.HEADER_BASE=48
 lemmas,blocks=sym.prove_blocks(table);assert len(blocks)==4
 print('Four literal list lemmas rederived',flush=True)
 contracts=[];total=maximum=0
 for pc,site in enumerate(mapped):
  for positive in ([False,True] if site[1]=='CD' else [False]):
   result=sym.case(table,lemmas,site,positive);total+=result['symbolic_steps'];maximum=max(maximum,result['symbolic_steps'])
   contracts.append({'site':pc,'positive':positive,'duration':result['duration'],'motion':result['motion'],'symbolic_steps':result['symbolic_steps']})
  if (pc+1)%500==0:print('Checked',pc+1,'source sites',flush=True)
 assert len(contracts)==4750
 tape=bytearray(20000);origin=10000;head=origin;q=74
 for step in range(57768):
  assert q!=254 and 0<=head<len(tape)
  w,d,q=rows[q,tape[head]];tape[head]=w;head+=d
 assert q==84 and head-origin==-2
 address=sites[25][0];frame=bytearray([1]+[int(b) for b in address]+[0]*(48-len(address))+[1]);logical=[2]+[0]*8;physical=[None]*9
 for i,j in enumerate(PHY):physical[j]=logical[i]
 for v in physical+[1]*26:frame.extend([0]+[1]*(v+1))
 expected=bytearray(len(tape));expected[head-1:head-1+len(frame)]=frame;assert tape==expected
 seed={'steps':57768,'state':q,'head':head-origin,'ones':[i-origin for i,b in enumerate(tape) if b],'source_site':25,'source_path':address,'logical_registers':logical,'physical_registers':physical,'spare_values':[1]*26,'whole_blank_tape_equal':True}
 enc=(json.dumps(contracts,separators=(',',':'))+'\n').encode();(out/'contracts.json').write_bytes(enc)
 receipt={'family':'PA194NS','status':'PASS','working_states':194,'transition_rows':388,'source_sites':3650,'source_outcomes':4750,'symbolic_steps':total,'maximum_symbolic_steps':maximum,'minimum_positive_duration_constant':min(x['duration'][0] for x in contracts),'four_list_lemmas_rederived_from_literal_table':True,'arithmetic_box_oracles':False,'two_CFG_resolvers_agree':True,'independent_source_splice_matches':True,'external_splice_entries':incoming,'whole_blank_tape_equal':True,'startup_steps':57768,'dense_sha256':sha(format_table(dense).encode()),'native_sha256':sha(format_table(rows).encode()),'contracts_sha256':sha(enc),'kernel_checked':False,'elapsed_seconds':round(time.monotonic()-started,3)}
 for name,obj in [('receipt.json',receipt),('list_lemmas.json',blocks),('blank_seed.json',seed),('source_binding.json',{'source_prefix':prefix,'old_subtree':before,'new_subtree':sites[at:at+7],'incoming':incoming,'replacement_graph':suffix})]: (out/name).write_text(json.dumps(obj,indent=2)+'\n')
 print(json.dumps(receipt,indent=2),flush=True)
 return receipt

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();run(args.output)
