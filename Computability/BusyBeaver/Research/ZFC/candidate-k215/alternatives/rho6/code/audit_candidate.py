#!/usr/bin/env python3
"""Independent audit of saved K215-rho6 evidence; imports no supplied checker.
Checks current literal inputs, ordered cases, affine clocks, row coverage, block
row bindings, and independently replays the complete blank prefix. It does not
rerun symbolic proof construction or turn ordinary evidence into kernel proofs.
"""
from __future__ import annotations
from pathlib import Path
from collections import deque
import argparse,hashlib,json,time
PINS={'symbolic_runtime.py':'7ca30fd11def00e973d8f30997e51fa2dd87ae2eff311ea8c9fc4ac08c9d774f','independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346','legacy_mapping.json':'26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'}
PHY=(6,2,0,4,3,7,8,5,1)
def need(c,m):
 if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_bytes())
def table(p,halt=254):
 T={};starts=[]
 for ln in p.read_text().splitlines():
  if ln.startswith('#! start '):starts.append(int(ln[9:]));continue
  if not ln or ln.startswith('#'):continue
  q,b,w,d,z=ln.split();q,b,w,z=map(int,(q,b,w,z));need((q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R'),'table syntax');T[q,b]=(w,1 if d=='R'else-1,z)
 Q={q for q,b in T};need(starts==[0]and len(Q)==215 and len(T)==430 and set(T)=={(q,b)for q in Q for b in(0,1)},'total215state table');need({z for w,d,z in T.values()}-Q=={halt},'unique external halt')
 reach={0};todo=[0]
 for q in todo:
  for b in(0,1):
   z=T[q,b][2]
   if z!=halt and z not in reach:reach.add(z);todo.append(z)
 need(reach==Q,'every counted state graphreachable');return T

def cfg(rows):
 leaves={p:i for i,(p,o,r)in enumerate(rows)};need(len(leaves)==len(rows),'source unique leaf paths');prefixes={p[:i]for p in leaves for i in range(len(p))};need(not leaves.keys()&prefixes,'prefix-free leaves');need(all(p+b in leaves or p+b in prefixes for p in prefixes for b in('0','1')),'full binary tree');need([p for p,o,r in rows]==sorted(leaves),'ordered source')
 depth=max(map(len,leaves))
 def first(prefix):
  z=prefix+'0'*depth
  for k in range(1,depth+1):
   if z[:k]in leaves:need('1'not in prefix[k:],'stray suffix');return leaves[z[:k]]
  raise ValueError('no successor leaf')
 def inc(p):return format((int(p,2)+1)%(1<<len(p)),f'0{len(p)}b')if p else''
 def cut(p,b,n):
  indexes=[i for i,v in enumerate(p)if v==b];return p[:indexes[-n]]if len(indexes)>=n else''
 edges=[]
 for p,o,r in rows:
  need(p and set(p)<=set('01')and o in('CI','CD','CB','CC','CH'),'source instruction')
  if o in('CI','CD'):need(type(r)is int and 0<=r<9,'register range')
  elif o in('CB','CC'):need(type(r)is int and r>=1,'control depth')
  else:need(r is None,'halt operand')
  if o=='CI':e=[first(inc(p))]
  elif o=='CD':e=[first(inc(cut(p,'0',1))),first(inc(p))]
  elif o=='CB':e=[first(inc(cut(p,'0',r)))]
  elif o=='CC':e=[first(cut(p,'1',r))]
  else:e=[]
  edges.append(e)
 return edges

def graph_compare(A,B):
 mp={0:0};iv={0:0};word={0:''};todo=deque([0])
 while todo:
  q=todo.popleft();v=mp[q]
  for b in(0,1):
   x=A.get((q,b));y=B.get((v,b));w=word[q]+str(b)
   if x is None or y is None:
    if x!=y:return {'isomorphic':False,'reason':'terminal mismatch','word':w}
    continue
   if x[:2]!=y[:2]:return {'isomorphic':False,'reason':'action mismatch','word':w,'states':[q,v],'actions':[x,y]}
   u,z=x[2],y[2]
   if u in mp and mp[u]!=z:return {'isomorphic':False,'reason':'forced map conflict','word':w,'left_target':u,'previous_right_target':mp[u],'new_right_target':z}
   if z in iv and iv[z]!=u:return {'isomorphic':False,'reason':'forced injectivity conflict','word':w,'right_target':z,'previous_left_target':iv[z],'new_left_target':u}
   if u not in mp:mp[u]=z;iv[z]=u;word[u]=w;todo.append(u)
 return {'isomorphic':True,'map':mp}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--runtime-code',type=Path,required=True);ap.add_argument('--reference',type=Path,action='append',default=[]);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--dense',type=Path);a=ap.parse_args();tic=time.monotonic();C=a.candidate
 paths={'table':C/'candidate.native.tm','source':C/'sites.json','parent_table':a.parent/'k215.native.tm','parent_source':a.parent/'sites215.json','report':C/'runtime/runtime.json','cases':C/'runtime/runtime_cases.json','startup':C/'runtime/startup.json','log':C/'runtime.log','symbolic_runtime.py':a.runtime_code/'runtime/symbolic_runtime.py','independent_runtime.py':a.runtime_code/'runtime/independent_runtime.py','legacy_mapping.json':a.runtime_code/'inputs/legacy_mapping.json'}
 before={k:sha(p)for k,p in paths.items()}
 for n,h in PINS.items():need(before[n]==h,'pinned runtime implementation '+n)
 T=table(paths['table']);O=table(paths['parent_table']);need(set(T)==set(O),'same state labels')
 patch={k:v for k,v in T.items()if O[k]!=v};need(patch=={(199,1):(1,1,12),(206,0):(0,1,76)},'exact two-row patch');need(O[199,1]==(1,1,166)and O[206,0]==(0,1,186),'patch origins')
 source=read(paths['source']);parent=read(paths['parent_source']);need(len(source)==len(parent)==4751,'4751 source leaves');diff=[i for i,(x,y)in enumerate(zip(parent,source))if x!=y];need(diff==[959,964,1137,1142],'exact four changed primitives');need(all(parent[i][:2]==source[i][:2]and parent[i][2]==3 and source[i][2]==5 for i in diff),'only parameterCtoB');need(cfg(source)==cfg(parent),'every guarded successor identical')
 rep=read(paths['report']);cases=read(paths['cases']);log=paths['log'].read_text();need('UNIVERSAL_MATHEMATICAL_PASS'in log and not any(v in log for v in('NOT_PROVED','Traceback')),'terminal raw log')
 need(rep['status']=='UNIVERSAL_MATHEMATICAL_PASS'and rep['failures']==[]and rep['working_states']==215 and rep['site_count']==4751 and rep['proved_cases']==rep['expected_cases']==6176,'complete successful report')
 need(rep['table_sha256']==before['table']and rep['sites_sha256']==before['source']and rep['checker_sha256']==before['symbolic_runtime.py']and rep['helper_sha256']==before['independent_runtime.py'],'runtime input hash bindings')
 expected=[(i,pos)for i,(p,op,r)in enumerate(source)for pos in((False,True)if op=='CD'else(False,))];need(len(expected)==6176 and [(x['site_index'],x['positive'])for x in cases]==expected,'full ordered guarded cases')
 Q={q for q,b in T};mp={int(k):v for k,v in read(paths['legacy_mapping.json']).items()}
 for q in Q|{254}:
  if q not in mp:mp[q]=q+1000
 need(len({mp[q]for q in Q|{254}})==216,'injective legacy map');L={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T.items()};used=set()
 for x in cases:
  need(len(x['duration'])==13 and all(type(v)is int and v>=0 for v in x['duration'])and x['duration'][0]>0,'positive affine duration')
  need(len(x['motion'])==13 and all(type(v)is int for v in x['motion']),'affine motion')
  need(type(x['symbolic_steps'])is int and x['symbolic_steps']>0 and sum(x['kinds'].values())==x['symbolic_steps'],'symbolic event accounting')
  need(set(x['kinds'])<=set(('literal','unary','list')),'permitted rule kinds')
  for r in x['rows']:need(tuple(r)in L,'literal case row binding');used.add(tuple(r))
 signatures=[];blockrows=set()
 for x in rep['blocks']:
  signatures.append((x['entry'],x['direction'],x['before'],x['after']));need(x['steps']=='v+2'and x['arbitrary_contexts']is True,'oneblock statement')
  for ev in x['trace']:
   need(ev[0]in('literal','unary')and len(ev[1])==5,'block event syntax');q,b,w,d,z=ev[1];need(L[q,b]==(w,d,z),'block exact literal action');blockrows.add((q,b))
 need(signatures==[(73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')],'four block signatures');need(used|blockrows==set(L),'all430 rows covered')
 st=read(paths['startup']);need(st['status']==rep['startup_status']=='CALIBRATED_DIRTY_ROOT_SEED','calibrated startup status');need(st['steps']==len(st['trace']),'startup duration')
 q=h=0;ones=set();visited=set();lo=hi=0
 for tick,event in enumerate(st['trace']):
  b=int(h in ones);need((q,b)in T,'no premature halt');w,d,z=T[q,b];need(event==[q,h,b,w,d,z],f'blank replay event{tick}');visited.add((q,b))
  if w:ones.add(h)
  else:ones.discard(h)
  q=z;h+=d;lo=min(lo,h);hi=max(hi,h)
 need(q==st['state']==84 and h==st['head']==-8 and st['gap']==1 and st['registers']==[4,0,0,0,0,0,0,0,0]and st['spares']==[1]*40,'exact root frame registers')
 physical=[0]*9
 for i,j in enumerate(PHY):physical[j]=[4,0,0,0,0,0,0,0,0][i]
 frame={-9,57};cursor=58
 for v in physical+[1]*40:frame.update(range(cursor+1,cursor+v+2));cursor+=v+2
 need(ones==frame and st['one_cells']==sorted(frame)and len(ones)==95,'complete independent frame with zero exterior');need(not(set(patch)&visited),'two patched rows absent in entire blank prefix')
 pre=C/'startup.json'
 if pre.exists():need(read(pre)==st,'preflight startup equals fresh runtime startup')
 dense_audit=None
 if a.dense:
  dense=table(a.dense,215);rename={q:i for i,q in enumerate(sorted(Q))};rename[254]=215;need(dense=={(rename[q],b):(w,d,rename[z])for(q,b),(w,d,z)in T.items()},'all dense rows');cmap=read(C/'canonicalization.json');need({int(q):v for q,v in cmap['native_to_canonical'].items()}==rename and cmap['native_sha256']==before['table']and cmap['canonical_sha256']==sha(a.dense),'literal canonicalization record');dense_audit={'sha256':sha(a.dense),'all430_rows_match':True,'start':0,'halt':215,'dispatcher':rename[84]}
 process_receipt=None
 receipt_path=C/'execution_receipt.json'
 if receipt_path.exists():
  pr=read(receipt_path);need(pr['observed_tool_exit_code']==0 and pr['stdout_stderr_file']=='runtime.log','root process observation receipt');process_receipt={'sha256':sha(receipt_path),'kind':pr['kind'],'observed_tool_exit_code':0,'prelaunch_before_after_receipt':pr['prelaunch_before_after_receipt']}
 comparisons=[]
 for p in a.reference:comparisons.append({'reference':str(p),'sha256':sha(p),**graph_compare(T,table(p))})
 after={k:sha(p)for k,p in paths.items()};need(before==after,'audited inputs unchanged during audit')
 result={'status':'PASS_INDEPENDENT_SAVED_EVIDENCE_AND_BLANK_AUDIT','candidate':str(C),'auditor_sha256':sha(Path(__file__)),'input_hashes':before,'unchanged_during_audit':True,'source':{'leaves':4751,'decrements':1425,'guarded_cases':6176,'changed_ordinals':diff,'all_guarded_targets_preserved':True,'interpretation':'The four data effects copy logicalB instead of logicalC inside rho6; mathematical row-family reparameterization proof remains separate.'},'table':{'states':215,'rows':430,'all_states_graph_reachable':True,'patch':[[*k,*O[k],*T[k]]for k in sorted(patch)],'dense':dense_audit},'runtime':{'cases':len(cases),'symbolic_rules':sum(x['symbolic_steps']for x in cases),'maximum_rules_per_case':max(x['symbolic_steps']for x in cases),'minimum_duration_constant':min(x['duration'][0]for x in cases),'all_affine_clock_coefficients_nonnegative':True,'literal_rows_covered':len(used|blockrows),'block_rows':len(blockrows),'four_block_schemas_exact_rows':True,'runtime_seconds':rep['seconds']},'blank':{'steps':st['steps'],'state':q,'head':h,'header':57,'gap':1,'logical_registers':st['registers'],'spares':st['spares'],'one_cells':sorted(frame),'head_range':[lo,hi],'full_trace_independently_replayed':True,'full_zero_exterior':True,'patched_rows_unvisited':True},'process_receipt':process_receipt,'rooted_graph_comparisons':comparisons,'audit_seconds':time.monotonic()-tic,'scope':'Independent current-input/saved-output integrity checks and full finite blank replay; no supplied Python checker imports. Full symbolic induction was executed by the separate inherited checker. Neither proof-assistant kernel certification, before/after runtime immutability, nor unrecorded process metadata is claimed.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in('input_hashes','blank','rooted_graph_comparisons')},indent=2))
if __name__=='__main__':main()
