#!/usr/bin/env python3
"""Independent finite review of depth41, reading artifacts as data.
The complete symbolic runtime was run separately by the source-search agent;
this program audits its input binding, case census, and row receipts, rather
than presenting that receipt audit as another quantified runtime derivation.
"""
from pathlib import Path
from collections import defaultdict, deque, Counter
from functools import lru_cache
import json,hashlib,gzip,argparse,sys
if not __debug__ or sys.flags.optimize:
 raise RuntimeError("Review requires assertions; run without -O.")
def load_json(p):
 raw=p.read_bytes()
 return json.loads(gzip.decompress(raw) if p.suffix=='.gz' else raw)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def enc(x):return (json.dumps(x,separators=(',',':'))+'\n').encode('ascii')
def digest(x):return hashlib.sha256(enc(x)).hexdigest()
def table(p,halt=254):
 out={};starts=[]
 for line in p.read_text().splitlines():
  if line.startswith('#! start '):starts.append(int(line[9:]));continue
  if not line or line.startswith('#'):continue
  q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t));assert (q,b)not in out and d in('L','R') and b in(0,1)and w in(0,1)
  out[q,b]=(w,1 if d=='R'else-1,t)
 Q={q for q,b in out};assert starts==[0] and set(out)=={(q,b)for q in Q for b in(0,1)}
 assert {t for w,d,t in out.values()}-Q=={halt}
 return out

def tree(rows):
 leaves={p:(op,arg)for p,op,arg in rows};assert len(leaves)==len(rows)
 def at(p):return leaves[p]if p in leaves else(at(p+'0'),at(p+'1'))
 t=at('');assert flat(t)==rows;return t

def leaf(t):return isinstance(t[0],str)
def flat(t,p=''):return [[p,*t]]if leaf(t)else flat(t[0],p+'0')+flat(t[1],p+'1')
def internal(t,p=''):
 if leaf(t):return
 yield p,t
 yield from internal(t[0],p+'0');yield from internal(t[1],p+'1')
@lru_cache(None)
def closed(t):
 if leaf(t):
  op,n=t
  return (1,0,False)if op=='CD'else(n,0,False)if op=='CB'else(0,n,False)if op=='CC'else(0,0,op=='CH')
 x,y=closed(t[0]),closed(t[1]);return max(x[0]-1,0,y[0]),max(x[1],y[1]-1,0),x[2]or y[2]
def replace(t,old,new):return new if t==old else t if leaf(t)else(replace(t[0],old,new),replace(t[1],old,new))

def interval_cfg(rows):
 # Determine each prefix interval from the literal ordered leaf list.
 spans={};n=len(rows)
 for i,(p,op,arg)in enumerate(rows):
  for j in range(len(p)+1):
   s=p[:j]
   if s not in spans:spans[s]=[i,i+1]
   else:spans[s][1]=i+1
 def escape(p,bit,count):
  for j in range(len(p)-1,-1,-1):
   if p[j]==bit:
    count-=1
    if count==0:return spans[p[:j]][1]%n if bit=='0'else spans[p[:j]][0]
  return 0
 out=[]
 for i,(p,op,a)in enumerate(rows):
  nxt=(i+1)%n
  out.append([op,a, [nxt]if op=='CI'else[escape(p,'0',1),nxt]if op=='CD'else[escape(p,'0',a)]if op=='CB'else[escape(p,'1',a)]if op=='CC'else[]])
 return out

def arithmetic_cfg(rows):
 leaves={p:i for i,(p,op,a)in enumerate(rows)};depth=max(map(len,leaves))
 def resolve(p):
  for j in range(1,depth+1):
   k=(p+'0'*depth)[:j]
   if k in leaves:
    assert '1'not in p[j:];return leaves[k]
  raise AssertionError('Unresolved successor')
 def succ(p):return format((int(p,2)+1)%(2**len(p)),'0'+str(len(p))+'b')if p else''
 def cut(p,b,n):
  inds=[j for j,x in enumerate(p)if x==b]
  return p[:inds[-n]]if len(inds)>=n else''
 out=[]
 for p,op,a in rows:
  targets=[resolve(succ(p))]if op=='CI'else[resolve(succ(cut(p,'0',1))),resolve(succ(p))]if op=='CD'else[resolve(succ(cut(p,'0',a)))]if op=='CB'else[resolve(cut(p,'1',a))]if op=='CC'else[]
  out.append([op,a,targets])
 return out

def decode(T,t):
 groups=defaultdict(set);paths=defaultdict(list);occ={}
 # Each prefix is independently replayed from the actual dispatcher.
 for p,n in internal(t):
  bits={-1:1,**{i:int(b)for i,b in enumerate(p)}};original=bits.copy();q=84;h=0
  for tick in range(10000):
   if h==len(p):break
   assert h in bits
   w,d,q=T[q,bits[h]];bits[h]=w;h+=d
  else:raise AssertionError('Prefix did not terminate')
  assert h==len(p) and bits==original
  groups[q].add(n);paths[q].append(p);occ[p]=q
 return groups,paths,occ

def canonical(T,halt=254):
 order=[0];m={0:0,halt:-1};rows=[]
 for q in order:
  for b in(0,1):
   w,d,t=T[q,b]
   if t not in m:m[t]=len(order);order.append(t)
   rows.append([m[q],b,w,d,m[t]])
 assert len(order)==len(T)//2
 return rows

def metrics(t):
 nodes=set()
 def go(n):
  if n in nodes:return
  nodes.add(n)
  if not leaf(n):go(n[0]);go(n[1])
 go(t);rr=flat(t)
 return {'dag_nodes':len(nodes),'leaf_occurrences':len(rr),'maximum_depth':max(len(p)for p,op,a in rr),'maximum_zero_run':max(len(x)for p,op,a in rr for x in p.split('1')),'total_address_bits':sum(len(p)for p,op,a in rr)}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();P=args.packet.resolve()
 basep=P/'baseline/k215.native.tm';bases=P/'baseline/sites215.json';tp=P/'machine/k215r.native.tm';sp=P/'machine/sites215r.json'
 assert sha(tp)=='8cfb95be77f8f8819ac7dc5c92297cf32b5104cbdf22aea925ab38de9c4443b9' and sha(sp)=='46ab3fdabc6ade3c6e4b5f08a0a59af66eb96f3992124ab6b71b8c3f1a05bf35'
 assert sha(basep)=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
 assert sha(bases)=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
 T=table(basep);base=dict(T);root=tree(json.loads(bases.read_text()));word=[x[1:]for x in flat(root)];cfg=interval_cfg(flat(root));assert cfg==arithmetic_cfg(flat(root))
 recipe=load_json(P/'machine/recipe.json');recipe['table_sha256']=recipe['expected_native_sha256'];recipe['source_sha256']=recipe['expected_source_sha256'];assert len(recipe['rotations'])==10;rot=[]
 for step in recipe['rotations']:
  assert step['state_merges']==[]
  q,m=step['q'],step['m'];side=1 if step['direction']=='left' else 0
  groups,paths,occ=decode(T,root);assert len(groups[q])==1 and len(groups[m])==1
  n=next(iter(groups[q]));sub=n[side];assert sub==next(iter(groups[m])) and set(paths[m])=={p+str(side)for p in paths[q]}
  assert {k for k,ns in groups.items()if n in ns}=={q}
  A,B,C=(n[0],*n[1])if side else(*n[0],n[1]);assert all(closed(x)==(0,0,False)for x in(A,B,C))
  assert all(T[z,b][:2]==(b,1)for z in(q,m)for b in(0,1)) and T[q,side][2]==m
  V=dict(T)
  if side:
   V[q,0]=(0,1,m);V[q,1]=(1,1,T[m,1][2]);V[m,0]=(0,1,T[q,0][2]);V[m,1]=(1,1,T[m,0][2]);new=((A,B),C)
  else:
   V[q,0]=(0,1,T[m,0][2]);V[q,1]=(1,1,m);V[m,0]=(0,1,T[m,1][2]);V[m,1]=(1,1,T[q,1][2]);new=(A,(B,C))
  root=replace(root,n,new);T=V;rr=flat(root);assert [x[1:]for x in rr]==word and interval_cfg(rr)==cfg==arithmetic_cfg(rr)
  decode(T,root)
  rot.append({**step,'source_occurrences':len(paths[q]),'all_three_factors_closed':True,'word_and_both_CFGs_equal':True})
 assert T==table(tp) and flat(root)==json.loads(sp.read_text())
 assert sha(tp)==recipe['table_sha256']and sha(sp)==recipe['source_sha256']
 comparisons=[];can=canonical(T);densep=P/'machine/k215r.tm';dense=table(densep,halt=215);assert {q for q,b in dense}==set(range(215)) and canonical(dense,halt=215)==can
 for name,p in [('primary',basep),('commands120',P/'baseline/commands120.native.tm'),('composed',P/'baseline/composed.native.tm')]:
  cc=canonical(table(p));assert can!=cc
  i=next(i for i,(a,b)in enumerate(zip(can,cc))if a!=b)
  comparisons.append({'name':name,'table_sha256':sha(p),'canonical_graph_sha256':digest(cc),'not_isomorphic':True,'first_canonical_differing_row':i,'candidate_row':can[i],'reference_row':cc[i]})
 # Replay every saved blank transition using an independent explicit tape.
 bootp=P/'verification/runtime/startup.json.gz';boot=load_json(bootp);q=0;h=0;ones=set()
 for event in boot['trace']:
  b=int(h in ones);w,d,z=T[q,b];assert event==[q,h,b,w,d,z]
  if w:ones.add(h)
  else:ones.discard(h)
  q=z;h+=d
 assert [q,h,len(boot['trace'])]==[boot['state'],boot['head'],boot['steps']] and sorted(ones)==boot['one_cells']
 assert q==84 and h==-8 and min(ones)==h-1
 header=min(x for x in ones if x>h-1);assert header==57 and not any(h<=x<header for x in ones)
 vals=[];p=header+1;last=max(ones)
 while p<=last:
  assert p not in ones and p+1 in ones;p+=1;v=0
  while p in ones:v+=1;p+=1
  vals.append(v-1)
 phy=(6,2,0,4,3,7,8,5,1);regs=[vals[j]for j in phy];assert regs==[4,0,0,0,0,0,0,0,0]and vals[9:]==[1]*40 and len(ones)==95
 assert len(boot['trace'])==95714 and boot['registers']==regs and boot['spares']==vals[9:]
 # Receipt audit of the independently executed complete symbolic runtime.
 rp=P/'verification/runtime/runtime.json';cp=P/'verification/runtime/runtime_cases.json.gz';runtime=json.loads(rp.read_text());cases=load_json(cp);rows=flat(root)
 expected=[(i,p)for i,x in enumerate(rows)for p in((False,True)if x[1]=='CD'else(False,))]
 assert [(x['site_index'],x['positive'])for x in cases]==expected and len(cases)==6176
 assert runtime['status']=='UNIVERSAL_MATHEMATICAL_PASS'and runtime['failures']==[] and runtime['proved_cases']==runtime['expected_cases']==6176
 assert runtime['table_sha256']==sha(tp)and runtime['sites_sha256']==sha(sp)
 checker=P/'runtime/runtime/symbolic_runtime.py';helper=checker.with_name('independent_runtime.py')
 assert runtime['checker_sha256']==sha(checker)=='7ca30fd11def00e973d8f30997e51fa2dd87ae2eff311ea8c9fc4ac08c9d774f' and runtime['helper_sha256']==sha(helper)=='0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'
 assert sha(P/'runtime/validate_native.py')=='49b0a77bafa3549cef72e381352eeadad28937519ec5463c3cf3bee545f6f7e2' and sha(P/'runtime/inputs/legacy_mapping.json')=='26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'
 mapping={int(k):v for k,v in json.loads((P/'runtime/inputs/legacy_mapping.json').read_text()).items()}
 for a in {q for q,b in T}|{254}:mapping.setdefault(a,a+1000)
 inv={v:k for k,v in mapping.items()};used=set()
 for c in cases:
  assert len(c['duration'])==len(c['motion'])==13 and c['duration'][0]>0 and all(v>=0 for v in c['duration'])
  assert c['symbolic_steps']>0 and sum(c['kinds'].values())==c['symbolic_steps']
  for x,b in c['rows']:
   assert x in inv and(inv[x],b)in T;used.add((inv[x],b))
 for oneblock in runtime['blocks']:
  assert oneblock['arbitrary_contexts']and oneblock['steps']=='v+2'
  for event in oneblock['trace']:
   if event[0]in('literal','unary'):
    x,b,w,d,z=event[1];assert T[inv[x],b]==(w,d,inv[z]);used.add((inv[x],b))
 assert len(runtime['blocks'])==4 and used==set(T)
 oldcases=load_json(P/'baseline/runtime_cases.json.gz');assert [(x['site_index'],x['positive'])for x in oldcases]==expected
 differences=[b['duration'][0]-a['duration'][0]for a,b in zip(oldcases,cases)];assert all(a['duration'][1:]==b['duration'][1:]for a,b in zip(oldcases,cases))
 basepaths=json.loads(bases.read_text());timing={'changed_leaf_paths':sum(a[0]!=b[0]for a,b in zip(basepaths,rows)),'depth_change_histogram':dict(sorted(Counter(len(b[0])-len(a[0])for a,b in zip(basepaths,rows)).items())),'affine_duration_nonconstant_coefficients_unchanged':True,'duration_constant_difference_sum':sum(differences),'duration_constant_difference_range':[min(differences),max(differences)],'cases_faster':sum(x<0 for x in differences),'cases_slower':sum(x>0 for x in differences),'cases_same_duration':sum(x==0 for x in differences),'scope':'Per-primitive symbolic duration comparison under matched ordinal cases. This is not a uniformly faster machine: some cases are slower. No execution-frequency weighting is claimed.'}
 report={'status':'INDEPENDENT_FINITE_SOURCE_STARTUP_AND_RECEIPT_REVIEW_PASS','candidate_table_sha256':sha(tp),'candidate_source_sha256':sha(sp),'dense_table_sha256':sha(densep),'dense_canonical_graph_equal':True,'working_states':len(T)//2,'transition_rows':len(T),'metrics':metrics(root),'rotations':rot,'ordered_primitive_word_equal':True,'guarded_successor_edges':sum(len(x[2])for x in cfg),'halt_sites':sum(x[0]=='CH'for x in cfg),'decoder_prefixes':len(list(internal(root))),'changed_rows':sum(T[k]!=base[k]for k in T),'canonical_graph_sha256':digest(can),'graph_comparisons':comparisons,'blank':{'steps':len(boot['trace']),'head':h,'dispatcher':q,'header':header,'gap':header-h-64,'registers':regs,'spare_count':len(vals)-9,'spare_values':[1],'one_cells':len(ones),'complete_trace_replayed':True,'zero_exterior':True,'startup_file_sha256':sha(bootp)},'runtime_receipt_review':{'cases':len(cases),'all_cases_in_canonical_order':True,'symbolic_rules':sum(x['symbolic_steps']for x in cases),'minimum_duration_constant':min(x['duration'][0]for x in cases),'all_transition_rows_accounted_for':len(used),'four_block_traces_match_exact_table':True,'runtime_sha256':sha(rp),'cases_sha256':sha(cp),'checker_sha256':sha(checker),'helper_sha256':sha(helper),'scope':'Reviews actual saved quantified-runtime records and unchanged checker code identity; does not rerun the quantified derivation or establish a proof-assistant kernel theorem.'},'proof_scope':'Ten closed source reassociations preserve every ordered primitive and both complete guarded CFGs. Given the separately executed unchanged whole-tape symbolic checker and inherited accepted K215 logical calibration, this is an ordinary-mathematical 215-state alternative, not a214-state result.','timing_comparison':timing,'reviewer':'encoding agent, independently of source-search construction','baseline_metrics':metrics(tree(json.loads(bases.read_text()))),'review_script_sha256':sha(Path(__file__))}
 args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
