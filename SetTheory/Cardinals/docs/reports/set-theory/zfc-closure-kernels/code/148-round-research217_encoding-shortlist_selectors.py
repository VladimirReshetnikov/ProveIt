"""Owned exact binding and new-marker selector tests for three source plateaus."""
from pathlib import Path
import sys,json,time,collections,hashlib,io,contextlib
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
import three_cell_selectors as S
T=A.R.table(A.NEW/'k218.native.tm');old=A.P.tree(json.load(open(A.NEW/'sites218.json')));og,op,oldgates=A.P.allocation(T,old)
folder=ROOT/'research217_source_plateaus';ranked=json.load(open(folder/'SELECTOR_OPPORTUNITY_SHORTLIST.json'))['ranked']
chosen=['source_62d69601c790b0c3.sites.json','source_6550ca5904ccf727.sites.json','source_da92475c629a42cb.sites.json']
plans=[next(r for r in ranked if r['source_file']==f)for f in chosen]
start=time.monotonic();steps=0
class Cap(Exception):pass

def allocate(V,root):
 groups=collections.defaultdict(set);paths={};gates=[]
 def visit(n,p):
  global steps
  if A.P.leaf(n):return
  tape={-1:1,**{i:int(b)for i,b in enumerate(p)}};orig=tape.copy();q=84;h=0;seen=set()
  while h!=len(p):
   if q==254 or h not in tape:raise ValueError(('unknown prefix',p,q,h))
   key=q,h,tuple(tape.values())
   if key in seen:raise ValueError(('cycle',p,q,h))
   seen.add(key)
   if steps>=1000000 or time.monotonic()-start>=5:raise Cap('aggregate cap')
   w,d,q=V[q,tape[h]];tape[h]=w;h+=d;steps+=1
  if tape!=orig:raise ValueError(('dirty prefix',p,q))
  groups[q].add(n);paths[p]=q
  for b,ch in enumerate(n):
   if A.P.leaf(ch):gates.append((ch,b,V[q,b],p+str(b)))
   else:visit(ch,p+str(b))
 visit(root,'');return groups,paths,gates

def selector(V,newpairs,dest):
 global steps
 inc=collections.defaultdict(list)
 for(q,b),(w,d,z)in V.items():inc[z].append((q,b,w,d))
 marks={};premises={}
 for q in {s for p in newpairs for s in p['states']}:
  assert q!=0 and inc[q]and all(d==1 for pp,b,w,d in inc[q])
  if all(pp!=0 and inc[pp]and all(dd==1 for ppp,bb,ww,dd in inc[pp])for pp,b,w,d in inc[q]):
   marks[q]=sorted({(ww,w)for pp,b,w,d in inc[q]for ppp,bb,ww,dd in inc[pp]});premises[q]='two R predecessors'
  else:
   marks[q]=sorted({(a,w)for pp,b,w,d in inc[q]for a in(0,1)});premises[q]='one R predecessor; older bit universally enumerated'
 pairs=[]
 for pair in newpairs:
  q,r=pair['states'];assert not set(marks[q])&set(marks[r]);same=[b for b in(0,1)if V[q,b]==V[r,b]];assert len(same)==1
  pairs.append(dict(states=[q,r],markers=[marks[q],marks[r]],shared_read=same[0]))
 S.T=V;S.states=sorted({q for q,b in V});S.path=dest/'raw.native.tm';S.incoming=inc;S.markers=marks;S.pairs=pairs;S.steps=0;S.start=time.monotonic();S.CAP_STEPS=1000000-steps;S.CAP_SECS=max(0,5-(S.start-start));S.OUTPUT_PATH=dest/'selectors.json'
 with contextlib.redirect_stdout(io.StringIO()):S.main()
 result=json.load(open(S.OUTPUT_PATH));steps+=S.steps;result['marker_premise_kind']=premises;result['scope']+=' Where only one incoming R marker is proved, the older bit is universally enumerated rather than assumed.';S.OUTPUT_PATH.write_text(json.dumps(result,indent=2)+'\n');return result
reports=[]
for i,plan in enumerate(plans):
 rec=dict(source_file=plan['source_file'],source_sha256=plan['source_sha256'],changed_rows=plan['changed_rows'])
 try:
  raw=(folder/plan['source_file']).read_bytes();assert hashlib.sha256(raw).hexdigest()==plan['source_sha256'];source=A.P.tree(json.loads(raw));assert A.continuation_cfg(old)==A.continuation_cfg(source)
  U=T.copy()
  for edit in plan['changed_rows']:
   k=tuple(edit['row']);assert U[k]==tuple(edit['old']);U[k]=tuple(edit['new'])
  assert len(U)==436;assert all(U[k]==T[k]for k in[(188,1),(189,1),(190,0),(190,1),(156,1),(176,1)])
  groups,paths,gates=allocate(U,source);oldgate=collections.defaultdict(set)
  for op,b,act,p in oldgates:oldgate[op,b].add(act)
  bad=[dict(op=op,read=b,action=act,path=p)for op,b,act,p in gates if act not in oldgate[op,b]]
  dest=OUT/f'plateau_shortlist_{i}';dest.mkdir(exist_ok=True);(dest/'sites.json').write_bytes(raw);(dest/'raw.native.tm').write_bytes(A.P.M.enc(U))
  rec.update(prefix_status='PASS',source_dag_nodes=len(A.P.nodes(source))+23,exact_cfg=True,novel_primitive_entry_count=len(bad),novel_primitive_entries=bad,decoder_states=len(groups),roles=sum(map(len,groups.values())))
  result=selector(U,plan['new_marked_pairs'],dest);rec.update(selector_status=result['status'],selector_pairs=len(result['pairs']),selector_matches=result['matches'],selector_near_matches=[dict(states=x['states'],action=x['action'],matching_role=x['matching_role'],missing_role=x['missing_role'],failures=[dict(marker=f['marker'],expected=f['expected_target'],actual=f['restored_wrong']['q'])for f in x['failures']])for x in result['near_matches']])
 except Cap as e:rec.update(status='CAP_UNKNOWN',reason=repr(e));reports.append(rec);break
 except Exception as e:rec.update(status='REJECT',reason=repr(e))
 reports.append(rec)
out=dict(reports=reports,total_prefix_helper_transitions=steps,seconds=time.monotonic()-start,scope='Source exact CFG plus complete prefix binding and supported primitive-action inventory; not universal primitive arithmetic/startup. Selector hits, if any, prove all-tape local folding of provisional raw layout, still requiring full runtime and blank proof.')
(OUT/'PLATEAU_SHORTLIST_RESULTS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
