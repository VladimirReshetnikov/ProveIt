#!/usr/bin/env python3
"""Independent finite source, table, prefix, and archived graph audit.
No incoming code is executed. Runtime proof and logical calibration are separate.
"""
from pathlib import Path
import argparse,hashlib,json,zipfile,io,sys
if not __debug__ or sys.flags.optimize:
 raise RuntimeError('Assertions are part of this audit; do not use Python -O.')

def sha(b):return hashlib.sha256(b).hexdigest()
def parse(raw):
 t={};start=None
 for s in raw.decode().splitlines():
  s=s.strip()
  if s.startswith('#! start '):start=int(s[9:]);continue
  if not s or s.startswith('#'):continue
  q,b,w,d,z=s.split();q,b,w,z=map(int,(q,b,w,z))
  assert (q,b)not in t and b in (0,1)and w in(0,1)and d in('L','R')
  t[q,b]=(w,1 if d=='R'else-1,z)
 qs={q for q,b in t};assert len(t)==2*len(qs) and all((q,b)in t for q in qs for b in(0,1))
 hs={z for w,d,z in t.values()}-qs;assert len(hs)==1;halt=next(iter(hs));assert start in qs
 return t,start,halt

def rooted(T,start,halt,U,us,uh,reflect=False):
 mp={start:us,halt:uh};inv={us:start,uh:halt};todo=[start];words={start:''}
 for q in todo:
  zq=mp[q]
  for b in (0,1):
   w,d,r=T[q,b];uw,ud,ur=U[zq,b]
   path=words[q]+str(b)
   if(w,d)!=(uw,-ud if reflect else ud):return {'isomorphic':False,'kind':'action','word':path,'candidate_action':[w,d],'other_action':[uw,-ud if reflect else ud]}
   if r in mp and mp[r]!=ur:return {'isomorphic':False,'kind':'forced_map','word':path,'old_target':r,'required':mp[r],'actual':ur}
   if ur in inv and inv[ur]!=r:return {'isomorphic':False,'kind':'injectivity','word':path,'old_target':r,'other_target':ur,'previous_old':inv[ur]}
   if r not in mp:
    mp[r]=ur;inv[ur]=r;todo.append(r);words[r]=path
 if len(mp)!=len(T)//2+1 or len(inv)!=len(U)//2+1:return {'isomorphic':False,'kind':'reachability','mapped':len(mp)}
 return {'isomorphic':True,'map':mp}

def canonical_graph(T,start,halt,reflect=False):
 # Breadth-first state numbering is forced by start and the ordered read bits.
 ids={start:0,halt:-1};queue=[start];rows=[]
 for q in queue:
  row=[]
  for b in (0,1):
   w,d,z=T[q,b]
   if z not in ids:ids[z]=len(queue);queue.append(z)
   row.append([w,-d if reflect else d,ids[z]])
  rows.append(row)
 return {'total_working_states':len(T)//2,'reachable_working_states':len(queue),'halt':-1,'rows':rows}

def graph_sha(T,start,halt,reflect=False):
 return sha(json.dumps(canonical_graph(T,start,halt,reflect),sort_keys=True,separators=(',',':')).encode())

def cfg(S):
 # Decode register control from numeric bit strings, then descend zero children.
 leaves={p:i for i,(p,op,k)in enumerate(S)}
 prefixes={p[:j]for p in leaves for j in range(len(p))}
 assert not set(leaves)&prefixes
 assert all(p+b in leaves or p+b in prefixes for p in prefixes for b in'01')
 def entry(p):
  q='';j=0
  while q not in leaves:
   assert q in prefixes,q
   q+=p[j] if j<len(p) else '0';j+=1
  return leaves[q]
 def plus(p):
  n=len(p);i=int(p or'0',2)+1
  return format(i%(1<<n),'0'+str(n)+'b')if n else''
 def strip(p,c,n):
  for j in range(len(p)-1,-1,-1):
   if p[j]==c:
    n-=1
    if n==0:return p[:j]
  return''
 graph=[]
 for p,op,k in S:
  if op=='CH':edges=[]
  elif op=='CI':edges=[entry(plus(p))]
  elif op=='CD':edges=[entry(plus(strip(p,'0',1))),entry(plus(p))]
  elif op=='CB':edges=[entry(plus(strip(p,'0',k)))]
  elif op=='CC':edges=[entry(strip(p,'1',k))]
  else:raise ValueError(op)
  graph.append(['JUMP'if op in('CB','CC')else op,None if op in('CB','CC')else k,edges])
 return graph,prefixes

def prefix_audit(T,S,prefixes):
 result=[];entries=[];pstates={}
 for p in sorted(prefixes):
  tape={-1:1,**{i:int(b)for i,b in enumerate(p)}};before=tape.copy();q=84;h=0;steps=0
  while h!=len(p):
   assert steps<10000 and -1<=h<len(p),(p,q,h)
   w,d,q=T[q,tape[h]];tape[h]=w;h+=d;steps+=1
  assert tape==before,(p,'changed prefix')
  pstates[p]=(q,steps);result.append({'path':p,'state':q,'steps':steps})
 for p,op,arg in S:
  q,steps=pstates[p[:-1]];b=int(p[-1]);entries.append({'path':p,'op':op,'arg':arg,'state':q,'steps':steps,'read':b,'entry_action':T[q,b]})
 return result,entries

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--table',type=Path,required=True);ap.add_argument('--source',type=Path,required=True);ap.add_argument('--reference-source',type=Path,required=True);ap.add_argument('--incoming',type=Path);ap.add_argument('--repository',type=Path);ap.add_argument('--comparison-inputs',type=Path);ap.add_argument('--pinned-head',default='75716498437bfc7291d5900cab2983a11fd54bac');ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
 assert a.comparison_inputs or(a.incoming and a.repository),'Supply either saved comparison inputs or both original input directories'
 inputs=a.out/'comparison-inputs';inputs.mkdir(exist_ok=True)
 raw=a.table.read_bytes();T,st,ha=parse(raw);assert len(T)==430
 # Control comparison separates the graph novelty from the append-zero bit.
 append_one=T.copy();w,d,z=append_one[198,0];assert(w,d,z)==(0,-1,40)
 append_one[198,0]=(1,d,z)
 S=json.loads(a.source.read_text());old=json.loads(a.reference_source.read_text());g,ps=cfg(S);og,_=cfg(old);assert g==og and[(o,k)for p,o,k in S]==[(o,k)for p,o,k in old]
 prefixes,entries=prefix_audit(T,S,ps)
 # Deterministic tree DAG, including primitive leaves.
 byp={p:(op,k)for p,op,k in S};nodes=set()
 def rec(p):
  n=byp[p]if p in byp else(rec(p+'0'),rec(p+'1'));nodes.add(n);return n
 rec('')
 records={};errors=[];archives=[]
 def add(raw,name):
  try:U,us,uh=parse(raw)
  except Exception as e:errors.append({'name':name,'reason':type(e).__name__});return
  if len(U)!=430:return
  h=sha(raw)
  if h not in records:
   (inputs/(h+'.tm')).write_bytes(raw)
   records[h]={'sha256':h,'names':[],'start':us,'halt':uh,'rooted_graph_sha256':graph_sha(U,us,uh),'rooted_reflected_graph_sha256':graph_sha(U,us,uh,True),'direct':rooted(T,st,ha,U,us,uh),'reflected':rooted(T,st,ha,U,us,uh,True),'append_one_control_direct':rooted(append_one,st,ha,U,us,uh),'append_one_control_reflected':rooted(append_one,st,ha,U,us,uh,True)}
  records[h]['names'].append(name)
 def scan_zip(data,name,depth=0):
  assert depth<=4
  with zipfile.ZipFile(io.BytesIO(data))as z:
   for item in z.infolist():
    if item.is_dir():continue
    if item.filename.lower().endswith('.tm'):
     add(z.read(item),name+'!'+item.filename)
    elif item.filename.lower().endswith('.zip') and depth<4:
     scan_zip(z.read(item),name+'!'+item.filename,depth+1)
 if a.comparison_inputs:
  provenance=json.loads((a.comparison_inputs/'provenance.json').read_text());assert provenance['pinned_repository_head']==a.pinned_head
  archives=provenance['archives']
  for item in provenance['tables']:
   data=(a.comparison_inputs/item['file']).read_bytes();assert sha(data)==item['sha256']
   for name in item['names']:add(data,name)
 else:
  for p in sorted(a.incoming.glob('*.zip')):
   data=p.read_bytes();archives.append({'name':p.name,'sha256':sha(data),'bytes':len(data)});scan_zip(data,p.name)
  for p in sorted((a.repository/'candidate-k215').rglob('*.tm')):add(p.read_bytes(),'repository/'+str(p.relative_to(a.repository)))
 provenance={'scope':'Inert byte copies of complete 215-state TM tables from the named archives, including nested ZIP members, and pinned repository candidate-k215 tables. No archive code is executed.','repository':'https://github.com/VladimirReshetnikov/ProveIt','pinned_repository_head':a.pinned_head,'archives':archives,'tables':[{'file':r['sha256']+'.tm','sha256':r['sha256'],'names':r['names']}for r in records.values()]}
 (inputs/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
 (a.out/'reference-source.sites.json').write_bytes(a.reference_source.read_bytes())
 cgraph=canonical_graph(T,st,ha);assert cgraph['reachable_working_states']==215
 (a.out/'canonical-rooted-graph.json').write_text(json.dumps(cgraph,indent=2)+'\n')
 csha=graph_sha(T,st,ha)
 assert all(r['direct']['isomorphic']==(csha==r['rooted_graph_sha256']) and r['reflected']['isomorphic']==(csha==r['rooted_reflected_graph_sha256']) for r in records.values())
 control_bytes=('#! start '+str(st)+'\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(append_one.items()))).encode()
 (a.out/'append-one-control.native.tm').write_bytes(control_bytes)
 control={'sha256':sha(control_bytes),'rooted_graph_sha256':graph_sha(append_one,st,ha),'isomorphic_direct':[r['names']for r in records.values()if r['append_one_control_direct']['isomorphic']],'isomorphic_reflected':[r['names']for r in records.values()if r['append_one_control_reflected']['isomorphic']],'scope':'The same final table with only native198/0 write restored to 1. This tests that graph novelty does not depend solely on the append-zero bit.'}
 (a.out/'graph-comparisons.json').write_text(json.dumps(list(records.values()),indent=2)+'\n')
 (a.out/'prefixes.json').write_text(json.dumps(prefixes,separators=(',',':'))+'\n');(a.out/'entries.json').write_text(json.dumps(entries,separators=(',',':'))+'\n')
 result={'status':'FINITE_SOURCE_TABLE_PREFIX_GRAPH_AUDIT_PASS','candidate_sha256':sha(raw),'source_sha256':sha(a.source.read_bytes()),'reference_source_sha256':sha(a.reference_source.read_bytes()),'rooted_graph_sha256':csha,'rooted_reflected_graph_sha256':graph_sha(T,st,ha,True),'working_states':len(T)//2,'reachable_working_states':cgraph['reachable_working_states'],'transitions':len(T),'start':st,'halt':ha,'dag_nodes':len(nodes),'leaves':len(S),'source_primitive_word_identical':True,'full_cfg_identical':True,'cfg_edges':sum(len(row[2])for row in g),'internal_prefixes':len(prefixes),'leaf_entries':len(entries),'max_depth':max(len(p)for p,_,_ in S),'max_zero_run':max(len(s)for p,_,_ in S for s in p.split('1')),'unique_215_table_bytes_compared':len(records),'named_215_tables_compared':sum(len(r['names'])for r in records.values()),'isomorphic_direct':[r['names']for r in records.values()if r['direct']['isomorphic']],'isomorphic_reflected':[r['names']for r in records.values()if r['reflected']['isomorphic']],'append_one_control':control,'unparsed_tm_files':errors,'scope':'Finite exact source/CFG, complete table, known-prefix traversal, and deterministic rooted graph comparisons. No arbitrary-value runtime or logical calibration proof is supplied by this script.'}
 (a.out/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
