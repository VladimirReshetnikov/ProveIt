"""Literal reader transplant with rigid common engine interfaces.
Outputs a table only when all source bindings finish and every target is defined.
The finite contracts and blank startup remain independent verification gates.
"""
from pathlib import Path
import sys,json,argparse
H=Path(__file__).resolve().parent;BASE=H.parents[1]
sys.path.insert(0,str(H));import independent_source as ds
import source_language as sl

def read(p):
 t={}
 for l in Path(p).read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();t[int(q),int(b)]=int(w),1 if d=='R' else -1,int(z)
 return t

def encode(t,start=0):
 return f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for(q,b),(w,d,z)in sorted(t.items()))

def build(p_table,p_sites,out,u_table=None,outside_report=None):
 out=Path(out);out.mkdir(parents=True,exist_ok=True)
 P=read(p_table);U=read(u_table or H/'u208.native.tm');ps=json.loads(Path(p_sites).read_text())
 outside_report=Path(outside_report or H/'outside_contracts.json')
 if isinstance(ps[0],dict):
  om={'inc':'CI','dec':'CD','continueTo':'CC','breakTo':'CB','halt':'CH'}
  ps=[[x['path'],om[x['op']],x['arg']]for x in ps]
 us=json.loads((H/'sites.json').read_text());prefix='10101001';uprefix='0011001'
 pbranches,*_=ds.source_info(ps);pbindings,_=ds.prefix_binding(P,pbranches)
 interfaces={q for q,b in P}-set(pbindings.values());interfaces.add(254)
 proot=pbindings[prefix];closure={proot};stack=[proot]
 while stack:
  q=stack.pop()
  if q in interfaces:continue
  for b in(0,1):
   z=P[q,b][2]
   if z not in closure:closure.add(z);stack.append(z)
 pnodes=closure-interfaces;unodes={q for q,b in U}-interfaces
 relation={(p,u)for p in pnodes for u in unodes if all(P[p,b][:2]==U[u,b][:2]for b in(0,1))}
 while True:
  nxt={(p,u)for p,u in relation if all((P[p,b][2],U[u,b][2])in relation or(P[p,b][2]in interfaces and P[p,b][2]==U[u,b][2])for b in(0,1))}
  if nxt==relation:break
  relation=nxt
 mapping={q:q for q in interfaces}
 for p in sorted(pnodes):
  qs=sorted(u for a,u in relation if a==p)
  mapping[p]=p if p in qs else qs[0]if qs else(p if(p,0)not in U else 10000+p)
 T=U.copy()
 for p in sorted(pnodes):
  q=mapping[p];acts=[(w,d,mapping[z])for b in(0,1)for w,d,z in[P[p,b]]]
  if(q,0)in T:assert all(T[q,b]==acts[b]for b in(0,1)),(p,q)
  else:
   for b in(0,1):T[q,b]=acts[b]
 T[11,1]=(1,1,mapping[proot])
 ax=[['0011001'+p[len(prefix):],o,a]for p,o,a in ps if p.startswith(prefix)]
 sites=[x for x in us if not x[0].startswith(uprefix)]
 sites=sites[:25]+ax+sites[25:]
 branches,*_=ds.source_info(sites);bindings,_=ds.prefix_binding(T,branches)
 used={q for q,b in json.loads(outside_report.read_text())['rows_used']}
 retained=set(bindings.values())|(interfaces-{254})|used|(set(mapping.values())-{254})
 # Existing outside helper201 is constrained only on1; reuse copied PA217.
 share=mapping.get(217)
 merges=[]
 if share and share in retained and share!=201 and T[share,1]==T[201,1]:
  assert [201,0]not in json.loads(outside_report.read_text())['rows_used']
  T[201,0]=T[share,0]
  T={(q,b):(w,d,201 if z==share else z)for(q,b),(w,d,z)in T.items()if q!=share}
  retained.discard(share);merges.append([share,201])
 T={k:a for k,a in T.items()if k[0]in retained}
 targets={z for w,d,z in T.values()}-{q for q,b in T}
 if targets!={254}:raise ValueError({'incomplete_states':len(T)//2,'undefined_targets':sorted(targets),'undefined_rows':[[q,b,*act]for(q,b),act in T.items()if act[2]in targets-{254}]})
 (out/'candidate.native.tm').write_text(encode(T));(out/'sites.json').write_text(json.dumps(sites,separators=(',',':'))+'\n')
 r={'states':len(T)//2,'sites':len(sites),'readers':len(set(bindings.values())),'merges':merges,'mapping':mapping,'source_metrics':sl.metrics(sl.tree(sites))}
 (out/'construction.json').write_text(json.dumps(r,indent=2)+'\n');print({k:v for k,v in r.items()if k!='mapping'})
 return r

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('table');p.add_argument('sites');p.add_argument('out');a=p.parse_args();build(a.table,a.sites,a.out)
