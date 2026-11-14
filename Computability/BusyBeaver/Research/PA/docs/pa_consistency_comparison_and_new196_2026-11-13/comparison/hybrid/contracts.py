from pathlib import Path
import sys,importlib.util,json,time
H=Path(__file__).resolve().parent

def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m
r=module('independent_runtime',H/'u208_independent_runtime.py')
s=module('hybrid_symbolic_runtime',H/'u208_symbolic_runtime.py')

def read(p):
 t={}
 for l in Path(p).read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();t[int(q),int(b)]=int(w),1 if d=='R' else -1,int(z)
 return t

def conjugacy(t):
 mp={int(k):int(v)for k,v in json.loads((H/'legacy_mapping.json').read_text()).items()}
 for q in {q for q,b in t}|{254}:mp.setdefault(q,q+10000)
 inv={v:k for k,v in mp.items()};assert len(inv)==len(mp)
 return {(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in t.items()},mp,inv

def verify(table,sites,outfile,selection=None):
 t=read(table);ts,mp,inv=conjugacy(t);lem,blocks=s.prove_blocks(ts)
 used=set();result=[];start=time.monotonic()
 for blk in blocks:
  for e in blk['trace']:used.add((inv[e[1][0]],e[1][1]))
 for i,site in enumerate(json.loads(Path(sites).read_text())):
  if selection and not selection(site):continue
  for positive in((False,True)if site[1]=='CD'else(False,)):
   try:ans=s.case(ts,lem,site,positive)
   except Exception as e:
    res={'status':'FAILED','site_index':i,'site':site,'positive':positive,'error':str(e),'completed':len(result),'seconds':time.monotonic()-start}
    Path(outfile).write_text(json.dumps(res,indent=2)+'\n');print({k:v for k,v in res.items()if k!='error'},flush=True);return res
   rs={(inv[q],b)for q,b in ans['rows']};used.update(rs)
   result.append({'i':i,'positive':positive,'symbolic_steps':ans['symbolic_steps'],'duration':ans['duration']})
 res={'status':'ALL_ARBITRARY_VALUE_CONTRACTS_PASS','cases':len(result),'states':len(t)//2,'rows_used':sorted(used),'maximum_steps':max(x['symbolic_steps']for x in result),'total_steps':sum(x['symbolic_steps']for x in result),'seconds':time.monotonic()-start}
 Path(outfile).write_text(json.dumps(res,indent=2)+'\n');print({k:v for k,v in res.items()if k!='rows_used'},flush=True);return res

if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('table');p.add_argument('sites');p.add_argument('output');p.add_argument('--outside-u208',action='store_true');a=p.parse_args()
 verify(a.table,a.sites,a.output,(lambda s:not s[0].startswith('0011001'))if a.outside_u208 else None)
