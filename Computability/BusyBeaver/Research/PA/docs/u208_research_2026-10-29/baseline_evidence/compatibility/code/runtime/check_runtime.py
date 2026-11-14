#!/usr/bin/env python3
"""Native-label whole-tape checker. Same inherited induction engine, not a new kernel."""
import argparse, hashlib, json, time
from pathlib import Path
import native_symbolic as s
import check_startup as boot

def need(b,msg):
 if not b:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def sites_checked(raw):
 S=json.loads(raw);need(isinstance(S,list) and S,'empty source');leaves=set();prefixes=set()
 for row in S:
  need(isinstance(row,list) and len(row)==3,'source row');pc,op,arg=row
  need(isinstance(pc,str) and 0<len(pc)<=64 and set(pc)<={'0','1'},'path')
  need(pc not in leaves,'duplicate site');leaves.add(pc);prefixes.update(pc[:i] for i in range(len(pc)))
  need(op in ('CI','CD','CB','CC','CH'),'opcode')
  if op=='CH':need(arg is None,'halt argument')
  elif op in ('CI','CD'):need(type(arg)==int and 0<=arg<9,'register')
  else:need(type(arg)==int and arg>=1,'loop depth')
 need(not leaves&prefixes,'prefix collision');need(all(p+b in leaves|prefixes for p in prefixes for b in '01'),'incomplete tree')
 need(sum(row[1]=='CH'for row in S)==1,'halt count');return S

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--table',required=True,type=Path);ap.add_argument('--sites',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);a=ap.parse_args();a.output.parent.mkdir(parents=True,exist_ok=True)
 paths=[a.table,a.sites,Path(__file__),Path(s.__file__),Path(s.r.__file__),Path(boot.__file__)];sealed=[p.read_bytes()for p in paths]
 T=boot.load_table(a.table);Q={q for q,b in T};need(0 in Q and 84 in Q,'start/dispatch');need(all((q,b)in T for q in Q for b in(0,1)),'partial table');need({q for _,_,q in T.values()}-Q=={254},'external target');S=sites_checked(sealed[1]);lemmas,blocks=s.prove_blocks(T);cases=[];began=time.monotonic()
 for i,site in enumerate(S):
  for positive in ((False,True)if site[1]=='CD'else(False,)):
   try:ans=s.case(T,lemmas,site,positive)
   except Exception as e:
    a.output.write_text(json.dumps({'status':'NOT_PROVED','site_index':i,'site':site,'positive':positive,'reason':repr(e)},indent=2)+'\n');raise
   ans['rows']=sorted(ans['rows']);ans.pop('trace');cases.append({'site_index':i,'positive':positive,**ans})
  if i%500==0:print('site',i,'cases',len(cases),flush=True)
 need(all(p.read_bytes()==raw for p,raw in zip(paths,sealed)),'input changed')
 report={'status':'NATIVE_UNIVERSAL_MATHEMATICAL_PASS','working_states':len(Q),'sites':len(S),'cases':len(cases),'table_sha256':sha(sealed[0]),'sites_sha256':sha(sealed[1]),'checker_files':{p.name:sha(b)for p,b in zip(paths[2:],sealed[2:])},'seconds':time.monotonic()-began,'blocks':blocks,'minimum_steps':min(c['duration'][0]for c in cases),'scope':'All natural primary registers at each guard; arbitrary natural extra gap; arbitrary nonempty finite spare list; complete tape. Inherited induction engine relabeled directly, not an independent proof kernel.'}
 a.output.write_text(json.dumps(report,indent=2)+'\n');a.output.with_suffix('.cases.json').write_text(json.dumps(cases)+'\n');print(report['status'],len(cases),flush=True)
if __name__=='__main__':main()
