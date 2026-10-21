#!/usr/bin/env python3
"""Run the pinned quantified primitive-interface checker on a literal candidate."""
from pathlib import Path
import sys,json,hashlib,time,argparse
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
REF=ROOT/'vendor'
sys.path.insert(0,str(REF/'runtime'));import symbolic_runtime as s

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('sites',type=Path);ap.add_argument('output',type=Path);args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
 T=s.r.table(args.table);sites=json.loads(args.sites.read_text());states={q for q,b in T};assert 254 not in states and len(T)==2*len(states)
 assert all(z==254 or z in states for w,d,z in T.values())
 m={int(k):int(v)for k,v in json.loads((REF/'inputs/legacy_mapping.json').read_text()).items()}
 for q in states|{254}:m.setdefault(q,q+1000)
 assert len({m[q]for q in states|{254}})==len(states)+1
 L={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()};begun=time.monotonic();cases=[];failures=[];rows=set();blocks=[]
 try:lemmas,blocks=s.prove_blocks(L)
 except Exception as e:failures.append(dict(stage='block_inductions',error=repr(e)))
 if not failures:
  for i,site in enumerate(sites):
   for positive in((False,True)if site[1]=='CD'else(False,)):
    try:
     ans=s.case(L,lemmas,site,positive);rows.update(ans.pop('rows'));ans.pop('trace');cases.append(dict(site_index=i,positive=positive,**ans))
    except Exception as e:
     failures.append(dict(stage='primitive_interface',site_index=i,site=site,positive=positive,error=repr(e)));print('FAIL',failures[-1],flush=True);break
   if failures:break
   if(i+1)%1000==0:print('SITE',i+1,'CASES',len(cases),'SECONDS',round(time.monotonic()-begun,3),flush=True)
 expected=sum(2 if x[1]=='CD' else 1 for x in sites);inv={v:k for k,v in m.items()}
 report=dict(status='ALL_PRIMITIVE_INTERFACES_PROVED'if not failures and len(cases)==expected else'NOT_PROVED',table_sha256=digest(args.table),sites_sha256=digest(args.sites),checker_sha256=digest(Path(s.__file__)),helper_sha256=digest(Path(s.r.__file__)),driver_sha256=digest(Path(__file__)),working_states=len(states),site_count=len(sites),expected_cases=expected,proved_cases=len(cases),failures=failures,blocks=blocks,seconds=time.monotonic()-begun,symbolic_steps=sum(x['symbolic_steps']for x in cases),minimum_actual_steps=min((x['duration'][0]for x in cases),default=None),native_rows=sorted([inv[q],b]for q,b in rows))
 (args.output/'runtime.json').write_text(json.dumps(report,indent=2)+'\n');(args.output/'runtime_cases.json').write_text(json.dumps(cases,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items()if k not in('blocks','native_rows')},indent=2),flush=True)
 return 0 if report['status']=='ALL_PRIMITIVE_INTERFACES_PROVED' else 1
if __name__=='__main__':raise SystemExit(main())
