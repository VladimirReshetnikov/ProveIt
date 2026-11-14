#!/usr/bin/env python3
"""Native-label whole-tape symbolic primitive and blank-start validation.
Uses the archived exact-table induction checker, without its obsolete source pin.
Source semantics must be calibrated separately. A failure to derive is NOT a
semantic counterexample. A seed is accepted only at dispatcher root with the
three formula registers T,W,H zero; all other registers may be arbitrary.
"""
from pathlib import Path
import sys,json,hashlib,argparse,time
ROOT=Path(__file__).resolve().parent
RUNTIME=ROOT/'runtime'
sys.path.insert(0,str(RUNTIME));import symbolic_runtime as s
MAPPATH=ROOT/'inputs/legacy_mapping.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def startup(T,limit=10000000):
 q=0;h=0;ones=set();trace=[]
 for tick in range(limit+1):
  if q==84 and ones and min(ones)==h-1:
   rights=[x for x in sorted(ones) if x>h-1]
   if rights and rights[0]>=h+64:
    header=rights[0];p=header+1;last=max(ones);v=[];good=True
    while p<=last:
     if p in ones or p+1 not in ones:good=False;break
     p+=1;n=0
     while p in ones:n+=1;p+=1
     v.append(n-1)
    if good and len(v)>=10 and v[0]==v[2]==v[7]==0:
     logical=[v[j] for j in s.r.PHY]
     return {'status':'CALIBRATED_DIRTY_ROOT_SEED','steps':tick,'state':q,'head':h,'gap':header-h-64,'registers':logical,'spares':v[9:],'one_cells':sorted(ones),'trace':trace}
  b=int(h in ones)
  if(q,b) not in T:return {'status':'UNDEFINED','steps':tick,'state':q,'head':h}
  w,d,z=T[q,b]
  if b==0 and z==q and (not ones or(d==1 and h>max(ones))or(d==-1 and h<min(ones))):
   return {'status':'EXACT_OUTWARD_RAY','steps':tick,'state':q,'head':h,'write':w,'direction':d,'one_cells':sorted(ones),'trace':trace}
  if tick==limit:return {'status':'BOUND_EXHAUSTED','steps':tick,'state':q,'head':h,'one_cells':sorted(ones)}
  trace.append([q,h,b,w,d,z])
  if w:ones.add(h)
  else:ones.discard(h)
  q=z;h+=d

def main():
 ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('sites',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--all-failures',action='store_true');a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 T=s.r.table(a.table);sites=json.loads(a.sites.read_text());states={q for q,b in T};assert all((q,b)in T for q in states for b in(0,1));assert{z for w,d,z in T.values()}-states=={254}
 leaves={pc for pc,op,arg in sites};prefixes={pc[:i]for pc in leaves for i in range(len(pc))};assert not leaves&prefixes;assert len(leaves)==len(sites);assert all(p+b in leaves|prefixes for p in prefixes for b in('0','1'))
 m={int(k):int(v)for k,v in json.loads(MAPPATH.read_text()).items()}
 for q in states|{254}:
  if q not in m:m[q]=q+1000
 assert len({m[q]for q in states|{254}})==len(states)+1
 L={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()}
 st=startup(T);(a.output/'startup.json').write_text(json.dumps(st,indent=2)+'\n');print('STARTUP',st['status'],st['steps'],flush=True)
 begun=time.monotonic();fail=[];cases=[];blocks=[]
 try:lemmas,blocks=s.prove_blocks(L)
 except Exception as e:fail.append({'block_failure':str(e)});lemmas={}
 if not fail:
  for i,site in enumerate(sites):
   for positive in((False,True)if site[1]=='CD'else(False,)):
    try:
     ans=s.case(L,lemmas,site,positive);ans['rows']=sorted(ans['rows']);ans.pop('trace');cases.append({'site_index':i,'positive':positive,**ans})
    except Exception as e:
     fail.append({'site_index':i,'site':site,'positive':positive,'reason':str(e)});print('NOT_PROVED',fail[-1],flush=True)
     if not a.all_failures:break
   if fail and not a.all_failures:break
   if(i+1)%1000==0:print('SITE',i+1,'CASES',len(cases),'SECONDS',round(time.monotonic()-begun,3),flush=True)
 total=sum(2 if x[1]=='CD' else 1 for x in sites)
 report={'status':'UNIVERSAL_MATHEMATICAL_PASS'if not fail and len(cases)==total else'NOT_PROVED','table_sha256':digest(a.table),'sites_sha256':digest(a.sites),'checker_sha256':digest(Path(s.__file__)),'helper_sha256':digest(Path(s.r.__file__)),'working_states':len(states),'site_count':len(sites),'expected_cases':total,'proved_cases':len(cases),'failures':fail,'blocks':blocks,'seconds':time.monotonic()-begun,'startup_status':st['status'],'source_semantics':'Separate obligation. Quantified runtime certificate only.','scope':'All natural primary values at each guard; arbitrary natural gap; nonempty arbitrary finite spare list; complete zero exterior. Induction over unary scans and list length. Not proof-assistant kernel checked.'}
 (a.output/'runtime.json').write_text(json.dumps(report,indent=2)+'\n');(a.output/'runtime_cases.json').write_text(json.dumps(cases,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k not in('blocks','failures')},indent=2),flush=True)
if __name__=='__main__':main()
