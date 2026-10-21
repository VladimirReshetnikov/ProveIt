"""Exact symbolic runtime replay for a supplied native-label table and source.

The quantified calculus is inherited. This driver binds it to explicit bytes;
the user must separately prove source calibration and blank initialization.
"""
from pathlib import Path
import argparse,json,hashlib,time,gzip,sys
import symbolic_runtime as rt
ap=argparse.ArgumentParser();ap.add_argument('--table',type=Path,required=True);ap.add_argument('--sites',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
assert __debug__ and not sys.flags.optimize
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
T=rt.r.table(a.table);sites=json.loads(a.sites.read_text());W={q for q,b in T}
assert len(T)==2*len(W)and{z for w,d,z in T.values()}-W=={254}
M={int(q):v for q,v in json.loads(Path(__file__).with_name('legacy_mapping.json').read_text()).items()}
for q in W|{254}:M.setdefault(q,q+1000)
assert len(set(M.values()))==len(M)
V={(M[q],b):(w,d,M[t])for(q,b),(w,d,t)in T.items()}
started=time.monotonic();lemmas,blocks=rt.prove_blocks(V);cases=[];used=set()
result={'table_sha256':sha(a.table),'source_sha256':sha(a.sites),'working_states':len(W),'transition_rows':len(T),'expected_cases':sum(2 if o=='CD' else 1 for pc,o,r in sites),'engine_sha256':sha(Path(rt.__file__)),'helper_sha256':sha(Path(rt.r.__file__)),'scope':'Independent arbitrary natural register values and gap; arbitrary nonempty finite spare list. Whole tape, positive finite durations. Ordinary symbolic proof, not a proof-assistant kernel certificate.'}
try:
 for i,site in enumerate(sites):
  for pos in ([False,True]if site[1]=='CD'else[False]):
   x=rt.case(V,lemmas,site,pos);used.update(x.pop('rows'));x.pop('trace');cases.append({'index':i,'positive':pos,**x})
  if len(cases)%500<2:print('PROVED',len(cases),round(time.monotonic()-started,2),flush=True)
 result['status']='ALL_PRIMITIVE_INTERFACES_PROVED'
except Exception as e:result.update(status='NOT_PROVED',index=i,site=site,positive=pos,error=str(e))
result.update(cases=len(cases),symbolic_steps=sum(x['symbolic_steps']for x in cases),seconds=time.monotonic()-started,minimum_duration_constant=min(x['duration'][0]for x in cases)if cases else None,used_rows=len(used),blocks=blocks)
a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
with gzip.open(a.output.with_suffix('.cases.json.gz'),'wt')as f:json.dump(cases,f,separators=(',',':'))
print(json.dumps({k:v for k,v in result.items()if k!='blocks'},indent=2),flush=True)
sys.exit(0 if result['status']=='ALL_PRIMITIVE_INTERFACES_PROVED' else 1)
