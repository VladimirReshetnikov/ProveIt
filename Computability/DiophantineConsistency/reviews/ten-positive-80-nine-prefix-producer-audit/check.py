#!/usr/bin/env python3
"""Check six matching nine-variable prefix receipts against the 80 closure."""
from hashlib import sha256
from pathlib import Path
import json

H=Path(__file__).resolve().parent; D=H.parents[1]
SCAN=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'
OUT=H/'observations/attempt01.json'
cases={
 'DiophantineConsistency.DiscreteOrderedRingFacts':'nine-variable-ipra-stages-3-5-author-audit/author/receipts/003.json',
 'DiophantineConsistency.ModelArithmetic':'nine-variable-ipra-stages-3-5-author-audit/author/receipts/004.json',
 'DiophantineConsistency.ModelExponentialCongruence':'nine-variable-ipra-stages-3-5-author-audit/author/receipts/005.json',
 'DiophantineConsistency.ModelRatioBounds':'nine-variable-ipra-stages-6-9-author-observation/author/receipts/006.json',
 'DiophantineConsistency.ArithmeticPellPigeonhole':'nine-variable-ipra-stages-6-9-author-observation/author/receipts/008.json',
 'DiophantineConsistency.ModelProductPell':'nine-variable-ipra-stages-6-9-author-observation/author/receipts/009.json',
}
def sha(p): return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b: raise RuntimeError(m)
need(not OUT.exists(),'output exists')
x=json.loads(SCAN.read_text());need(x['status']=='PASS','closure failed'); out={}; drifts=[]
for name,rel in cases.items():
 f=D/'reviews'/rel; rec=json.loads(f.read_text()); chosen=x['project'][name]['selected']
 need(rec['status']=='PASS' and rec['module']==name,'receipt failure '+name)
 need(rec['output']['sha256']==chosen['sha256']==sha(chosen['path']),'output mismatch '+name)
 source=next(Path(a) for a in rec['command'] if a.endswith('.lean'))
 need(source.is_file() and sha(source)==rec['source_sha256'],'source mismatch '+name)
 log=Path(rec['log']); need(log.is_file() and sha(log)==rec['log_sha256'],'log mismatch '+name)
 imports=set(x['fresh_headers'][name]); pins=rec['direct'];need(set(pins)==imports,'header/pin imports differ '+name)
 compared={}
 for dep, pin in pins.items():
  final=x['project'].get(dep,{}).get('selected',x['outside'].get(dep))
  need(final is not None,'missing final dependency '+name+' '+dep)
  p=Path(pin['path']); now=sha(p) if p.is_file() else None
  entry={'producer_recorded':pin['record'],'producer_path':pin['path'],'producer_path_current_sha256':now,
         'final_selected':final,'equal_to_final':final['sha256']==pin['record']['sha256']}
  compared[dep]=entry
  if not entry['equal_to_final']: drifts.append({'module':name,'dependency':dep,**entry})
 out[name]={'receipt':str(f),'receipt_sha256':sha(f),'source':str(source),
            'source_sha256':sha(source),'output':chosen,'direct_imports_compared':compared,
            'log':str(log),'log_sha256':sha(log),'warning_policy':rec.get('warning_policy')}
result={'status':'COMPARED_WITH_DRIFTS','closure_sha256':sha(SCAN),'cases':out,'drifts':drifts,
        'scope':'retained producer source/output/log and direct-import pins versus final selected closure; transitive/package/dynamic ancestry inherited'}
OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'COMPARED_WITH_DRIFTS','cases':len(out),'drifts':len(drifts),'result_sha256':sha(OUT)},sort_keys=True))
