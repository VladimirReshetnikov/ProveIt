#!/usr/bin/env python3
"""Fresh all-natural literal-table proof, compared with the released case census."""
from pathlib import Path
import json,gzip,sys,time,hashlib,argparse
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code/runtime'))
import symbolic_runtime as S

def replay(out):
 out.mkdir(parents=True,exist_ok=False)
 T=S.r.table(ROOT/'machine/zc215.native.tm');sites=json.loads((ROOT/'source/zc215.sites.json').read_text())
 m={int(k):int(v)for k,v in json.loads((ROOT/'code/runtime/legacy_mapping.json').read_text()).items()}
 for q in {q for q,b in T}|{254}:
  if q not in m:m[q]=q+1000
 assert len(set(m[q]for q in {q for q,b in T}|{254}))==216
 L={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()}
 lemmas,blocks=S.prove_blocks(L);cases=[];rows=set();start=time.monotonic()
 for i,site in enumerate(sites):
  for positive in((False,True)if site[1]=='CD'else(False,)):
   ans=S.case(L,lemmas,site,positive,append=0)
   rows.update(ans['rows']);ans['rows']=sorted(ans['rows']);ans.pop('trace')
   cases.append({'site_index':i,'positive':positive,**ans})
  if (i+1)%1000==0:print('SOURCE_SITES',i+1,'GUARDED_CASES',len(cases),flush=True)
 for block in blocks:
  for event in block['trace']:
   if event[0]!='list':rows.add(tuple(event[1][:2]))
 inv={v:k for k,v in m.items()}
 record={'status':'ALL_NATURAL_RUNTIME_PASS','cases':len(cases),'rules':sum(c['symbolic_steps']for c in cases),'minimum_duration':min(c['duration'][0]for c in cases),'native_rows':sorted((inv[q],b)for q,b in rows),'row_count':len(rows),'blocks':blocks,'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256((ROOT/'source/zc215.sites.json').read_bytes()).hexdigest(),'table_sha256':hashlib.sha256((ROOT/'machine/zc215.native.tm').read_bytes()).hexdigest()}
 stored=json.loads(gzip.decompress((ROOT/'evidence/runtime_cases.json.gz').read_bytes()))
 assert json.loads(json.dumps(cases))==stored
 old=json.loads((ROOT/'evidence/runtime.json').read_text())
 for k in record:
  if k!='seconds':assert json.loads(json.dumps(record[k]))==old[k],k
 (out/'runtime_cases.json.gz').write_bytes(gzip.compress((json.dumps(cases,separators=(',',':'))+'\n').encode(),mtime=0))
 (out/'runtime.json').write_text(json.dumps(record,indent=2)+'\n')
 return {k:v for k,v in record.items()if k not in('blocks','native_rows')}
if __name__=='__main__':
 if not __debug__:raise RuntimeError('Run with assertions enabled')
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args();print(json.dumps(replay(a.out),indent=2))
