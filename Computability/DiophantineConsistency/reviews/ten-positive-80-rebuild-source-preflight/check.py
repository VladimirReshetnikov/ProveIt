#!/usr/bin/env python3
"""Compare 114 candidate sources to their retained producer source pins."""
from hashlib import sha256
from pathlib import Path
import json
H=Path(__file__).resolve().parent;D=H.parents[1]
SURVEY=D/'reviews/ten-positive-80-nine-prefix-producer-audit/observations/survey01.json'
SCAN=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'
SINGLE=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/producer-audit01.json'
STAGE=D/'reviews/ten-positive-80-staged-producer-audit/observations/attempt01.json'
NINE=D/'reviews/ten-positive-80-nine-prefix-producer-audit/observations/attempt01.json'
OUT=H/'observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(not OUT.exists(),'output exists')
s=json.loads(SURVEY.read_text());x=json.loads(SCAN.read_text());single=json.loads(SINGLE.read_text());stage=json.loads(STAGE.read_text());nine=json.loads(NINE.read_text())
need(len(s['ordered'])==114,'unexpected cone size')
records={}
for n in s['ordered']:
 candidates=s['sources_by_basename'][n]; need(len(candidates)==1,'ambiguous source '+n)
 source=Path(candidates[0]); current=sha(source)
 if n in single['matched']:
  receipt=Path(single['matched'][n]['receipt']); need(sha(receipt)==single['matched'][n]['receipt_sha256'],'receipt drift '+n)
  expected=json.loads(receipt.read_text()).get('pins',{}).get('source'); kind='single'
 elif n in stage['cases']:
  expected=stage['cases'][n]['source_sha256'];kind='stage'
 elif n in nine['cases']:
  expected=nine['cases'][n]['source_sha256'];kind='nine-prefix'
 else:raise RuntimeError('no source pin '+n)
 need(expected==current,'source hash drift '+n)
 imports=[]
 for line in source.read_text().splitlines():
  if line.startswith('import '):imports.extend(line[7:].split())
 need(set(imports)==set(x['fresh_headers'][n])-{'Init'},'source/header imports differ '+n)
 records[n]={'source':str(source),'sha256':current,'producer_kind':kind,'source_imports':imports}
result={'status':'PASS','inputs':{str(p):sha(p) for p in (SURVEY,SCAN,SINGLE,STAGE,NINE)},'ordered':s['ordered'],'sources':records,
        'scope':'candidate source bytes match retained producer source pins and header import names; no rebuild, transitive provenance or source-theorem replay'}
OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','sources':len(records),'sha256':sha(OUT)},sort_keys=True))
