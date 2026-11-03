#!/usr/bin/env python3
"""Compare the 12 new modules' serialized project imports with their producer pins."""
from pathlib import Path
from hashlib import sha256
import json,re,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
h=Path(__file__).resolve().parent;research=h.parent;capture=h/'observations/attempt01/result.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
need(sha(capture)=='1b41178b0123d25e8814b6d430c1f996c90765fc5f1517283d4248b787dc6e1b','capture changed')
c=json.loads(capture.read_text());mapping={
'BFSDisplayedFullIPRA':'ten-positive-80-bfs-displayed-full-ipra/observations/attempt01',
'BFSDisplayedHighIPRA':'ten-positive-80-bfs-displayed-high/observations/attempt01',
'BFSDisplayedLowInferredV4':'ten-positive-80-bfs-low-inferred/observations/attempt04',
'BFSDisplayedBetaIPRAV2':'ten-positive-80-bfs-displayed-beta/observations/attempt02',
'BFSHighSymbolic':'ten-positive-80-bfs-high-symbolic/observations/attempt01',
'BFSHighFlat':'ten-positive-80-bfs-high-flat/observations/attempt01',
'BFSDisplayed80IPRA':'ten-positive-80-bfs-displayed-ipra/observations/attempt01',
'BFSDisplayedSlots':'ten-positive-80-bfs-slots-lean/observations/attempt01',
'BFSHighRunsV2':'ten-positive-80-bfs-high-runs/observations/attempt02',
'BFSHighGeneric':'ten-positive-80-bfs-high-generic/observations/attempt01',
'BFSDisplayedKernelV4':'ten-positive-80-bfs-selectors-lean/observations/kernel-attempt04',
'BFSDisplayedSelectors':'ten-positive-80-bfs-selectors-lean/observations/attempt01'}
need(set(mapping)==set(c['new_project']),'new module set changed');rows=[];edge_count=0
for n,rel in mapping.items():
 p=research/rel/'terminal.json';r=json.loads(p.read_text());need(r['status']=='PASS' and r['exit']==0 and r['reason'] is None,'bad producer '+n)
 row=c['closure']['project'][n];need(r['output']==row['path'] and r['output_sha256']==row['record']['sha256'],'producer output mismatch '+n)
 sources=[(k,v) for k,v in r['pins'].items() if k.endswith('.lean')];need(len(sources)==1,'source pin count '+n)
 source,sourcepin=sources[0];need(sha(source)==sourcepin['sha256'] and str(Path(source).resolve())==sourcepin['resolved'],'source drift '+n)
 imports=re.findall(r'^import\s+(\S+)',Path(source).read_text(),re.M);serialized=[x for x in row['imports'] if x!='Init'];need(imports==serialized,'source/header import mismatch '+n)
 edges=[]
 for dep in serialized:
  dep_row=c['closure']['project'].get(dep);need(dep_row is not None,'unrecorded project direct '+n+' '+dep)
  path=dep_row['path'];pin=r['pins'].get(path);need(pin is not None,'un-pinned direct import '+n+' '+dep)
  need(pin['sha256']==dep_row['record']['sha256'] and pin['resolved']==dep_row['companions']['.olean']['resolved'],'direct pin mismatch '+n+' '+dep)
  edges.append({'module':dep,'path':path,'sha256':pin['sha256'],'resolved':pin['resolved']});edge_count+=1
 rows.append({'module':n,'receipt':str(p),'receipt_sha256':sha(p),'source':source,'source_sha256':sourcepin['sha256'],'direct_imports':edges})
print(json.dumps({'status':'PASS','modules':rows,'project_direct_edges':edge_count,'scope':'serialized project direct imports of the 12 new modules versus their retained producer object pins; outside, historical transitive and package ancestry inherited'},indent=2,sort_keys=True))
