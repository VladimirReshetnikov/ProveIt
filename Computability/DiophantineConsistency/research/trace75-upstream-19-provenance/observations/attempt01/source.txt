#!/usr/bin/env python3
"""Check 19 candidate producer receipts against selected explicit imports; no Lean."""
from hashlib import sha256
from pathlib import Path
import json,re,sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
INV=D/'research/trace75-upstream-141-inventory/observations/attempt01/stdout'
FINAL=D/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json'
PINS={INV:'87c27b168b3d242214d75e8de5c4165dd2c7ac9005ac680c6bc812558dbd8575',
      FINAL:'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c'}
def need(b,m):
    if not b:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PINS.items():need(sha(p)==h,'input drift '+str(p))
inv=json.loads(INV.read_text());final=json.loads(FINAL.read_text());project=final['selected_project'];outside=final['selected_outside']
need(inv['status']=='PASS' and final['status']=='PASS','input status')
records=[];edges=0;external=[]
for x in inv['records']:
    if x['exact_producer_in_six_runs'] or not x['prior_capture'] or not x['prior_capture']['all_companions_match'] or not x['prior_candidate_receipts']:continue
    project_imports={d for d in x['selected_header'] if d in project}
    compared={e['module'] for r in x['prior_candidate_receipts'] for e in r['recorded_direct_comparisons'] if e.get('matches')}
    if not project_imports<=compared:continue
    n=x['module'];need(len(x['prior_candidate_receipts'])==1,'multiple candidate receipts '+n)
    candidate=x['prior_candidate_receipts'][0];rp=Path(candidate['path']);need(sha(rp)==candidate['sha256'],'receipt drift '+n)
    receipt=json.loads(rp.read_text());need(receipt['exit']==0 and receipt['reason'] is None,'producer status '+n)
    need(receipt['pins']==receipt['after'],'producer pins changed '+n)
    need(receipt['direct_imports']==receipt['direct_imports_after'],'direct imports changed '+n)
    output=Path(receipt['output_root'])/(n.replace('.','/')+'.olean')
    need(output.is_file() and str(output.resolve())==x['selected_realpath'] and sha(output)==receipt['object_sha256']==x['selected_olean_sha256'],'selected output mismatch '+n)
    snapshot=rp.parent/'source.txt';copy=Path(receipt['command'][5]);source_hash=receipt['pins']['source']
    need(snapshot.is_file() and copy.is_file() and sha(snapshot)==sha(copy)==source_hash,'producer source drift '+n)
    source_imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',snapshot.read_text(),re.M)
    need(source_imports==[d for d in x['selected_header'] if d!='Init'],'source/header mismatch '+n)
    for ext in ['stdout','stderr']:
        p=rp.parent/ext;need(p.is_file() and sha(p)==receipt[ext+'_sha256'],'log drift '+n+' '+ext)
    direct=receipt['direct_imports'];need({d['module'] for d in direct}==set(source_imports),'explicit import coverage mismatch '+n)
    selected_edges=[]
    for dep in direct:
        target=project.get(dep['module']) or outside.get(dep['module']);p=Path(dep['path'])
        need(target is not None and p.is_file() and sha(p)==dep['sha256']==target['.olean']['sha256'],'selected import mismatch '+n+' '+dep['module'])
        if dep['module'] in outside:external.append([n,dep['module']])
        selected_edges.append({'module':dep['module'],'producer_path':str(p),'producer_realpath':str(p.resolve()),
                               'selected_realpath':target['.olean']['resolved'],'olean_sha256':dep['sha256']})
        edges+=1
    records.append({'module':n,'receipt':str(rp),'receipt_sha256':candidate['sha256'],'output_realpath':str(output.resolve()),
                    'output_sha256':receipt['object_sha256'],'source_snapshot':str(snapshot),'source_sha256':source_hash,
                    'copied_source':str(copy),'explicit_imports':selected_edges,
                    'implicit_init_in_header':'Init' in x['selected_header']})
need(len(records)==19,'strongest subset size changed')
for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
print(json.dumps({'status':'PASS','summary':{'records':len(records),'explicit_direct_olean_edges':edges,
 'explicit_outside_edges':external},'records':records,
 'scope':'capture-relative explicit direct .olean records only; implicit Init, companion bundles, package transitive/dynamic ancestry and the other 122 inputs are not authenticated'},sort_keys=True))
