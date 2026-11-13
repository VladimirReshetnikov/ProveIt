#!/usr/bin/env python3
"""Triage 141 captured cone-boundary objects; no Lean or upstream rebuild."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json,sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
INPUTS={
 'research/ten-positive-80-coherent-rebuild/observations/attempt04/result.json':'e1ccee0f9c5fdc14cde89368925cb56f41d6acbe5c89a41c9e2bab798184582b',
 'research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json':'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559',
 'research/trace75-bfs-compatible-provider-rebuild/observations/attempt01/result.json':'04cd437011c9a8b753a310da6c7691f229f9758b9050fdba9b61b812697fbc3c',
 'research/trace75-bfs-compatible-reverse-rebuild/observations/attempt01/result.json':'9cf2209e033a0baeab5e1ecac3c9aee0f13afffade6c6a716a7661eeff17ba49',
 'research/trace75-bfs-compatible-forward-rebuild/observations/attempt01/result.json':'f8d6388911e101a7dfae2547907bc6f9245950fa953c3a4769eff00c140fc3d8',
 'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json':'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c',
 'research/trace75-cone-source-inventory/observations/attempt03/stdout':'473df595296a18b16836906d2dd6daf4b740fea1e56014e1bebaaabd9fececbf',
 'research/direct-bfs-80-ipra-serialized-audit/observations/attempt01/result.json':'beca7bfd182f49fb0640ed2b49bff33aa2aa8e1ec09bb1fa1d632b2f06ab9883'}
PATHS=list(INPUTS)[:6];FINAL=PATHS[-1];INVENTORY=list(INPUTS)[6];OLD=list(INPUTS)[7]
def need(b,m):
    if not b:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def hashes(b):return {k:None if v is None else v['sha256'] for k,v in b.items()}
def read(p):return json.loads((D/p).read_text())
def check_record(b):
    for item in b.values():
        if item is None:continue
        p=Path(item['path']);need(p.is_file() and str(p.resolve(strict=True))==item['resolved'] and sha(p)==item['sha256'],'selected object drift '+str(p))
for p,h in INPUTS.items():need(sha(D/p)==h,'input drift '+p)
final=read(FINAL);inv=read(INVENTORY);old=read(OLD);upstream=set(inv['upstream_project'])
need(final['status']=='PASS' and inv['status']=='PASS' and old['status']=='PASS_CAPTURE' and len(upstream)==141,'input status/count')
matches={}
for path in PATHS:
    producer=read(path);need(producer['status']=='PASS','producer result status '+path)
    for stage in producer['stages']:
        n=stage['module'];out=stage.get('object') or stage.get('output');selected=final['selected_project'].get(n)
        if n not in upstream or selected is None:continue
        if out['.olean']['resolved']!=selected['.olean']['resolved'] or hashes(out)!=hashes(selected):continue
        need(n not in matches and stage['exit']==0 and stage['reason'] is None,'ambiguous/failed matching producer '+n)
        check_record(out);matches[n]={'result':path,'stage':stage['index'],'output_realpath':out['.olean']['resolved'],
                                     'output_sha256':out['.olean']['sha256']}
records=[];counts=Counter()
oldproject=old['closure']['project'];receipts=old['producer_direct']
for n in sorted(upstream):
    selected=final['selected_project'][n];check_record(selected);oldrec=oldproject.get(n)
    category='absent';old_data=None
    if oldrec is not None:
        category='all_companions_match' if hashes(oldrec['companions'])==hashes(selected) else 'companion_difference'
        old_data={'olean_sha256':oldrec['record']['sha256'],'olean_realpath':oldrec['record'].get('resolved') or oldrec['record'].get('real_path'),
                  'all_companions_match':category=='all_companions_match'}
    candidates=[]
    for item in receipts.get(n,[]):
        p=Path(item['receipt']);need(p.is_file() and sha(p)==item['receipt_sha256'],'candidate receipt drift '+n)
        candidates.append({'path':str(p),'sha256':item['receipt_sha256'],
                           'recorded_direct_comparisons':item['direct_imports_compared']})
    counts['prior_'+category]+=1
    if n in matches:counts['exact_selected_producer_from_six_runs']+=1
    if candidates:counts['prior_capture_has_candidate_receipt']+=1
    records.append({'module':n,'selected_realpath':selected['.olean']['resolved'],'selected_olean_sha256':selected['.olean']['sha256'],
      'selected_companion_hashes':hashes(selected),'selected_header':final['serialized_headers'][n],
      'exact_producer_in_six_runs':matches.get(n),'prior_capture':old_data,'prior_candidate_receipts':candidates})
need(len(records)==141,'coverage')
for p,h in INPUTS.items():need(sha(D/p)==h,'input changed '+p)
print(json.dumps({'status':'PASS','summary':dict(counts),'records':records,
 'scope':'selected object and candidate receipt triage; hash matches alone do not establish producer-time direct imports or transitive ancestry'},sort_keys=True))
