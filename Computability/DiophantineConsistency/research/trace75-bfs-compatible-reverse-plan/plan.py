#!/usr/bin/env python3
"""Freeze source and accepted-receipt evidence only; never read live parent output."""
from hashlib import sha256
from pathlib import Path
import json,re,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
old=D/'research/trace75-reverse-fresh-provider-plan/observations/plan-attempt01/result.json'
pin='486a30360cc6c0ef5fd39f68d33227ee5022518717d216ce2539e29e3bd07f69'
sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
if sha(old)!=pin:raise SystemExit('source plan pin changed')
chosen={'Trace75GenericCarrier':'carrier-attempt01','Trace75SeedOffset':'offset-attempt01','Trace75UnscaledReverseData':'data-attempt02','Trace75OldTraceMap':'map-attempt01','Trace75OldTraceOutput':'output-attempt01','Trace75PositiveTraceShift':'shift-attempt02','Trace75NaturalTraceShift':'natural-attempt02','Trace75OldTracePositiveMap':'positive-attempt02','Trace75OldTracePartsJoin':'join-attempt01','Trace75NaturalPartsBinding':'binding-attempt03','Trace75UnscaledReverseGraph':'data-attempt04','Trace75PackingReverseGraph':'data-attempt01','Trace75BFSHaltGraph':'directbfshalt80-attempt03'}
p=json.loads(old.read_text());names=[r['module'] for r in p['stages']];assert len(names)==13 and set(names)==set(chosen);rows=[];seen=set()
for row in p['stages']:
 n=row['module'];src=Path(row['source']);o=src.parent/'observations'/chosen[n];receipt=o/'terminal.json';r=json.loads(receipt.read_text());out=o/'stdout';err=o/'stderr';snapshot=o/'source.txt'
 assert sha(src)==sha(snapshot)==row['source_sha256'] and r['exit']==0 and r['reason'] is None and r['object_sha256'] and sha(out)==r['stdout_sha256'] and sha(err)==r['stderr_sha256']
 text=out.read_text();reports=re.findall(r'^#print axioms\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M);assert len(reports)==1
 axioms='[propext, Quot.sound]' if n in ('Trace75OldTraceMap','Trace75OldTraceOutput') else '[propext, Classical.choice, Quot.sound]'
 assert text==f"'{reports[0]}' depends on axioms: {axioms}\n" and not err.read_text()
 assert all(v['kind']!='stage' or k in seen for k,v in row['direct'].items());seen.add(n)
 rows.append({'module':n,'source':str(src),'source_sha256':sha(src),'snapshot':str(snapshot),'snapshot_sha256':sha(snapshot),'receipt':str(receipt),'receipt_sha256':sha(receipt),'stdout':str(out),'stdout_sha256':sha(out),'stderr':str(err),'stderr_sha256':sha(err),'historical_object_sha256':r['object_sha256'],'imports':row['imports'],'prior_direct':row['direct'],'expected_stdout':text})
result={'status':'PASS','scope':'source and historical receipt pinning only; no access to live parent provider, no replay, no ancestry claim','historical_direct_plan':str(old),'historical_direct_plan_sha256':pin,'planner_sha256':sha(__file__),'stages':rows}
o=H/'observations/source-plan-attempt01';o.mkdir(parents=True,exist_ok=False);(o/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':'PASS','stages':len(rows),'sha256':sha(o/'result.json')}))
