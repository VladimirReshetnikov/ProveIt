#!/usr/bin/env python3
"""Read-only compare new captured project selections to the producer receipt pins."""
from pathlib import Path
from hashlib import sha256
import json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
h=Path(__file__).resolve().parent;d=h.parents[1];capture=h/'observations/attempt01/result.json';receipt=d/'research/ten-positive-80-bfs-displayed-full-ipra/observations/attempt01/terminal.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
need(sha(capture)=='1b41178b0123d25e8814b6d430c1f996c90765fc5f1517283d4248b787dc6e1b','capture changed')
need(sha(receipt)=='bd210ff5388f1353c65821031bde96e55a42ed20dac592ad42fe5a5943092ece','receipt changed')
c=json.loads(capture.read_text());r=json.loads(receipt.read_text());need(c['status']=='PASS_CAPTURE' and r['status']=='PASS','not passed')
expected={Path(p).stem:{'path':p,'sha256':v['sha256'],'resolved':v['resolved']} for p,v in r['pins'].items() if p.endswith('.olean')}
expected['BFSDisplayedFullIPRA']={'path':r['output'],'sha256':r['output_sha256'],'resolved':str(Path(r['output']).resolve())}
rows=[]
for n in c['new_project']:
 need(n in expected,'new module lacks producer pin '+n);e=expected[n];record=c['closure']['project'][n];actual=record['companions']['.olean']
 need(record['path']==e['path'] and actual['sha256']==e['sha256'] and actual['resolved']==e['resolved'],'selected path/hash mismatch '+n)
 need(sha(e['path'])==e['sha256'] and str(Path(e['path']).resolve())==e['resolved'],'live path changed '+n)
 rows.append({'module':n,'path':e['path'],'sha256':e['sha256'],'resolved':e['resolved'],'imports':record['imports']})
need(len(rows)==12,'unexpected new count')
print(json.dumps({'status':'PASS','new_selected':rows,'source_capture_sha256':sha(capture),'source_receipt_sha256':sha(receipt),'scope':'new module selected olean path/hash/resolved-target vs root receipt; no new Lean or historical producer/package ancestry audit'},indent=2,sort_keys=True))
