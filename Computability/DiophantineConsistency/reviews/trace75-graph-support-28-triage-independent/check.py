from pathlib import Path
import hashlib,json,re,collections
D=Path(__file__).resolve().parents[2];h=D/'research/trace75-graph-support-28-triage';o=h/'observations/attempt01';R=D/'research';overlay=Path('/tmp/compact44-graph-support-join-01')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def imports(p):return re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',p.read_text(),re.M)
assert sha(h/'check.py')==sha(o/'source.txt')=='2efe676d2fd92626cb878628f6cf948547fcce2c64b282f3effa339856a29fdf';assert sha(o/'terminal.json')=='6b2dcfae50c3ccee1f60657691cd809df9d15319508c16a06a83e476f95dcb5a' and sha(o/'stdout')=='a1f701226ce2c5c1f9eef7b627f4d6ce6aa494bc4689c846d8617f172d750570';t=load(o/'terminal.json');assert t['exit']==0 and t['checker_sha256']==sha(h/'check.py') and t['stdout_sha256']==sha(o/'stdout') and t['stderr_sha256']==sha(o/'stderr')
ps=[R/'trace75-upstream-141-inventory/observations/attempt01/stdout',R/'trace75-upstream-19-provenance/observations/attempt01/stdout',R/'trace75-upstream-ten-runner-triage/observations/attempt03/stdout',R/'trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json'];ds=['87c27b168b3d242214d75e8de5c4165dd2c7ac9005ac680c6bc812558dbd8575','d9e3020b3a928aefdbc7c4601a023c6f1b40d0930d4ad4f5229d4eac36555eb3','d31977de4a6c5c724f52c9b43a1caeb173a2a979a5834ab8c68b87ee4aa3a7be','b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c'];assert all(sha(p)==d for p,d in zip(ps,ds));inv,nineteen,ten,final=map(load,ps);output=load(o/'stdout');records={r['module']:r for r in output['records']};known={x['module'] for x in inv['records'] if x['exact_producer_in_six_runs']}|{x['module'] for x in nineteen['records']}|{x['module'] for x in ten['records']}|{'ScaledOffsetGeneric'};subset={x['module']:x for x in inv['records'] if x['module'] not in known and Path(x['selected_realpath']).parent==overlay/'lib/DiophantineConsistency'};assert len(subset)==28 and set(subset)==set(records)
workspace=list((R/'ordinary12-ipra-bridge').glob('*/*.lean'));counts=collections.Counter();missing=[]
for n,x in subset.items():
 r=records[n];chosen=final['selected_project'][n]['.olean'];obj=Path(chosen['path']);assert str(obj.resolve(strict=True))==x['selected_realpath']==r['selected_realpath'] and sha(obj)==x['selected_olean_sha256']==r['selected_olean_sha256'];assert r['selected_header']==x['selected_header']==final['serialized_headers'][n];short=n.split('.')[-1];src=overlay/(short+'.lean')
 if src.is_file():
  counts['source']+=1;sh=sha(src);assert r['overlay_source']=={'path':str(src),'sha256':sh};assert imports(src)==[d for d in x['selected_header'] if d!='Init'];matches=[p for p in workspace if p.name==short+'.lean' and sha(p)==sh];assert len(matches)==1 and r['workspace_matches']==[str(matches[0])]
  candidates=[]
  for p in sorted(matches[0].parent.rglob('*.json')):
   try:raw=p.read_text()
   except (OSError,UnicodeDecodeError):continue
   if sh in raw and x['selected_olean_sha256'] in raw:candidates.append({'path':str(p),'sha256':sha(p),'contains_exact_output_realpath':x['selected_realpath'] in raw})
  assert r['local_observation_json_dual_hash_candidates']==candidates
  if candidates:counts['candidates']+=1;assert not any(c['contains_exact_output_realpath'] for c in candidates)
 else:
  missing.append(n);assert r['overlay_source'] is None and not r['workspace_matches'];assert short=='ArithmeticPackingBlocks';p=D/'Lean/DiophantineConsistency/ArithmeticPackingBlocks.lean';assert imports(p)==[d for d in x['selected_header'] if d!='Init'] and r['workspace_candidate_only']=={'path':str(p),'sha256':sha(p)}
 logs=[{'path':str(p),'sha256':sha(p)} for p in sorted(overlay.glob(short+'*.log')) if p.is_file()];assert r['overlay_logs']==logs
 if logs:counts['logs']+=1
assert counts=={'source':27,'logs':22,'candidates':7} and missing==['DiophantineConsistency.ArithmeticPackingBlocks'];print('PASS 28 selected objects; 27 current source/header unique matches, 1 absent, 22 named log groups, 7 dual-hash JSON candidate groups with no exact output path')
