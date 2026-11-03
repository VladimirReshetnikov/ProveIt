from pathlib import Path
import ast,collections,hashlib,json,os
D=Path(__file__).resolve().parents[2];h=D/'research/trace75-upstream-141-inventory';obs=h/'observations/attempt01';src=h/'check.py'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def hs(b):return {k:None if v is None else v['sha256'] for k,v in b.items()}
assert sha(src)==sha(obs/'source.txt')=='0226c4646a85e4bc22f75ce1673960617fa7e3a1ee86e939e4266c98f54a5082';assert sha(obs/'terminal.json')=='94a001c50e462013f7576d3b2e3fe909aa6c62a882ebf3627dc9b569643d81a4';assert sha(obs/'stdout')=='87c27b168b3d242214d75e8de5c4165dd2c7ac9005ac680c6bc812558dbd8575'
t=load(obs/'terminal.json');assert t['exit']==0 and t['checker_sha256']==sha(src) and t['stdout_sha256']==sha(obs/'stdout') and t['stderr_sha256']==sha(obs/'stderr')
a=ast.parse(src.read_text());node=next(x for x in a.body if isinstance(x,ast.Assign) and any(isinstance(n,ast.Name) and n.id=='INPUTS' for n in x.targets));pins=ast.literal_eval(node.value);assert len(pins)==8
for path,hash in pins.items():assert sha(D/path)==hash
paths=list(pins);runs=[load(D/p) for p in paths[:6]];final=runs[-1];inv=load(D/paths[6]);old=load(D/paths[7]);output=load(obs/'stdout');records={r['module']:r for r in output['records']};assert len(records)==141 and set(records)==set(inv['upstream_project'])
selected_matches={}
for path,run in zip(paths,runs):
 assert run['status']=='PASS'
 for stage in run['stages']:
  n=stage['module'];obj=stage.get('object') or stage.get('output');selected=final['selected_project'].get(n)
  if n in records and selected is not None and obj['.olean']['resolved']==selected['.olean']['resolved'] and hs(obj)==hs(selected):
   assert n not in selected_matches and stage['exit']==0 and stage['reason'] is None
   selected_matches[n]=(path,stage)
counts=collections.Counter();nonexact_match=[];nonexact_cand=[];prior_diff=[]
for n,r in records.items():
 b=final['selected_project'][n];f=Path(b['.olean']['path']);assert f.is_file() and str(f.resolve(strict=True))==b['.olean']['resolved'];assert r['selected_realpath']==b['.olean']['resolved'] and r['selected_olean_sha256']==b['.olean']['sha256'] and r['selected_companion_hashes']==hs(b) and r['selected_header']==final['serialized_headers'][n]
 for suff,v in b.items():
  p=Path(str(f)[:-6]+suff)
  if v is None:assert not os.path.lexists(p)
  else:assert p.is_file() and str(p.resolve(strict=True))==v['resolved'] and sha(p)==v['sha256']
 match=selected_matches.get(n)
 if match:
  path,stage=match;capt=r['exact_producer_in_six_runs'];assert capt['result']==path and capt['stage']==stage['index'] and capt['output_realpath']==b['.olean']['resolved'] and capt['output_sha256']==b['.olean']['sha256'];counts['exact']+=1
 else:assert r['exact_producer_in_six_runs'] is None
 previous=old['closure']['project'].get(n)
 if previous is None:assert r['prior_capture'] is None;counts['absent']+=1;matching=False
 else:
  matching=hs(previous['companions'])==hs(b);capture=r['prior_capture'];assert capture['all_companions_match']==matching and capture['olean_sha256']==previous['record']['sha256'] and capture['olean_realpath']==(previous['record'].get('resolved') or previous['record'].get('real_path'))
  counts['match' if matching else 'diff']+=1
  if not matching:prior_diff.append(n)
  if matching and not match:assert capture['olean_realpath']==b['.olean']['resolved'];nonexact_match.append(n)
 candidates=old['producer_direct'].get(n,[]);capt=r['prior_candidate_receipts'];assert len(candidates)==len(capt)
 for a,c in zip(candidates,capt):assert c['path']==a['receipt'] and c['sha256']==a['receipt_sha256']==sha(a['receipt']) and c['recorded_direct_comparisons']==a['direct_imports_compared']
 if candidates:
  counts['candidates']+=1
  if not match and matching:nonexact_cand.append(n)
assert counts=={'exact':16,'match':126,'diff':1,'absent':14,'candidates':41} and prior_diff==['DiophantineConsistency.ArithmeticNegativeNorms'] and len(nonexact_match)==115 and len(nonexact_cand)==30
print('PASS exact 141 selected bundles/header records, 16 exact 6-run matches, 126/1/14 earlier bundle categories, 41 candidate receipt groups, and overlapping 115/30 classifications')
