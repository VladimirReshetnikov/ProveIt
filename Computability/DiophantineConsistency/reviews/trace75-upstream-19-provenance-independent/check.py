from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2];h=D/'research/trace75-upstream-19-provenance';o=h/'observations/attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
assert sha(h/'check.py')==sha(o/'source.txt')=='2195352d4a31e84e49e74b37f2cf322e3dedf30b989b4dc158525ceba3ad809b';assert sha(o/'terminal.json')=='9f5bc341d45234f151319ea2a113f181184debc7a89bca201491bd7151b56ba7' and sha(o/'stdout')=='d9e3020b3a928aefdbc7c4601a023c6f1b40d0930d4ad4f5229d4eac36555eb3'
t=load(o/'terminal.json');assert t['exit']==0 and t['checker_sha256']==sha(h/'check.py') and t['stdout_sha256']==sha(o/'stdout') and t['stderr_sha256']==sha(o/'stderr')
inv=D/'research/trace75-upstream-141-inventory/observations/attempt01/stdout';fin=D/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json';assert sha(inv)=='87c27b168b3d242214d75e8de5c4165dd2c7ac9005ac680c6bc812558dbd8575' and sha(fin)=='b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c'
original=load(inv);final=load(fin);outputs=load(o/'stdout');assert original['status']==final['status']==outputs['status']=='PASS';project=final['selected_project'];outside=final['selected_outside'];selected={}
for x in original['records']:
 if x['exact_producer_in_six_runs'] or x['prior_capture'] is None or not x['prior_capture']['all_companions_match'] or not x['prior_candidate_receipts']:continue
 proj={d for d in x['selected_header'] if d in project};cmp={e['module'] for r in x['prior_candidate_receipts'] for e in r['recorded_direct_comparisons'] if e.get('matches')}
 if proj<=cmp:selected[x['module']]=x
records={r['module']:r for r in outputs['records']};assert set(records)==set(selected) and len(records)==19
edges=0;external=[]
for n,x in selected.items():
 rr=records[n];assert len(x['prior_candidate_receipts'])==1;candidate=x['prior_candidate_receipts'][0];receipt=Path(candidate['path']);assert str(receipt)==rr['receipt'] and sha(receipt)==candidate['sha256']==rr['receipt_sha256'];a=load(receipt)
 assert a['exit']==0 and a['reason'] is None and a['pins']==a['after'] and a['direct_imports']==a['direct_imports_after']
 out=Path(a['output_root'])/(n.replace('.','/')+'.olean');assert out.is_file() and str(out.resolve(strict=True))==x['selected_realpath']==rr['output_realpath'] and sha(out)==a['object_sha256']==x['selected_olean_sha256']==rr['output_sha256']
 snapshot=receipt.parent/'source.txt';copied=Path(a['command'][5]);assert str(snapshot)==rr['source_snapshot'] and str(copied)==rr['copied_source'] and sha(snapshot)==sha(copied)==a['pins']['source']==rr['source_sha256']
 for ext in ('stdout','stderr'):assert sha(receipt.parent/ext)==a[ext+'_sha256']
 imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',snapshot.read_text(),re.M);assert imports==[dep for dep in x['selected_header'] if dep!='Init'];assert rr['implicit_init_in_header']==('Init' in x['selected_header']);direct=a['direct_imports'];assert {e['module'] for e in direct}==set(imports) and len(rr['explicit_imports'])==len(direct)
 for entry,reported in zip(direct,rr['explicit_imports']):
  dep=entry['module'];target=project.get(dep) or outside.get(dep);p=Path(entry['path']);assert target is not None and p.is_file() and sha(p)==entry['sha256']==target['.olean']['sha256'];assert reported=={'module':dep,'producer_path':str(p),'producer_realpath':str(p.resolve()),'selected_realpath':target['.olean']['resolved'],'olean_sha256':entry['sha256']};edges+=1
  if dep in outside:external.append([n,dep])
assert edges==56 and len(external)==4 and sorted(external)==sorted(outputs['summary']['explicit_outside_edges']);print('PASS independent selection 19 producer receipts, sources/logs, output realpaths and 56 explicit .olean edges (52 project, 4 outside)')
