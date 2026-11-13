from pathlib import Path
import json,hashlib,re
D=Path(__file__).resolve().parents[2];h=D/'research/trace75-upstream-scaled-offset-provenance';o=h/'observations/attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
assert sha(h/'check.py')==sha(o/'source.txt')=='3f35c84e4a4b0845e87fea9dde086072bb01babfa6c7ee05eeb9a15ed868ab1a'
assert sha(o/'terminal.json')=='c8d295ed11436af67c5bbbc673ea5794c3059edc0084fb1b4427ae7dc8e05049' and sha(o/'stdout')=='44dc03a3ccf92c985ccfe5a6b3da34b1dcdc97fbb509d1d7a4a9dbc99601c2fd'
t=load(o/'terminal.json');assert t['exit']==0 and t['checker_sha256']==sha(h/'check.py') and t['stdout_sha256']==sha(o/'stdout') and t['stderr_sha256']==sha(o/'stderr')
receipt=D/'research/ten-positive-scaled-offset-generic-prototype/observations/offset-attempt01/terminal.json';final=D/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json';triage=D/'research/trace75-upstream-141-inventory/observations/attempt01/stdout'
for p,d in [(receipt,'b65e6628a81a71aeac5481571e815c5ae5117dd09e68d3c7a4b2629251ab461e'),(final,'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c'),(triage,'87c27b168b3d242214d75e8de5c4165dd2c7ac9005ac680c6bc812558dbd8575')]:assert sha(p)==d
r=load(receipt);f=load(final);row=next(x for x in load(triage)['records'] if x['module']=='ScaledOffsetGeneric');reported=load(o/'stdout');name='ScaledOffsetGeneric';dep='DiophantineConsistency.ArithmeticPellCongruences'
assert r['exit']==0 and r['reason'] is None and r['pins']==r['after'];assert row['exact_producer_in_six_runs'] is None and row['prior_capture']['all_companions_match'];out=Path(r['output_root'])/(name+'.olean');selected=f['selected_project'][name]['.olean'];assert out.is_file() and str(out.resolve(strict=True))==selected['resolved']==reported['output_realpath'] and sha(out)==r['object_sha256']==selected['sha256']==reported['output_sha256']
src=receipt.parent/'source.txt';copy=Path(r['command'][5]);assert sha(src)==sha(copy)==r['pins']['source']==reported['source_sha256'];imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M);assert imports==[dep]==[x for x in f['serialized_headers'][name] if x!='Init']
for ext in ('stdout','stderr'):assert sha(receipt.parent/ext)==r[ext+'_sha256']
assert set(r['pins']['direct_imports'])=={dep} and r['pins']['direct_imports']==r['after']['direct_imports'];entry=r['pins']['direct_imports'][dep];p=Path(entry['path']);target=f['selected_project'][dep]['.olean'];assert str(p.resolve(strict=True))==entry['real_path'] and sha(p)==entry['sha256']==target['sha256'];assert reported['explicit_import']=={'module':dep,'producer_realpath':entry['real_path'],'selected_realpath':target['resolved'],'sha256':entry['sha256']}
print('PASS exact output realpath, recorded source/logs, named before/after single explicit direct olean hash')
