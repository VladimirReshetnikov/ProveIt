#!/usr/bin/env python3
"""Inspect packaged actual Rocq records. No compiler, extraction, or object recheck."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, tarfile

def sha(b):return hashlib.sha256(b).hexdigest()
def require(x,message):
 if not x:raise RuntimeError(message)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--evidence',type=Path,default=Path(__file__).with_name('actual'));ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();root=a.evidence
 index=json.loads((root/'evidence-index.json').read_text());archive=root/'evidence.tar.gz';require(sha(archive.read_bytes())==index['archive_sha256'],'archive changed')
 files={}
 with tarfile.open(archive,'r:gz') as tar:
  for m in tar:
   p=PurePosixPath(m.name);require(m.isfile() and not p.is_absolute() and '..' not in p.parts and m.name not in files,'invalid archive member')
   f=tar.extractfile(m);require(f is not None,'missing member');b=f.read();require(m.name in index['members'] and index['members'][m.name]=={'bytes':len(b),'sha256':sha(b)},'member mismatch: '+m.name);files[m.name]=b
 require(set(files)==set(index['members']),'member census')
 def doc(n):return json.loads(files[n])
 plan=doc('plan.json');tc=doc('toolchain.json');live=doc('actual-review.json');old=Path(index['historical_build_root'])
 require(plan['count']==237 and plan['reference_count']==195 and plan['target']=='K215F.CorrectDense215','plan census')
 require(len(plan['order'])==len(set(plan['order']))==237 and live['status']=='PASS_CLOSED_KERNEL','live audit status')
 require(set(plan['modules'])==set(plan['order']),'module keys')
 closure=set()
 def visit(n):
  if n in closure:return
  closure.add(n)
  for d in plan['modules'][n]['dependencies']:visit(d)
 visit(plan['target']);require(closure==set(plan['order']),'target closure')
 require(sha(files['plan.json'])==live['plan_sha256'] and sha(files['toolchain.json'])==live['toolchain_record_sha256'],'live audit binding')
 require(json.loads((root/'actual-review.json').read_text())==live,'published live review')
 require('version 9.1.0' in tc['compiler'] and tc['stdlib']=='9.0.0','toolchain')
 records={n:doc('records/'+n+'.json') for n in plan['order']};objects={};closed={}
 for n in plan['order']:
  r=records[n];m=plan['modules'][n];require(r['module']==n and r['status']=='PASS' and r['exit_code']==0 and r['post_inputs_unchanged'] is True,'module status: '+n)
  opts=['-w','-deprecated,-notation-overridden']
  if n.startswith('Undecidability.'):opts+=['-set','Default Proof Using = Type']
  require(r['argv']==[r['argv'][0],*plan['flags'],*opts,m['target']],'compiler argv: '+n)
  snap=Path(r['source_snapshot']).relative_to(old).as_posix();log=PurePosixPath(snap).parent/'output.log'
  require(sha(files[snap])==r['source_sha256'] and sha(files[str(log)])==r['output_sha256'],'snapshot/log: '+n)
  expected={m['source']:r['source_sha256']}
  for d in m['dependencies']:expected[str(Path(plan['modules'][d]['target']).with_suffix('.vo'))]=records[d]['object_sha256']
  require(expected==r['inputs'],'dependency record: '+n)
  if 'expected_reference_sha256' in m:require(m['expected_reference_sha256']==r['source_sha256'],'reference pin: '+n)
  require(live['module_record_sha256'][n]==sha(files['records/'+n+'.json']),'live record binding: '+n)
  objects[str(Path(m['target']).with_suffix('.vo'))]=r['object_sha256']
  if n in ('K215F.Correct215','K215F.CorrectDense215'):
   text=files[str(log)].decode();require(text.count('Closed under the global context')==2 and 'Axioms:' not in text,'endpoint assumptions: '+n)
   require((root/(n+'.log')).read_bytes()==files[str(log)],'endpoint display log');closed[n]=2
 kp=Path(live['kernel_record']).relative_to(old).as_posix();k=doc(kp);kl=str(PurePosixPath(kp).parent/'output.log')
 require(k['status']=='PASS' and k['exit_code']==0 and k['post_inputs_unchanged'] is True and k['inputs']==objects,'kernel record')
 require(sha(files[kp])==live['kernel_record_sha256'] and sha(files[kl])==k['output_sha256']==live['kernel_log_sha256'],'kernel binding')
 require(k['argv'][1:]==[*plan['flags'],'-silent','-o','K215F.CorrectDense215'],'recursive kernel flags')
 require((root/'coqchk.log').read_bytes()==files[kl],'display kernel log')
 result={'status':'PASS_SAVED_RECORDS','scope':'Read-only packaged-record consistency and exact raw assumption reports. No compiler invocation, current .vo replay, or independent replacement for the recorded live object audit.','modules':237,'reference_modules':195,'K215_modules':42,'closed_reports':closed,'kernel_exit_code':0,'archive_sha256':index['archive_sha256'],'live_review_sha256':sha(files['actual-review.json'])}
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
