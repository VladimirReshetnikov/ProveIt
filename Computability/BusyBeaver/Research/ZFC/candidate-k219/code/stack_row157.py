"""Root-authorized single-row stack experiment; no search or dependency replay."""
from pathlib import Path
import argparse,collections,hashlib,json,os,subprocess,sys,time

BASE_SHA='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parse(path):
 out={};start=[]
 for line in path.read_text().splitlines():
  if line.startswith('#! start '):start.append(int(line.split()[-1]));continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();key=(int(q),int(b))
  assert key not in out and d in ('L','R')
  out[key]=(int(w),1 if d=='R' else -1,int(z))
 assert start==[0]
 return out
def encode(t):
 return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(t.items()))).encode()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for name in ('baseline','baseline-receipt','checker','output'):ap.add_argument('--'+name,type=Path,required=True)
 a=ap.parse_args();assert __debug__ and not os.environ.get('PYTHONOPTIMIZE')
 assert sha(a.baseline)==BASE_SHA
 t=parse(a.baseline);assert len(t)==438
 expected={(157,1):(1,-1,148),(148,0):(0,1,186),(187,0):(0,1,186),(187,1):(1,1,76),(76,1):(1,-1,148)}
 assert {k:t[k] for k in expected}==expected
 parent=json.loads(a.baseline_receipt.read_text());assert parent['table_sha256']==BASE_SHA
 boot=parent['startup'];assert (boot['steps'],boot['native_state'],boot['head'],len(boot['one_cells']),boot['all_other_cells'])==(312617,84,-5,277,0)
 original_inputs={str(p):sha(p) for p in (a.baseline,a.baseline_receipt,a.checker,Path(__file__))}
 out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
 (out/'baseline.native.tm').write_bytes(a.baseline.read_bytes())
 (out/'baseline-canonicalization.json').write_bytes(a.baseline_receipt.read_bytes())
 (out/'check_joint_fold.py').write_bytes(a.checker.read_bytes())
 n=t.copy();n[157,1]=(1,-1,187)
 assert [k for k in t if t[k]!=n[k]]==[(157,1)]
 native=out/'k219-row157.native.tm';native.write_bytes(encode(n))
 cmd=[sys.executable,'-B',str(out/'check_joint_fold.py'),'--old',str(out/'baseline.native.tm'),'--new',str(native),'--output',str(out/'joint-window.json')]
 started=time.monotonic()
 with (out/'joint-window.log').open('w') as log:
  r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=120,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
 assert r.returncode==0
 proof=json.loads((out/'joint-window.json').read_text())
 assert proof['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS' and proof['negative_control']['status']=='REJECTED'
 assert proof['changed_old_rows']==[[157,1]] and (proof['old_states'],proof['new_states'])==(219,219)
 proof_seconds=time.monotonic()-started
 # Canonicalization is graph relabeling, independent of the window checker.
 states={q for q,b in n};order=[0];mp={0:0}
 for q in order:
  for b in (0,1):
   z=n[q,b][2]
   if z!=254 and z not in mp:mp[z]=len(mp);order.append(z)
 assert set(mp)==states and len(states)==219;mp[254]=219
 c={(mp[q],b):(w,d,mp[z]) for (q,b),(w,d,z) in n.items()}
 canonical=out/'k219-row157.tm';canonical.write_bytes(encode(c))
 # Find the SAME complete baseline entry tape, with a strict finite cap.
 wanted=set(boot['one_cells']);q=h=0;ones=set();uses=collections.Counter()
 for ticks in range(2_000_001):
  if ticks and q==84 and h==boot['head'] and ones==wanted:break
  assert ticks<2_000_000 and q!=254
  b=int(h in ones);uses[q,b]+=1;w,d,q=n[q,b]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 else:raise AssertionError('No complete baseline startup frame within cap')
 # Independent dense canonical tape, sufficient room for this exact prefix.
 origin=ticks+1;buf=bytearray(2*origin+1);cq=0;ch=origin
 for _ in range(ticks):
  w,d,cq=c[cq,buf[ch]];buf[ch]=w;ch+=d
 assert cq==mp[84] and ch-origin==h and {i-origin for i,b in enumerate(buf) if b}==wanted
 assert original_inputs=={p:sha(Path(p)) for p in original_inputs}
 outputs={f.name:sha(f) for f in out.iterdir() if f.is_file()}
 result={'status':'SINGLE_ROW219_STACK_ALL_TAPE_AND_COMPLETE_STARTUP_PASS','role':'Root-authorized bounded experiment by drop_contract; Source139 window checker unchanged. No compiler or full primitive replay.','command':cmd,'exit_code':r.returncode,'timeout_seconds':120,'proof_seconds':proof_seconds,'inputs':original_inputs,'outputs':outputs,'change':{'row':[157,1],'old':[1,-1,148],'new':[1,-1,187]},'helpers_checked':[{ 'row':k,'action':v} for k,v in expected.items()],'states':219,'rows':438,'native_sha256':sha(native),'canonical_sha256':sha(canonical),'native_to_canonical':mp,'window_proof':proof,'startup':{'steps':ticks,'native_state':q,'canonical_state':cq,'head':h,'one_cells':sorted(ones),'all_other_cells':0,'same_complete_baseline_frame':True,'dense_canonical_agrees':True,'uses_changed_row':uses[157,1],'baseline_receipt_sha256':sha(a.baseline_receipt)},'limits':['Same219 state count; no218 result.','Halting equivalence from native state0 for all initial binary tapes and integer head positions; no arbitrary-state theorem claimed.','Ordinary mathematical window certificate; no new proof-assistant or internal-PA endpoint.','Baseline consistency calibration and full runtime are separate; no repeat of those proofs by this experiment.']}
 dump(out/'result.json',result)
 print(json.dumps({k:result[k] for k in ('status','states','rows','native_sha256','canonical_sha256')}))
 print('Startup',ticks,'changed-row uses',uses[157,1],'window contexts',proof['inductive_window_contexts'])
if __name__=='__main__':main()
