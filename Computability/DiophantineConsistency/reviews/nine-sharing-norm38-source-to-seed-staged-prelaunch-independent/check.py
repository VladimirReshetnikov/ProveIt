import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-source-to-seed-staged';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();man=q/'source-manifest.json';run=q/'run.py';survey=q/'provider_survey.py'
assert sha(man)=='616e70064e4ad2959b2d9bb45d0baf635f5765b20f1a1a327a2edaf925e60e4c' and sha(survey)=='631812fa3f28d07fafa704f43e152f9b78dd3b1faa6eb8cd0baddc0faa08b783' and sha(run)=='6b5ee8ddba7c09914ca18cf9450ebafd53cdda77d7f90d58cb7618a169187869'
rows=json.loads(man.read_text())['rows'];names=['Norm38SourceCarrierZero','Norm38CarrierUnitNorms','Norm38SourceToSeed'];pins=['83125197be060ad2c18701fcea91a3edd7db5e4961f74406115dac1d4e82889a','e6c6172f3365bbdfc1c1e1b1e434da7fffb7e80122e0ec029c598946bc32d83a','53e513e7c0e5cc4e8a84d146793229e925cfb78e69e2332a6fa694cc3843f92e'];assert [r['module'].split('.')[-1] for r in rows]==names
texts=[];seen=set()
for r,n,h in zip(rows,names,pins):
 p=q/'src/DiophantineConsistency'/f'{n}.lean';assert sha(p)==r['source_sha256']==h and D.parents[1]/r['source']==p;t=p.read_text();texts.append(t);assert re.findall(r'^import ([A-Za-z0-9_.]+)$',t,re.M)==r['imports'] and t.count('#print axioms')==1 and 'sorry' not in t
 for dep in r['imports']:
  if dep.split('.')[-1] in names:assert dep in seen
 seen.add(r['module'])
a,b,c=texts;assert '∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)' in a and 'InternalZero (ObjectCurrentEquation2011.expressionAt p) (fun j => u j+1)' in a and 'Carrier65.value (fun j => ι (ports j)) (fun j => ι (u j+1)) = 0' in a
assert '(hb : (0 : DiffRing V) < ι (ports 0))' in b and 'd.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1' in b
assert '(hb : (0 : DiffRing V) < ((p 0 : ℤ) : DiffRing V))' in c and 'InternalZero (ObjectCurrentEquation2011.expressionAt p) (fun j => u j+1)' in c and '(Fin.cons (1 : V) (SharingForward38.witnessCoordinates ports u))' in c and 'Norm38Forward.static_implies_seed_zero' in c
x=subprocess.run([sys.executable,'-I','-S','-B',str(survey)],capture_output=True,text=True,timeout=120);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_POINT_PRODUCER_SURVEY' and 'DiophantineConsistency.Norm38ForwardFiveNorms' in z['selected'] and z['providers']['forwardpartial']['rows']==1
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=120);assert x.returncode==0 and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT' and not x.stderr,(x.stdout,x.stderr)
p=D/'reviews/nine-sharing-norm38-forward-source-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','manifest_sha256':sha(man),'runner_sha256':sha(run),'scope':'Three generic staged source-to-seed candidate proofs, explicit four port casts and first-port positivity; no Lean replay.'},indent=2,sort_keys=True))
