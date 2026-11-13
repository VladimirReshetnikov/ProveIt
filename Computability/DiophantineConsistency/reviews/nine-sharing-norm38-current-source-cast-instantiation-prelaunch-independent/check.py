import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-source-cast-instantiation';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();man=q/'source-manifest.json';run=q/'run.py';survey=q/'provider_survey.py'
assert sha(man)=='8065a6e99a475def42b31e03044d77d67b64a97243686dc1b8bbbce1ef68ec6a' and sha(survey)=='a8b88dcbd9a1ea69d8679a459f6941ada18e6b845c216330413f2f78c760e85c' and sha(run)=='2369327030d8b551c84a896ff8afb1e4725040ed220c2d880b6b7f925a2759cf'
rows=json.loads(man.read_text())['rows'];names=['Norm38SourceFourCasts','Norm38CurrentSourceFourCasts'];pins=['d8e92e15fee8448e6ee417a5615c7c8708d012c08baee7452bff0ef0b8e1ca76','e9314397aa9995ef6903421168a4aac0bdf7ac64b95c48db4f48ee46fb038f9b'];assert [r['module'].split('.')[-1] for r in rows]==names
texts=[]
for r,n,h in zip(rows,names,pins):
 p=q/'src/DiophantineConsistency'/f'{n}.lean';assert sha(p)==r['source_sha256']==h and D.parents[1]/r['source']==p;t=p.read_text();texts.append(t);assert re.findall(r'^import ([A-Za-z0-9_.]+)$',t,re.M)==r['imports'] and t.count('#print axioms')==1 and 'sorry' not in t
a,b=texts
for i,v in enumerate(('b','k','l','h')):assert f'(h{i} : ((CurrentWindowCarry2011.ports {i} : ℤ) : DiffRing V) = ι {v})' in a
assert 'Norm38CurrentSourceToSeed.source_zero_implies_seed_zero _ u' in a and '(Norm38FourVariablePorts.casts_of_four CurrentWindowCarry2011.ports b k l h h0 h1 h2 h3) hs' in a
assert 'Norm38CurrentFourCastInstantiation.currentNaturalPorts (V := V)' in b and 'Norm38CurrentPorts.port0 Norm38CurrentPorts.port1 Norm38CurrentPorts.port2 Norm38CurrentPorts.port3 hs' in b and 'CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ' in b and 'InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)' in b and 'InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports)' in b
x=subprocess.run([sys.executable,'-I','-S','-B',str(survey)],capture_output=True,text=True,timeout=120);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_POINT_PRODUCER_SURVEY' and all('DiophantineConsistency.'+n in z['selected'] for n in ['Norm38CurrentSourceToSeed','Norm38FourVariablePorts','Norm38CurrentFourCastInstantiation']+[f'Norm38CurrentPort{i}' for i in range(4)]) and z['providers']['portpartial']['rows']==5 and z['providers']['sourcepartial']['rows']==1
assert all('DiophantineConsistency/'+n+'.olean' not in z['links'] for n in names)
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=120);assert x.returncode==0 and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT' and not x.stderr,(x.stdout,x.stderr)
for name in ('nine-sharing-norm38-current-source-to-seed-terminal-independent','nine-sharing-norm38-current-four-cast-terminal-independent'):
 p=D/'reviews'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','manifest_sha256':sha(man),'runner_sha256':sha(run),'scope':'No Lean; fixed current source-to-seed candidate and exact current model representatives uncompiled.'},indent=2,sort_keys=True))
