import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-four-variable-ports-check';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();run=q/'run.py';man=q/'source-manifest.json';src=q/'src/DiophantineConsistency/Norm38FourVariablePorts.lean'
assert sha(src)=='24c2e6a9ccfa40c8766e53c9523cbc4562322308279b8e7f3afa51b9e08c7302' and sha(man)=='b0a4e6a276d070640a70987791d1a46761bbb474baa7cf1527b61f5f10b285e6' and sha(run)=='39f9e980a646f279ccca90e5c1d8f8885cfa83b6dd71b63cc826ab4257122e56'
m=json.loads(man.read_text())['rows'];assert len(m)==1 and m[0]['source_sha256']==sha(src) and m[0]['module']=='DiophantineConsistency.Norm38FourVariablePorts' and m[0]['imports']==['DiophantineConsistency.Norm38FinFour','DiophantineConsistency.Norm38SeedStaticIff']
t=src.read_text();assert 'def naturalPorts (b k l h : V) : Fin 4 → V := ![b,k,l,h]' in t and t.count('theorem ')==2 and t.count('#print axioms')==2 and 'sorry' not in t
for i,v in enumerate(('b','k','l','h')):assert t.count(f'(h{i} : ((p {i} : ℤ) : DiffRing V) = ι {v})')==2
assert '∀ j, ((p j : ℤ) : DiffRing V) = ι (naturalPorts b k l h j)' in t and 'h0 h1 h2 h3' in t and 'Norm38SeedStaticIff.seed_zero_iff_static p _ w (casts_of_four p b k l h h0 h1 h2 h3)' in t
assert 'CurrentMasks2011' not in t and 'CurrentKernel2011' not in t
r=run.read_text();assert "'c7e1f7e465cf89c0d5ca5e3231cf0ddc96bcd35fa31399d219174a119df75c09'" in r and "base['rows']=base['rows'][:1]" in r and "ir['module']=='Norm38SeedStaticIff'" in r and "'ebc30ad19643e6e0fe5eb5f253163d660c8510165e902d53150e11d75a9be578'" in r and "'-M2800'" in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=90);assert x.returncode==0 and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT' and not x.stderr,(x.stdout,x.stderr)
p=D/'reviews/nine-sharing-norm38-current-ports-abstract-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','source_sha256':sha(src),'runner_sha256':sha(run),'scope':'Port-parametric only with four cast assumptions; no Lean replay or concrete current-port instantiation.'},indent=2,sort_keys=True))
