import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-seed-source-draft';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();man=q/'source-manifest.json';run=q/'run.py';survey=q/'provider_preflight.py';inv=q/'survey-result.json'
assert sha(man)=='60a4658bd4ccf35868962afec2517a3448d66bc60302b185989da39ebf5de2ac' and sha(run)=='6ce71783221031646266888b484404ae3a1926a1a52a21c505c2bd162efc2d79' and sha(survey)=='52cd5c208320f64d809e0ca6731cf00b349080a045fd052c7fa41d87268d408d' and sha(inv)=='4a8fc9a1e2a4b4269e31152ba71b26e4b7647ecc64ee2d1b4ff8b53a60830b7e'
rows=json.loads(man.read_text())['rows'];names=['Norm38FourCastSeedSource','Norm38CurrentSeedSource'];pins=['6d63d13b73689ca57e6ffaec619efbae2001d0e9269073d7daec04e91327f723','fdf2be6294f35fdb21a532ecb5c0cfd10a8072c8cb15e40daad167a77f0f4d03'];assert [r['module'].split('.')[-1] for r in rows]==names
texts=[]
for r,n,h in zip(rows,names,pins):
 p=q/'src/DiophantineConsistency'/f'{n}.lean';assert sha(p)==r['source_sha256']==h and D.parents[1]/r['source']==p;t=p.read_text();texts.append(t);assert re.findall(r'^import ([A-Za-z0-9_.]+)$',t,re.M)==r['imports'] and t.count('#print axioms')==1 and 'sorry' not in t
a,b=texts
for i,v in enumerate(('b','k','l','h')):assert f'(h{i} : ((p {i} : ℤ) : DiffRing V) = ι {v})' in a
assert 'Norm38SeedSource.seed_zero_implies_source_zero p' in a and '(Norm38FourVariablePorts.casts_of_four p b k l h h0 h1 h2 h3) hz' in a
assert 'InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports)' in b and 'InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)' in b and 'Norm38CurrentPorts.port0 Norm38CurrentPorts.port1 Norm38CurrentPorts.port2 Norm38CurrentPorts.port3 hz' in b and 'CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ' in b
z=json.loads(inv.read_text());assert z['shared_count']==1107 and not z['shared_mismatches'] and len(z['a_only'])==35 and len(z['b_only'])==8
for n in ['Norm38FourVariablePorts']+[f'Norm38CurrentPort{i}' for i in range(4)]:assert 'DiophantineConsistency/'+n+'.olean' in z['b_only']
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=120);assert x.returncode==0 and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT' and not x.stderr,(x.stdout,x.stderr)
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','manifest_sha256':sha(man),'runner_sha256':sha(run),'shared_overlay_paths':1107,'current_only_paths':8,'scope':'No Lean; two current-specialization candidates uncompiled, no converse or endpoint.'},indent=2,sort_keys=True))
