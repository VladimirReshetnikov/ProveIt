import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-four-cast-instantiation-check';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();run=q/'run.py';man=q/'source-manifest.json';src=q/'src/DiophantineConsistency/Norm38CurrentFourCastInstantiation.lean'
assert sha(src)=='8d9e2996454c0fd2ffbc05055db11cab7ab1ca22cef5b93ba8149cf535f0fa1e' and sha(man)=='ceb6011af0cd26f06beb5f697daac9bcb08e3952763e5a621b3dcc441d77a30e' and sha(run)=='be2be3f2c1708d38c7c6466a8036d8673f7ebd989ba4cdc1db001ff43e1892e8'
m=json.loads(man.read_text())['rows'];assert len(m)==1 and m[0]['source_sha256']==sha(src) and m[0]['module']=='DiophantineConsistency.Norm38CurrentFourCastInstantiation' and m[0]['imports']==['DiophantineConsistency.Norm38FourVariablePorts']+[f'DiophantineConsistency.Norm38CurrentPort{i}' for i in range(4)]
t=src.read_text();assert 'Norm38FourVariablePorts.naturalPorts (CurrentMasks2011.beta : V) (CurrentKernel2011.K : V)' in t and t.count('CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ')==2
assert 'InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) ↔' in t and 'NormAssignment38.gatesHold ι (currentNaturalPorts (V := V)) w ∧' in t and 'NormAssignment38.fiveNorms ι (currentNaturalPorts (V := V)) w' in t
assert 'Norm38FourVariablePorts.seed_zero_iff_four_port_static' in t and 'Norm38CurrentPorts.port0 Norm38CurrentPorts.port1 Norm38CurrentPorts.port2 Norm38CurrentPorts.port3' in t and t.count('#print axioms')==1 and 'sorry' not in t
r=run.read_text();assert "'c3bf8f529e151226e83d9b8db93a025f6eaf1e7d3795d2395e47ca6b731321b0'" in r and "'0f89b8b0a53abd15b0d7c1e20f198495775628e104fabc247c24efbd2cb81ad4'" in r and "prod['rows'][:5]" in r and "for n in tuple('Norm38CurrentPort%d'%i for i in range(4))" in r and "'-M2800'" in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=90);assert x.returncode==0 and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT' and not x.stderr,(x.stdout,x.stderr)
for name in ('nine-sharing-norm38-current-ports-split-terminal-independent','nine-sharing-norm38-four-variable-ports-terminal-independent'):
 p=D/'reviews'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),(name,x.stderr)
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','source_sha256':sha(src),'runner_sha256':sha(run),'scope':'No Lean; symbolic-current cast instantiation remains unverified and may trigger kernel memory.'},indent=2,sort_keys=True))
