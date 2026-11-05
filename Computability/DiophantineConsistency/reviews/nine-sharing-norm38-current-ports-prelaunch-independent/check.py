import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-current-ports-check'; sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
src=q/'src/DiophantineConsistency/Norm38CurrentPorts.lean';run=q/'run.py';man=q/'source-manifest.json';old=q/'preflight-initial/run.py';obs=q/'preflight-initial/observation.json'
assert sha(src)=='fa3edbe7b05a7efe82808631f0d6a21800ed7db498af61c5d0d1093f5f31bc0c' and sha(man)=='79e1bb3268ea151995c107844c1911fcb5fc31d1fc3f9ac0714f4b166f8a4766' and sha(run)=='eeb783c0f2516bf321695948de0cc561e41f2b7130c3e89fae07cd7c14ab3bb1' and sha(old)=='ce6da75c2d32f435b1400815a9b53337022ffe147130d7fa799c819b52e7179a'
a=old.read_text();assert a.count("Path(prod['snapshot'])/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentKernelData2011.lean'")==1
assert a.replace("Path(prod['snapshot'])/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentKernelData2011.lean'","Path(prod['snapshot'])/'src/DiophantineConsistency/CurrentKernelData2011.lean'")==run.read_text()
o=json.loads(obs.read_text());assert o['exit_code']==1 and not o['lean_launched'] and 'author-recorded' in o['observation_kind'] and o['initial_runner_sha256']==sha(old)
t=src.read_text();base=(D/'Lean/DiophantineConsistency/ModelThirteenCarrier.lean').read_text();start='theorem port0';end='theorem positive_of_ι';assert t[t.index(start):t.index('theorem port_casts')].strip()==base[base.index(start):base.index(end)].strip()
assert '![beta, K, lowPort, highPort + beta]' in (D/'Lean/DiophantineConsistency/CurrentMaskData2011.lean').read_text()
assert 'def ports : Fin 4 → ℤ := CurrentMasks2011.ports (K : ℤ)' in (D/'Lean/DiophantineConsistency/CurrentKernelData2011.lean').read_text()
assert 'InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) ↔' in t
assert 'Norm38SeedStaticIff.seed_zero_iff_static _ _ w (port_casts (V := V))' in t and 'fin_cases j' in t
assert t.count('#print axioms')==2 and 'sorry' not in t
m=json.loads(man.read_text())['rows'];assert len(m)==1 and m[0]['source_sha256']==sha(src) and m[0]['imports']==['DiophantineConsistency.Norm38SeedStaticIff','DiophantineConsistency.CurrentKernelData2011']
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=90);assert x.returncode==0 and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT' and not x.stderr,(x.stdout,x.stderr)
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','source_sha256':sha(src),'runner_sha256':sha(run),'initial_preflight':'author recorded exit 1; exact single path correction','scope':'No Lean run; theorem proof and resource fit unverified.'},indent=2,sort_keys=True))
