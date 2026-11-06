import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-reference-gates-batched-check';draft=R/'nine-sharing-norm38-reference-gates-batched-draft';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();run=q/'run.py';man=q/'source-manifest.json';gen=draft/'generate.py';oldman=draft/'source-manifest.json'
assert sha(run)=='da96ae87bd9d90819aba563e84e757c090af9d3e4b99acc01e8f2c80d078b589' and sha(man)=='f1bcea19ffbb926edaa3cff8e455ff0e0b63b9698f6ab3b28ae7ddbe9fc6ee20' and sha(gen)=='a38102ed3a86932ca3e37084d1ab3044d73206608492af82026860f7b705a7b3' and sha(oldman)=='e51de4382ec1c4b247dc15b408924e60b8923e8e36f36d01b2a9d370c27e94c8'
A=R/'nine-sharing-seed38-weighted-retry/src/DiophantineConsistency/NormAssignment38.lean';B=R/'nine-sharing-norm38-reference-base-retry02/src/DiophantineConsistency/Norm38ReferenceBase.lean';assert sha(A)=='c66694acbba431aa20f4be03a85c0210d24f1b3a51378e0bbeb40452b611817a' and sha(B)=='be7f61985d51b07cfda37da0d1ca40c7d44a01950ef6cf94866a5cb3e2bf1da2'
gates=[(int(t),int(l),int(r),op) for t,l,r,op in re.findall(r'⟨(\d+), (\d+), (\d+), GateOp\.(add|sub|mul)⟩',A.read_text())];assert len(gates)==60 and [x[0] for x in gates]==list(range(21,81))
defs={int(i):x for i,x in re.findall(r'^  let a(\d+) : R := (.+)$',B.read_text(),re.M)};assert sorted(defs)==list(range(81));sign={'add':'+','sub':'-','mul':'*'}
for t,l,r,op in gates:assert defs[t]==f'a{l} {sign[op]} a{r}' and l<t and r<t
rows=json.loads(man.read_text())['rows'];oldrows=json.loads(oldman.read_text())['rows'];assert len(rows)==len(oldrows)==13
roots=[Path('/tmp/nine-sharing-norm38-reference-base-retry02-20261105/lib'),Path('/tmp/current2011-spheres-fresh-base-priority-check02'),Path('/tmp/normalized106-fresh-model-client-20261105'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
for i,(row,old) in enumerate(zip(rows,oldrows)):
 n=f'Norm38ReferenceGateGroup{i:02}' if i<12 else 'Norm38ReferenceGatesAll';assert row['module']==old['module']=='DiophantineConsistency.'+n
 f=q/'src/DiophantineConsistency'/f'{n}.lean';oldf=draft/'src/DiophantineConsistency'/f'{n}.lean';assert sha(f)==sha(oldf)==row['source_sha256']==old['source_sha256'] and D.parents[1]/row['source']==oldf
 t=f.read_text();assert re.findall(r'^import ([A-Za-z0-9_.]+)$',t,re.M)==row['imports'] and 'sorry' not in t
 for root in roots:assert not os.path.lexists(root/('DiophantineConsistency/'+n+'.olean'))
 if i<12:
  assert row['imports']==['DiophantineConsistency.Norm38ReferenceBase'];matches=re.findall(r'theorem reference_gate(\d+) \{R : Type\*\} \[CommRing R\] \(p : Fin 4 → R\) \(x : Fin 14 → R\) :\n    reference p x (\d+) = ringCompute GateOp\.(add|sub|mul) \(reference p x (\d+)\) \(reference p x (\d+)\) := by rfl',t);want=gates[i*5:i*5+5];assert len(matches)==5 and [(int(a),int(b),int(d),int(e),c) for a,b,c,d,e in matches]==[(target,target,left,right,op) for target,left,right,op in want]
 else:
  assert row['imports']==['DiophantineConsistency.Norm38ReferenceGateGroup'+f'{j:02}' for j in range(12)];assert [int(x) for x in re.findall(r'reference_gate(\d+) p x',t)]==list(range(21,81)) and '∀ g ∈ NormAssignment38.gates' in t and t.count('#print axioms')==1
assert not Path('/tmp/nine-sharing-norm38-reference-gates-batched-check-20261105').exists()
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=90);assert x.returncode==0 and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT' and not x.stderr,(x.stdout,x.stderr)
p=D/'reviews/nine-sharing-norm38-reference-base-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','runner_sha256':sha(run),'manifest_sha256':sha(man),'groups':12,'gates':60,'target_collisions':'none at review time among five current roots','scope':'Source-to-gate checks and no-Lean preflight only; proofs uncompiled.'},indent=2,sort_keys=True))
