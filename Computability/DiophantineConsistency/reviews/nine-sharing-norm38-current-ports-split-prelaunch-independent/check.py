import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-ports-split-draft';old=R/'nine-sharing-norm38-current-ports-check';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();src=old/'src/DiophantineConsistency/Norm38CurrentPorts.lean';manifest=q/'source-manifest.json';run=q/'run.py';gen=q/'generate.py'
assert sha(src)=='fa3edbe7b05a7efe82808631f0d6a21800ed7db498af61c5d0d1093f5f31bc0c' and sha(gen)=='42431f339be4b5a03ff3cae5d78d471448240be9742a1bb8d1a8c188f09f809b' and sha(manifest)=='868481d10dc1dfd490aec4e34466cce1c90eedb98a1d2d1b196d1686558e9cc7' and sha(run)=='67b968d31634547dd97c10d238b3a1a8abeb7bc605516581518d26cb8564da9f'
a=(old/'run.py').read_text();a=a.replace('/tmp/nine-sharing-norm38-current-ports-check-20261105','/tmp/nine-sharing-norm38-current-ports-split-20261105').replace('79e1bb3268ea151995c107844c1911fcb5fc31d1fc3f9ac0714f4b166f8a4766',sha(manifest)).replace('single-module fixed-current-port cast and static equivalence experiment','seven-module split current-port cast and static equivalence experiment').replace('PASS norm38 fixed-current-port casts','PASS norm38 split fixed-current-port casts');assert a==run.read_text()
s=src.read_text();head=s[s.index('set_option autoImplicit'):s.index('def naturalPorts')];end='\nend DiophantineConsistency.Norm38CurrentPorts\n';expected={}
expected['Norm38CurrentPortBase']='import DiophantineConsistency.Norm38SeedStaticIff\nimport DiophantineConsistency.CurrentKernelData2011\n'+head+s[s.index('def naturalPorts'):s.index('theorem port0')]+end
for i in range(4):
 start=s.index(f'theorem port{i} :');stop=s.index(f'theorem port{i+1} :') if i<3 else s.index('theorem port_casts');expected[f'Norm38CurrentPort{i}']='import DiophantineConsistency.Norm38CurrentPortBase\n'+head+s[start:stop]+end+f'#print axioms DiophantineConsistency.Norm38CurrentPorts.port{i}\n'
imports=''.join(f'import DiophantineConsistency.Norm38CurrentPort{i}\n' for i in range(4));expected['Norm38CurrentPortCasts']=imports+head+s[s.index('theorem port_casts'):s.index('theorem current_seed_zero_iff_static')]+end+'#print axioms DiophantineConsistency.Norm38CurrentPorts.port_casts\n'
expected['Norm38CurrentPortSpecialization']='import DiophantineConsistency.Norm38CurrentPortCasts\n'+head+s[s.index('theorem current_seed_zero_iff_static'):s.index('end DiophantineConsistency.Norm38CurrentPorts')]+end+'#print axioms DiophantineConsistency.Norm38CurrentPorts.current_seed_zero_iff_static\n'
rows=json.loads(manifest.read_text())['rows'];assert [r['module'].split('.')[-1] for r in rows]==list(expected)
seen=set()
for r in rows:
 n=r['module'].split('.')[-1];f=q/'src/DiophantineConsistency'/f'{n}.lean';assert f.read_text()==expected[n] and sha(f)==r['source_sha256'] and (D.parents[1]/r['source'])==f and 'sorry' not in f.read_text()
 assert re.findall(r'^import ([A-Za-z0-9_.]+)$',f.read_text(),re.M)==r['imports']
 for dep in r['imports']:
  if dep.split('.')[-1] in expected:assert dep in seen
 seen.add(r['module'])
x=subprocess.run([sys.executable,'-I','-S','-B',str(run),'--preflight'],capture_output=True,text=True,timeout=90);assert x.returncode==0 and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT' and not x.stderr,(x.stdout,x.stderr)
print(json.dumps({'status':'PASS_PRELAUNCH_ONLY','seven_exact_declarations':True,'manifest_sha256':sha(manifest),'runner_sha256':sha(run),'scope':'No Lean; prior failed universal proof is unchanged and remains unverified on split providers.'},indent=2,sort_keys=True))
