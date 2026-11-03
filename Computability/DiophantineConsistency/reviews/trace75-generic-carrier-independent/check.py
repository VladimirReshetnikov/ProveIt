from pathlib import Path
import hashlib,json,re,os
h=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace75-generic-carrier-prototype');a=h/'observations/carrier-attempt01';t=json.loads((a/'terminal.json').read_text());s=h/'Trace75GenericCarrier.lean';r=h/'run.py';obj=Path(t['output_root'])/'Trace75GenericCarrier.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(a/'terminal.json')=='8c74d7c68fad07cd5b1c9ceb8630a5f3655428741f55de362a5cb267bfa6b2e6','terminal')
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))=='fe9d125e328de5934e0d16401084df9b59fb66dfb892b73ebbffb872086c6220','source')
need(sha(r)==t['runner_sha256']=='8b225d03ad2caf26855ab35e367112ff7582ec468f28c3c23850e5687b3d21f7','runner')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='1b083a3965eadf56fdbe00673ef078ff597f114186e19b3a39bb55a190da84f1','object')
for name in ('stdout','stderr'):need(sha(a/name)==t[name+'_sha256'],'log '+name)
need((a/'stdout').read_text()=="'Trace75GenericCarrier.positive_carrier' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes(),'axioms')
need(len(t['inputs'])==10,'input count')
for p,d in t['inputs'].items():need(Path(p).is_file() and sha(p)==d,'pin '+p)
mods=['DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ArithmeticPellRecurrence'];need(re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)==mods,'direct imports')
roots=[Path(p) for p in t['lean_path'].split(':')];need(len(roots)==3,'provider roots')
for n in mods:
 candidates=[p/(n.replace('.','/')+'.olean') for p in roots if os.path.lexists(p/(n.replace('.','/')+'.olean'))];need(candidates and candidates[0].is_file() and str(candidates[0]) in t['inputs'],'first pinned direct '+n);print(n,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:need(snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2,'resource')
print('PASS terminal/source/object/exact report; 10 input hashes and 2 first direct imports; resource samples')
