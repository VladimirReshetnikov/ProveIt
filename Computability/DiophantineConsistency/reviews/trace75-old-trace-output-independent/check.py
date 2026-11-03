from pathlib import Path
import hashlib,json,re,os
h=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace75-old-trace-output-prototype');a=h/'observations/output-attempt01';t=json.loads((a/'terminal.json').read_text());s=h/'Trace75OldTraceOutput.lean';r=h/'run.py';obj=Path(t['output_root'])/'Trace75OldTraceOutput.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(a/'terminal.json')=='3c82c755792715daa3e2f560f13d1d0cfd60c8715d44e170fc84dc9a8168e76d','terminal')
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))=='984197521412381f0e948cb2fb901c0b683201889f94a538a6f7a9e5492be800','source')
need(sha(r)==t['runner_sha256']=='00d2b08629a1135457ee7ec71dc4c35e355644e0a89a60a1929213456045bd80','runner')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='4d661c0f310a2857459cbb1f11369b7c6dacfb6329ea8d132fb26e67a7b457bb','object')
for name in ('stdout','stderr'):need(sha(a/name)==t[name+'_sha256'],'log '+name)
need((a/'stdout').read_text()=="'Trace75OldTraceOutput.old_output_zero' depends on axioms: [propext, Quot.sound]\n" and not (a/'stderr').read_bytes(),'axioms')
need(len(t['inputs'])==9,'input count')
for p,d in t['inputs'].items():need(Path(p).is_file() and sha(p)==d,'pin '+p)
mods=['Trace75OldTraceMap'];need(re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)==mods,'direct imports')
roots=[Path(p) for p in t['lean_path'].split(':')];need(len(roots)==3,'provider roots')
for n in mods:
 candidates=[p/(n.replace('.','/')+'.olean') for p in roots if os.path.lexists(p/(n.replace('.','/')+'.olean'))];need(candidates and candidates[0].is_file() and str(candidates[0]) in t['inputs'],'first pinned direct '+n);print(n,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:need(snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2,'resource')
print('PASS terminal/source/object/exact report; nine input hashes and first selected direct import; resource samples')
