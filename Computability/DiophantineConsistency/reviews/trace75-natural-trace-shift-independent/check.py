from pathlib import Path
import hashlib,json,re,os
h=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace75-natural-trace-shift-prototype');a=h/'observations/natural-attempt02';t=json.loads((a/'terminal.json').read_text());s=h/'Trace75NaturalTraceShift.lean';r=h/'run-v2.py';obj=Path(t['output_root'])/'Trace75NaturalTraceShift.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(a/'terminal.json')=='c1054e8ec26986679062c73aa8c2e38c241e0fbe4dbe0ce41b1863eadabd6c2a','terminal')
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))=='db24cb58b890c762a3eb8e79d6aff42ec9cdf95ae0893a0b519b5962a77b8a57','source')
need(sha(r)==t['runner_sha256']=='18d8713272d1e7524958a7ccc2f78e483544dd5882008f74879fa4e4bd4a3c3e','runner')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='b828737e9a8889dc05a8aab6e22f84dc2dd470a0265ae27d0d7462fe04498318','object')
for name in ('stdout','stderr'):need(sha(a/name)==t[name+'_sha256'],'log '+name)
need((a/'stdout').read_text()=="'Trace75NaturalTraceShift.natural_shift' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes(),'axioms')
need(len(t['inputs'])==10,'input count')
for p,d in t['inputs'].items():need(Path(p).is_file() and sha(p)==d,'pin '+p)
mods=['Trace75PositiveTraceShift','DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ArithmeticPellRecurrence'];need(re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)==mods,'direct imports')
roots=[Path(p) for p in t['lean_path'].split(':')];need(len(roots)==3,'provider roots')
for n in mods:
 candidates=[p/(n.replace('.','/')+'.olean') for p in roots if os.path.lexists(p/(n.replace('.','/')+'.olean'))];need(candidates and candidates[0].is_file() and str(candidates[0]) in t['inputs'],'first pinned direct '+n);print(n,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:need(snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2,'resource')
old=h/'observations/natural-attempt01';ot=json.loads((old/'terminal.json').read_text());need(ot['exit']!=0 and 'error' in (old/'stdout').read_text()+(old/'stderr').read_text(),'failed attempt')
print('PASS terminal/source/object/exact report; 10 input hashes and 3 first direct imports; resource samples; failed attempt excluded')
