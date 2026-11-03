from pathlib import Path
import hashlib,json,re
h=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace75-positive-trace-shift-prototype');a=h/'observations/shift-attempt02';t=json.loads((a/'terminal.json').read_text());s=h/'Trace75PositiveTraceShift.lean';r=h/'run-v2.py';obj=Path(t['output_root'])/'Trace75PositiveTraceShift.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(a/'terminal.json')=='d1aeb6a09fd2767c39ff84d3a64a71b8b66193627a82ed074ed18f67bf1f6629','terminal')
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))=='453cb4a857d4e4c529a5587e159b3ee3a593ff83f1a4a9e05ec9ae447fa7c283','source')
need(sha(r)==t['runner_sha256']=='98c2e57e150a5b1204910184a15a7ada17311571f2f78650452249ae4512b2e2','runner')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='f37bfe2a63967448298d15fc8aac2da4ad491489453be6bcd9d73ebda8a94c7b','object')
for name in ('stdout','stderr'):need(sha(a/name)==t[name+'_sha256'],'log '+name)
need((a/'stdout').read_text()=="'Trace75PositiveTraceShift.positive_shift' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes(),'axioms')
need(len(t['inputs'])==7,'input count')
for p,d in t['inputs'].items():need(Path(p).is_file() and sha(p)==d,'pin '+p)
mods=['Mathlib.Algebra.Order.Ring.Basic','Mathlib.Tactic.Linarith','Mathlib.Tactic.Positivity','Mathlib.Tactic.Ring'];need(re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)==mods,'direct imports')
roots=[Path(p) for p in t['lean_path'].split(':')];need(len(roots)==1,'package root')
for n in mods:need(str(roots[0]/(n.replace('.','/')+'.olean')) in t['inputs'],'pinned direct '+n)
for snap in [t['preflight'],t['postflight'],*t['samples']]:need(snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2,'resource')
old=h/'observations/shift-attempt01';ot=json.loads((old/'terminal.json').read_text());need(ot['exit']!=0 and 'sorryAx' in (old/'stdout').read_text()+(old/'stderr').read_text(),'failed attempt')
print('PASS terminal/source/object/exact report; 7 input hashes and 4 direct imports; resource samples; failed attempt excluded')
