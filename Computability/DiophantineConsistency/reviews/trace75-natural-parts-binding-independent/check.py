from pathlib import Path
import hashlib,json,re,os
h=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace75-natural-parts-binding-prototype');a=h/'observations/binding-attempt03';t=json.loads((a/'terminal.json').read_text());s=h/'Trace75NaturalPartsBinding.lean';r=h/'run-v3.py';obj=Path(t['output_root'])/'Trace75NaturalPartsBinding.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(a/'terminal.json')=='e57737f93700dd94ffb92f040f6f76b7c22ea14b816376357d8634557be3588c','terminal')
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))=='676c6fc7e3930fc07de7a64feb19d1da3b9d7561d4e066c68aa2781b8cd69d31','source')
need(sha(r)==t['runner_sha256']=='7d7ec624cde8d205d7fd624f6969b548a63a8ee014f8ec2a0d21dcdf51868aa6','runner')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='749302923c77ec62b0b9cef23cadc3f7ff6b9c18e65bafa0eb1facee629022eb','object')
for name in ('stdout','stderr'):need(sha(a/name)==t[name+'_sha256'],'log '+name)
need((a/'stdout').read_text()=="'Trace75NaturalPartsBinding.positive_zero_of_natural_parts' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes(),'axioms')
need(len(t['inputs'])==16,'input count')
for p,d in t['inputs'].items():need(Path(p).is_file() and sha(p)==d,'pin '+p)
mods=['Trace75OldTracePartsJoin','Trace75Rank'];need(re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)==mods,'direct imports')
roots=[Path(p) for p in t['lean_path'].split(':')];need(len(roots)==8,'provider roots')
for n in mods:
 candidates=[p/(n.replace('.','/')+'.olean') for p in roots if os.path.lexists(p/(n.replace('.','/')+'.olean'))];need(candidates and candidates[0].is_file() and str(candidates[0]) in t['inputs'],'first pinned direct '+n);print(n,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:need(snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2,'resource')
print('PASS terminal/source/object/exact report; sixteen input hashes and first selected direct import; resource samples')

for i in (1,2):
 old=h/f'observations/binding-attempt0{i}';ot=json.loads((old/'terminal.json').read_text());need(ot['exit']!=0 and 'sorryAx' in (old/'stdout').read_text()+(old/'stderr').read_text(),'failed attempt '+str(i))
print('PASS prior failed attempts excluded')
