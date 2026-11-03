from pathlib import Path
import hashlib,json,re,os
h=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace75-seed-offset-prototype');a=h/'observations/offset-attempt01';t=json.loads((a/'terminal.json').read_text());s=h/'Trace75SeedOffset.lean';r=h/'run.py';obj=Path(t['output_root'])/'Trace75SeedOffset.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(a/'terminal.json')=='fc17af3f8805848488b0d7fabad18a00df54036bf35057174d1d70f61df6c90a','terminal')
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))=='35c660d55a688ae4169d55d91ffe9923b8ad38ea0bd0b59eaabce36489698519','source')
need(sha(r)==t['runner_sha256']=='2554987c71eef5e4cb1d3efe063e99bbe5351a76a553d051bed29faa8ecec525','runner')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='3ebcc03a5d12f348c46d5d79f6ce499f4f14f80f1d23e011e3c18f3707567d9c','object')
for name in ('stdout','stderr'):need(sha(a/name)==t[name+'_sha256'],'log '+name)
need((a/'stdout').read_text()=="'Trace75SeedOffset.offset_divisible' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes(),'axioms')
need(len(t['inputs'])==11,'input count')
for p,d in t['inputs'].items():need(Path(p).is_file() and sha(p)==d,'pin '+p)
mods=['DiophantineConsistency.ArithmeticPellCongruences'];need(re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)==mods,'direct imports')
roots=[Path(p) for p in t['lean_path'].split(':')];need(len(roots)==3,'provider roots')
for n in mods:
 candidates=[p/(n.replace('.','/')+'.olean') for p in roots if os.path.lexists(p/(n.replace('.','/')+'.olean'))];need(candidates and candidates[0].is_file() and str(candidates[0]) in t['inputs'],'first pinned direct '+n);print(n,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:need(snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2,'resource')
print('PASS terminal/source/object/exact report; 11 input hashes and 1 first direct import; resource samples')
