from pathlib import Path
import hashlib,json,re,os
h=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace75-old-trace-map-prototype');a=h/'observations/map-attempt01';t=json.loads((a/'terminal.json').read_text());s=h/'Trace75OldTraceMap.lean';r=h/'run.py';obj=Path(t['output_root'])/'Trace75OldTraceMap.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(a/'terminal.json')=='c9ca2fe3caa963fdcd7682f993139fea0d1cd09f7288787cf80938ffe95a0ff2','terminal')
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))=='0722013ce7cdb32ae4bf4aac7aee64906fa4e0e064406eeba8a378220b2e5021','source')
need(sha(r)==t['runner_sha256']=='617f2d3aeb8ecb4e97e6c02c4c9a73a8156f4bbae3ef86f55cc50d257dd521c4','runner')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='037f11212356efaa43494a640dbb45af97a437f6cadd2812c955bcdbc6d8ec56','object')
for name in ('stdout','stderr'):need(sha(a/name)==t[name+'_sha256'],'log '+name)
need((a/'stdout').read_text()=="'Trace75OldTraceMap.value_shift' depends on axioms: [propext, Quot.sound]\n" and not (a/'stderr').read_bytes(),'axioms')
need(len(t['inputs'])==8,'input count')
for p,d in t['inputs'].items():need(Path(p).is_file() and sha(p)==d,'pin '+p)
mods=['DiophantineConsistency.TenPositiveTrace75'];need(re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)==mods,'direct imports')
roots=[Path(p) for p in t['lean_path'].split(':')];need(len(roots)==2,'provider roots')
for n in mods:
 candidates=[p/(n.replace('.','/')+'.olean') for p in roots if os.path.lexists(p/(n.replace('.','/')+'.olean'))];need(candidates and candidates[0].is_file() and str(candidates[0]) in t['inputs'],'first pinned direct '+n);print(n,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:need(snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2,'resource')
print('PASS terminal/source/object/exact report; eight input hashes and first selected direct import; resource samples')
