from pathlib import Path
import hashlib,json,re,os
h=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace75-old-trace-parts-join-prototype');a=h/'observations/join-attempt01';t=json.loads((a/'terminal.json').read_text());s=h/'Trace75OldTracePartsJoin.lean';r=h/'run.py';obj=Path(t['output_root'])/'Trace75OldTracePartsJoin.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(a/'terminal.json')=='7497e758137d54b6c452031acef605e4c6cdda1a548507ee26d0198deb9830dd','terminal')
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))=='9e2f48369704d67849a897f755334ea93ba8e00b7b22ca664da91718f564e46f','source')
need(sha(r)==t['runner_sha256']=='93c2aa5f5f24359ee1e56e8e91b8c5b81f87956c10c32a888a586e7c78b6a69b','runner')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='848b124f48ae212c85c97872dfca584490a05651c07a9860f69f7436ecfedddb','object')
for name in ('stdout','stderr'):need(sha(a/name)==t[name+'_sha256'],'log '+name)
need((a/'stdout').read_text()=="'Trace75OldTracePartsJoin.positive_zero_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes(),'axioms')
need(len(t['inputs'])==14,'input count')
for p,d in t['inputs'].items():need(Path(p).is_file() and sha(p)==d,'pin '+p)
mods=['Trace75OldTraceOutput','Trace75OldTracePositiveMap'];need(re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)==mods,'direct imports')
roots=[Path(p) for p in t['lean_path'].split(':')];need(len(roots)==7,'provider roots')
for n in mods:
 candidates=[p/(n.replace('.','/')+'.olean') for p in roots if os.path.lexists(p/(n.replace('.','/')+'.olean'))];need(candidates and candidates[0].is_file() and str(candidates[0]) in t['inputs'],'first pinned direct '+n);print(n,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:need(snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2,'resource')
print('PASS terminal/source/object/exact report; fourteen input hashes and first selected direct import; resource samples')
