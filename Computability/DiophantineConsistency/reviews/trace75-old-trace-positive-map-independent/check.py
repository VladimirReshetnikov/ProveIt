from pathlib import Path
import hashlib,json,re,os
h=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace75-old-trace-positive-map-prototype');a=h/'observations/positive-attempt02';t=json.loads((a/'terminal.json').read_text());s=h/'Trace75OldTracePositiveMap.lean';r=h/'run-v2.py';obj=Path(t['output_root'])/'Trace75OldTracePositiveMap.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(a/'terminal.json')=='f6d7ed97af49e206bfd301debac28f06157cef8f3dc9f3c0a21ccf0103ba40e4','terminal')
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))=='4159326d3b7d7e4fc3c769b6d14448c1b63952a8c4e108b1ad9a6f517ebd0bb1','source')
need(sha(r)==t['runner_sha256']=='293897174f26f40487aa773e1fc69cf79070b3caf972c515b7474db73464e789','runner')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='3827f85c28655115020d07835f6b58144b6c056c3fb6194f817b08f59e4e97d0','object')
for name in ('stdout','stderr'):need(sha(a/name)==t[name+'_sha256'],'log '+name)
need((a/'stdout').read_text()=="'Trace75OldTracePositiveMap.positive_parent_zero' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes(),'axioms')
need(len(t['inputs'])==12,'input count')
for p,d in t['inputs'].items():need(Path(p).is_file() and sha(p)==d,'pin '+p)
mods=['Trace75OldTraceMap','Trace75NaturalTraceShift'];need(re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)==mods,'direct imports')
roots=[Path(p) for p in t['lean_path'].split(':')];need(len(roots)==5,'provider roots')
for n in mods:
 candidates=[p/(n.replace('.','/')+'.olean') for p in roots if os.path.lexists(p/(n.replace('.','/')+'.olean'))];need(candidates and candidates[0].is_file() and str(candidates[0]) in t['inputs'],'first pinned direct '+n);print(n,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:need(snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2,'resource')
old=h/'observations/positive-attempt01';ot=json.loads((old/'terminal.json').read_text());log=(old/'stdout').read_text()+(old/'stderr').read_text();need(ot['exit']==0 and ot['reason'] is None and 'warning' in log and 'unused' in log,'warning-rejected attempt')
print('PASS terminal/source/object/exact report; 12 input hashes and 2 first direct imports; resource samples; warning-rejected attempt excluded')
