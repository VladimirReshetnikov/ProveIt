from pathlib import Path
import hashlib,json,re
h=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace73-center-normalization');a=h/'observations/fixed-attempt01';t=json.loads((a/'terminal.json').read_text());s=h/'Trace75FixedTo73.lean';r=h/'run-fixed.py';obj=Path(t['output'])
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(a/'terminal.json')=='ca2a8cdfdcc52b2f247bd28f01bd5c1861c7d742e11de81d4ba58ab2d7bcc54b','terminal hash')
need(t['status']=='PASS' and t['exit']==0 and t['reason'] is None,'terminal status')
need(sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['source_sha256']=='5c486b31cd384fa031dc20b07a64e662542812226b79fbfcc4097ecea9a95e9b','source')
need(sha(r)==t['runner_sha256']=='6d78f43d8e4dc4a58de5cb83a871149b590beedef12d74aa22fe030f6f6e3b97','runner')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==t['output_sha256']=='7ba08d2cd24c4d3c1e25155a23fc23608607adc995c1ec96e43c295600c7d349','object')
for name in ('stdout','stderr'):need(sha(a/name)==t[name+'_sha256'],'log '+name)
need((a/'stdout').read_text()=="'Trace75FixedTo73.positive_zero_to_center' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes(),'diagnostics')
need(len(t['pins'])==15,'pin count')
for p,rec in t['pins'].items():p=Path(p);need(p.is_file() and sha(p)==rec['sha256'] and str(p.resolve())==rec['resolved'],'pin '+str(p))
roots=[Path(p) for p in t['lean_path'].split(':')];mods=['Trace75NormalizeCenter','Trace75FixedBounds'];need(re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)==mods,'source imports')
for mod in mods:
 candidates=[x/(mod+'.olean') for x in roots if (x/(mod+'.olean')).exists()];need(candidates and str(candidates[0]) in t['pins'],'first direct import '+mod)
 print(mod,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:need(snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2,'resource')
print('PASS terminal/source/object/logs; 15 pins and 2 first direct imports; resource samples')
