from pathlib import Path
import hashlib,json,re
h=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace73-center-normalization');a=h/'observations/normalize-attempt02';t=json.loads((a/'terminal.json').read_text());s=h/'Trace75NormalizeCenter.lean';r=h/'run-normalize.py';obj=Path(t['output'])
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(a/'terminal.json')=='5b2e91e5c5f7947d42365237740e719b9cbd18de2d3aaa55fcebec4da0e1702c','terminal hash')
need(t['status']=='PASS' and t['exit']==0 and t['reason'] is None,'terminal status')
need(sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['source_sha256']=='f1737d306452a44076e18001a513ca237ab1baaff95f30852ea28c0a9623e797','source')
need(sha(r)==t['runner_sha256']=='a232c90cad80313593f3af08a1b4feadf9c9e81af69e165c2c66a73aa86559e1','runner')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==t['output_sha256']=='c9db6c31f50c7b19480d7f8f0653e053a77313b7765363ffdd5967b2f1195148','object')
for name in ('stdout','stderr'):need(sha(a/name)==t[name+'_sha256'],'log '+name)
need((a/'stdout').read_text()=="'Trace75NormalizeCenter.positive_zero_to_center' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes(),'diagnostics')
need(len(t['pins'])==13,'pin count')
for p,rec in t['pins'].items():p=Path(p);need(p.is_file() and sha(p)==rec['sha256'] and str(p.resolve())==rec['resolved'],'pin '+str(p))
roots=[Path(p) for p in t['lean_path'].split(':')];mods=['Trace75KappaRoot','Trace75SignFlip','Trace75IntegralTransport','Trace73ModelSigns'];need(re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)==mods,'source imports')
for mod in mods:
 candidates=[x/(mod+'.olean') for x in roots if (x/(mod+'.olean')).exists()];need(candidates and str(candidates[0]) in t['pins'],'first direct import '+mod)
 print(mod,'first',candidates[0])
for snap in [t['preflight'],t['postflight'],*t['samples']]:need(snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2,'resource')
old=h/'observations/normalize-attempt01';ot=json.loads((old/'terminal.json').read_text());need(ot['status']=='FAILED' and ot['exit']!=0,'failed attempt');need('sorryAx' in (old/'stdout').read_text()+(old/'stderr').read_text(),'failed proof disclaimer')
print('PASS terminal/source/object/logs; 13 pins and 4 first direct imports; resource samples; failed attempt excluded')
