from pathlib import Path
import hashlib,json,re
h=Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/trace73-gauge');a=h/'observations/attempt04';t=json.loads((a/'terminal.json').read_text());s=h/'Trace73Gauge.lean';r=h/'run.py';obj=Path(t['output'])
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(sha(a/'terminal.json')=='8948683f35f6d24bfd6abdeadcd7a89c239b263d57a7b9d5fdfb18d27761e66d','terminal hash')
need(t['status']=='PASS' and t['exit']==0 and t['reason'] is None,'terminal status')
need(sha(s)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['source_sha256']=='ea63e8f4c0c59b5548b972f176bbb33b320cbe71d2968f4603aad6b561ce85c4','source')
need(sha(r)==t['runner_sha256']=='388718996da8792634ac12cc5c31fe52fda36a2e3ae366170b325c7b4b7ae2e7','runner')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==t['output_sha256']=='397b4aec0c8ed0042867e0e24cb0cc479213769262bda2248b9fccc9d76e7ca9','object')
for name in ('stdout','stderr'):need(sha(a/name)==t[name+'_sha256'],'log '+name)
reports=''.join("'Trace73Gauge."+n+"' depends on axioms: [propext, Quot.sound]\n" for n in ('rank_move','B_move','center_move','graph_move'))
need((a/'stdout').read_text()==reports and not (a/'stderr').read_bytes(),'all four exact diagnostics')
need(len(t['pins'])==7,'pin count')
for p,rec in t['pins'].items():p=Path(p);need(p.is_file() and sha(p)==rec['sha256'] and str(p.resolve())==rec['resolved'],'pin '+str(p))
roots=[Path(p) for p in t['lean_path'].split(':')];mod='Trace73Literal';need(re.findall(r'^import\s+([^\s]+)',s.read_text(),re.M)==[mod],'source imports')
candidates=[x/(mod+'.olean') for x in roots if (x/(mod+'.olean')).exists()];need(candidates and str(candidates[0]) in t['pins'],'first direct import')
for snap in [t['preflight'],t['postflight'],*t['samples']]:need(snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2,'resource')
for i in (1,2,3):
 old=h/f'observations/attempt0{i}';ot=json.loads((old/'terminal.json').read_text());need(ot['status']=='FAILED' and ot['exit']!=0 and 'sorryAx' in (old/'stdout').read_text()+(old/'stderr').read_text(),'failed attempt '+str(i))
print('PASS terminal/source/object/four reports; seven pins and first direct import; resource samples; three failed attempts excluded')
