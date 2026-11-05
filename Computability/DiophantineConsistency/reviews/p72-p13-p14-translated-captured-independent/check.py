#!/usr/bin/env python3
"""Read-only review of captured P13/P14 translated endpoint receipt."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/p72-p13-p14-translated-captured';O=Path('/tmp/p72-p13-p14-translated-captured-20261105');R=D/'reviews/p72-p13-p14-captured-endpoint-independent/check.py';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={'P72Translated.lean':'324803ca69036a8731c1bb9a65fd635e8a48d29a998c57023eef8f6f1901691a','run.py':'34e8eb5a11a5cb707bd805fd3648b9f4cc8f1b55d661fde97a389c39907e994c','attempt01/state.json':'f080f7ef8a5e361b99af72860a6a9f26f2da05486575fb1a558b8bbef69925b2','attempt01/outer-terminal.json':'8c0f15210c74500e38e66e6bae373297663c33f5030e29c4123f34dbbb2d4b7f'}
for f,h in pins.items():need(sha(P/f)==h,'pin '+f)
q=subprocess.run([sys.executable,'-I','-S','-B',str(R)],capture_output=True,timeout=120);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)['status']=='PASS','prior independent audit')
s=json.loads((P/'attempt01/state.json').read_bytes());outer=json.loads((P/'attempt01/outer-terminal.json').read_bytes());need(s['status']=='PASS' and outer['actual_session']==24376 and outer['exit_code']==0,'observed status');need(sha(O/'state.json')==pins['attempt01/state.json'] and sha(O/'src/DiophantineConsistency/P72Translated.lean')==pins['P72Translated.lean'],'source state')
need(s['runner_sha256']==pins['run.py'] and s['object_sha256']==sha(O/'lib/DiophantineConsistency/P72Translated.olean')=='75531c205ee5bbb6053d00a8a8b1beefbb73747cdfa6835994e14945510949ed','output')
need(len(s['runs'])==2,'runs')
for typ,r in zip(('deps','compile'),s['runs']):
 need(r['exit']==0 and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==5*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==180,'monitor '+typ)
 need(sha(O/(typ+'.txt'))==sha(P/'attempt01'/(typ+'.txt'))==r['log_sha256'],'log '+typ)
need(set(s['dependencies'])=={'Init','DiophantineConsistency.Compact44.IPRAOrdinary72P14'},'direct import')
dep=s['dependencies']['DiophantineConsistency.Compact44.IPRAOrdinary72P14'];need(dep['sha256']=='3c47dcbbd39cbb2f89092e40d747366589cc618da7bdf9765016554d65e82468' and sha(dep['path'])==dep['sha256'] and str(Path(dep['path']).resolve())==dep['realpath'],'P14 route')
for path,v in s['direct_guard'].items():
 f=Path(path)
 if v is None:need(not os.path.lexists(f),'unexpected guard '+path)
 else:need(f.is_file() and str(f.resolve())==v['realpath'] and sha(f)==v['sha256'],'changed guard '+path)
for path,target in s['overlay_links'].items():
 f=Path(path);need(f.is_symlink() and str(f.resolve())==target,'overlay '+path)
source=(P/'P72Translated.lean').read_text();need(source.count('have z := IPRABoundedRhoZFC.zfcEquiv')==2 and source.count('Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z)')==2 and source.count('Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h)')==2,'composition orientation')
for name,mod in [('standard_translated_p13','IPRAOrdinary72'),('standard_translated_p14','IPRAOrdinary72P14')]:
 need('positiveShift '+mod+'.expression' in source and mod+'.standard_equivalence' in source and 'theorem '+name in source,'theorem '+name)
 text=(P/'attempt01/compile.txt').read_text();r=re.findall(r"'DiophantineConsistency.P72Translated."+name+r"' depends on axioms: \[([^]]*)\]",text);need(len(r)==1 and {x.strip() for x in r[0].split(',')}=={'propext','Classical.choice','Quot.sound'},'axioms '+name)
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','actual_session':24376,'object_sha256':s['object_sha256'],'direct_guard_slots':len(s['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'Mapped translated endpoints on audited captured P13/P14 providers; no fresh source closure, Lean JSON/port byte theorem, or separate evidence of first preflight refusal.'},indent=2,sort_keys=True))
