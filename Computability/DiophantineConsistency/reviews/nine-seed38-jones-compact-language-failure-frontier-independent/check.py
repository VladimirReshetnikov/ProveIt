import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-language-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-compact-language-check-20261106');n='Norm38MacroLanguage';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='f68968f4fae77941198bf7726512df92b81a9be0a25f797e21a17cfed390f258';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and s['failure']=="RuntimeError('compile failed Norm38MacroLanguage')"
assert sha(a/'outer-terminal-author-record.json')=='1a7fc958482ceaff1af9935c27b85987db0e2d37116095c3524e22e3d3c8a8ba';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==15667 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='18ecac5f271aafd336133d48d8fdf9357e06dda7ca649712a801e71097a0e624' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'];assert r['deps']['exit']==0 and r['compile']['exit']==1 and r['compile']['stop_reason'] is None and not r['compile']['monitor_errors'] and not r['compile']['observed_descendant_pids']
for phase in ('deps','compile'):assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==r[phase]['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='3c8396391cb87aebe9782efe5c13f6ed40c8d878c0028998bfd9a32e8ace0627' and "unexpected token 'prefix'" in log and 'Unknown identifier `Dag`' in log and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1164
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
dep=r['dependencies']['DiophantineConsistency.Norm38NamedFormula'];check(dep['path'],'f628947fecd14dec5840ed18aa4b362c8e1173e6cf4fbdb60722c428e23b2725',dep['realpath']);assert dep['sha256']=='f628947fecd14dec5840ed18aa4b362c8e1173e6cf4fbdb60722c428e23b2725' and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
print(json.dumps({'status':'PASS_FAILED_RUN_AUDIT','author_session':15667,'author_exit':1,'failure':'unexpected reserved token prefix and cascading unknown Dag','guard_slots':100,'overlay_links':1164,'scope':'No language object, no postflight, no Lean replay or recipe theorem.'},indent=2,sort_keys=True))
