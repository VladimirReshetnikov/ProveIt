import hashlib,json,os,subprocess,sys,re
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-prefix-embedding-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-embedding-check-20261106');n='Norm38MacroPrefixEmbedding';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='9e8939bb926fd5d1e88721240579b4fd5c4eccadacbbb2c4c23f9c4dfeb44a5d';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='45b76ca53c0206ab31183ddd7a33b3730ec4b22005d413eea3ba266f8119ae27';assert sha(a/'outer-terminal-author-record.json')=='fa6b21798e0d2cd9001dc3fe475addd9dd0d4ee1b3acc36dc0c9091b65556e63';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['session_id']==18184 and o['exit_code']==0 and 'not an independently retained raw transcript' in o['observation']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='0e44abd4d3cbc028dac5759b7091c3e861376f42f6327a4db11c1512ede71477' and r['object_sha256']=='a7f4b4f604505643e057e48a3f30ee5aaba9780348ee3edbb4ce3a58b58218be'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['inductive PrefixPath','theorem lookup','theorem lookup_two']:assert x in t,x
assert 'SemanticTarget' not in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for theorem in ['lookup','lookup_two']:assert re.search(r"'DiophantineConsistency\.Norm38MacroPrefixEmbedding\."+theorem+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1166
dep=r['dependencies']['DiophantineConsistency.Norm38MacroCuts'];h='9c83339175c439edd66ef5a10e6a192b79621803463dbf9e8420fc6f8725bf36';check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':18184,'author_exit':0,'axiom_reports':'two reports each [propext, Classical.choice, Quot.sound]','guard_slots':100,'overlay_links':1166,'scope':'Generic prefix path and two lookup identities only; no recipe semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
