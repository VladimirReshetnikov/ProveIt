import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-named-prefix-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-named-prefix-check-20261106');sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='67ed2555859b8cb25ab3ce3189036fefdccaab10b8df219a9fe06e2d299bc1f1';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['runner_sha256']=='b96df7ac6a942bcdf4d52890659f05b48b54b7f14a33f70ecffeeb0d55db5ec7'==sha(p/'run.py') and len(s['rows'])==2
assert sha(a/'outer-terminal-author-record.json')=='86b48909c9e3facdd5128b446b6412477070e0b6d45201e4fba438ab310e541d';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==83109 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
cache={}
def check(path,h,rp=None):
 q=Path(path);assert q.is_file() and (rp is None or str(q.resolve())==rp)
 if str(q.resolve()) not in cache:cache[str(q.resolve())]=sha(q)
 assert cache[str(q.resolve())]==h
expected=[('Norm38MacroPrefixes','c2d995fcf0287325efcfbd060bed17eefd33a1b481a2b67a20978234614b00fa','ab6534c698e5d369189c7d799702d5db98fe7701a015b0af0086406c141c2ea8','fe298ae37c2ff9212a083f2a43e23677bb781708c9b1b3b0cec4bc76e43499b2',100),('Norm38MacroPrefixFirst','cad3163594121c4c2d9a626385f1cea9faa3917783510e84a6cf53f0901ba007','a69ba5536b935e388c616cc6c624ecb8da8aaef052b3350bc09d327dd8272c9a','daad5651454c61e445730496e8585f7bb8a9eb321bf1781b8faccd935c9c245f',150)]
for row,(n,sh,oh,lh,gc) in zip(s['rows'],expected):
 assert row['module']==n and row['source_sha256']==sh and row['object_sha256']==oh and len(row['direct_guard'])==gc
 check(p/'src/DiophantineConsistency'/f'{n}.lean',sh);check(out/'src/DiophantineConsistency'/f'{n}.lean',sh);check(out/'lib/DiophantineConsistency'/f'{n}.olean',oh)
 for phase in ('deps','compile'):
  z=row[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];check(a/f'{n}-{phase}.txt',z['log_sha256']);check(out/f'{n}-{phase}.txt',z['log_sha256'])
 check(a/f'{n}-compile.txt',lh)
 for k,v in row['direct_guard'].items():
  if v is None:assert not os.path.lexists(k)
  else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(s['overlay_links'])==1167
for row,bindings in [(s['rows'][0],{'DiophantineConsistency.Norm38MacroRecipe':'c1c8213d2c752991e7404820521fcd6466511b187a0648c000894254f4bd7129'}),(s['rows'][1],{'DiophantineConsistency.Norm38MacroPrefixes':expected[0][2],'DiophantineConsistency.Norm38MacroCuts':'9c83339175c439edd66ef5a10e6a192b79621803463dbf9e8420fc6f8725bf36'})]:
 for k,h in bindings.items():
  dep=row['dependencies'][k];check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and row['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
assert (a/'Norm38MacroPrefixes-compile.txt').read_text()=="'DiophantineConsistency.Norm38MacroPrefixes.recipe_eq_named' does not depend on any axioms\n"
assert (a/'Norm38MacroPrefixFirst-compile.txt').read_text()=="'DiophantineConsistency.Norm38MacroPrefixFirst.first_prefix_value' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
t=(p/'src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();u=(p/'src/DiophantineConsistency/Norm38MacroPrefixFirst.lean').read_text();assert 'Norm38MacroRecipe.recipe = d45' in t and 'd1.values a (Fin.last 0)' in u and 'Norm38MacroRecipe.recipe.values' not in u
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','author_session':83109,'author_exit':0,'stage_objects':{x[0]:x[2] for x in expected},'stage_axioms':{'recipe_eq_named':[],'first_prefix_value':['propext','Classical.choice','Quot.sound']},'guard_slots':250,'overlay_links':1167,'scope':'Recipe-to-d45 identity and d1 value only; no full-recipe first-entry or semantic graph equality, no Lean replay.'},indent=2,sort_keys=True))
