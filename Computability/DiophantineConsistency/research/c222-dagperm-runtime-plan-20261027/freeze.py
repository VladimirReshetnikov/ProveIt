from pathlib import Path
import hashlib,json,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency/research';P=D/'c222-dagperm-runtime-plan-20261027';P.mkdir(exist_ok=False)
def rec(p):
 p=Path(p);return {'path':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
for f in ['plan-dagperm-runtime-20261027.py','plan-dagperm-runtime-20261027-v1.py','plan-dagperm-runtime-20261027-v2.py']:
 shutil.copyfile('/tmp/'+f,P/f)
shutil.copyfile(__file__,P/'freeze.py')
save(P/'preflight-history.json',{'scope':'Read-only planners only; no Lean invocation or overlay creation.', 'attempt1':{'driver':rec(P/'plan-dagperm-runtime-20261027-v1.py'),'status':'FAILED','diagnostic':'KeyError: path at verify(external[n]); the tool output was observed directly and this diagnostic is manually transcribed. One boundary record uses nested object.', 'no_successful_plan_written':True},'attempt2':{'driver':rec(P/'plan-dagperm-runtime-20261027-v2.py'),'status':'PASS','scope':'two cache profiles, then expanded before freeze to add exact first macro-only profile'},'final':{'driver':rec(P/'plan-dagperm-runtime-20261027.py'),'status':'PASS','scope':'three exact reachable cache profiles; all selected source/header/object and boundary primary checks pass'}})
plan=D/'c222-dagperm-runtime-cache-plan-20261027.json';a=json.loads(plan.read_text());pins={}
for profile in a['profiles'].values():
 for m in profile['modules']:
  for q in [m['source'],*m['objects']]:pins[q['path']]=q
 for e in profile['external']:
  def walk(v):
   if isinstance(v,dict):
    if 'path'in v and'sha256'in v:pins[v['path']]=v
    for x in v.values():walk(x)
   elif isinstance(v,list):
    for x in v:walk(x)
  walk(e)
for q in a['selected_authentication']+a['source_guide_pins']:pins[q['path']]=q
for path,q in pins.items():assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==q['sha256'],path
save(P/'final-rehash.json',{'status':'PASS','unique_paths':len(pins),'pins':list(pins.values()),'scope':'Selected source/objects/package boundary companions plus parent/provider observations and source guides; no compiler/rebuild.'})
files=[D/'c222-dagperm-runtime-proposal-20261027.md',plan,*sorted(p for p in P.iterdir()if p.is_file())];save(P/'FILES.json',[rec(p)for p in files]);print(json.dumps({'proposal':rec(files[0]),'inventory':rec(plan),'manifest':rec(P/'FILES.json'),'files':len(files),'final_pins':len(pins)},indent=2))
