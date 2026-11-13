#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-weight-union942-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='92a146a0e3a0885fd06a9a98531ab33753eb727e72e873640dc929dfd01dcda6' and sha(p/'source-manifest.json')=='43b326e71f54283140b56a92717c6e47386326114cd0787ad9bc84e6c32a9a88'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-k-weight-union224-check/source-manifest.json').read_text())['rows'];assert len(rows)==40 and rows[:22]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
prev=224
for j in range(6):
 a=4+j*2;b=a+1;middle=prev+64;end=middle+(14 if b==15 else 64);base=22+j*3
 pair=json.loads((root/f'research/nine-sharing-sign17-k-weight-aggregate-batch{a:02}-{b:02}-check/source-manifest.json').read_text())['rows'];assert rows[base:base+2]==pair[15:17]
 e=rows[base+2];assert e['module']==f'DiophantineConsistency.Sign17KWeightUnion{end}' and e['imports']==[f'DiophantineConsistency.Sign17KWeightUnion{prev}',f'DiophantineConsistency.Sign17KWeightAggregateBatch{a:02}',f'DiophantineConsistency.Sign17KWeightAggregateBatch{b:02}']
 s=(p/'src/DiophantineConsistency'/(e['module'].split('.')[-1]+'.lean')).read_text()
 for t in (f'def indices{middle} : Fin {middle}',f'def weights{middle} : Fin {middle}',f'def indices : Fin {end}',f'def weights : Fin {end}',f'Sign17KWeightUnion{prev}.all_weights Sign17KWeightAggregateBatch{a:02}.all_weights i',f'all_weights{middle} Sign17KWeightAggregateBatch{b:02}.all_weights i') : assert t in s,t
 assert s.count('Sign17KWeightAppend.append_certificates')==2
 c=root/f'reviews/nine-sharing-sign17-k-weight-aggregate-batch{a:02}-{b:02}-terminal-independent/check.py';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=180);prev=end
assert prev==942
c=root/'reviews/nine-sharing-sign17-k-weight-union224-terminal-independent/check.py';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':40,'lengths':[224,352,480,608,736,864,942],'scope':'Fin942 candidate index/weight equality; no physical ranks, global K or file theorem'},indent=2))
