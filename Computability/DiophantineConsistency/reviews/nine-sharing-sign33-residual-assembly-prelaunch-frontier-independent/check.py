#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-assembly-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'20d89d741a47669b4bcfd2d6d10b2318168ce24202310c9754ca3abc5f97c078','provider_survey.py':'33390bab8bd394f27c922a1fb97da2fa3f211164115410d293817b3e6e9d4325','source-manifest.json':'423c609b25efb5ed55f2edcea37a9dafff322d76dc913168836bc17f3f8e1aa5','src/DiophantineConsistency/Sign33ResidualAssembly.lean':'da9229b543500e40d4a3d5fa100fe11a969b58bcdc4f280d385abf3617ba2358'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='da9229b543500e40d4a3d5fa100fe11a969b58bcdc4f280d385abf3617ba2358';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33ResidualBatch%02d'%i for i in range(8)];assert re.findall(r'^theorem (\w+)',s,re.M)==['all_cuts_of_seed_zero']
names=['three_cuts_of_seed_zero']*3+['two_cuts_and_norm_of_seed_zero','signed_cuts_and_norm_of_seed_zero','transport_and_cuts_of_seed_zero','three_cuts_of_seed_zero','cut_and_norms_of_seed_zero']
for i,n in enumerate(names):
 b=(d/f'research/nine-sharing-sign33-residual-batch{i:02}-check/src/DiophantineConsistency/Sign33ResidualBatch{i:02}.lean').read_text();b=b.split('theorem '+n,1)[1].split(':= by',1)[0].rsplit(' :\n',1)[-1];f=re.search(r'  batch%02d :\n(.*?)(?=\n  batch\d\d :|\n\ntheorem)'%i,s,re.S).group(1);f=f.replace('Sign33ResidualBatch%02d.'%i,'');norm=lambda x:re.sub(r'\s+','',x);assert norm(b)==norm(f);assert f'Sign33ResidualBatch{i:02}.{n} p ' in s
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'conclusions_compared':8,'scope':'uncompiled one-way assembly; no Lean replay'},sort_keys=True,indent=2))
