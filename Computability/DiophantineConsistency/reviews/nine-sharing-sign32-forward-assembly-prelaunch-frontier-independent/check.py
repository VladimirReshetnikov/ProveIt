#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-forward-assembly-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'700bba88ee4a579c03c1e48e13787280ae930520db6275a0132086b0bb534046','survey.py':'5f443546621c14ed1283aeff03192f0226235b6ff0a6b165faa786515447276e','providers.json':'f46e4aad54ea1f5659b671fb6f677f6b9d3bb95098adbd04526125def9d5e987','source-manifest.json':'4a57e6ba3689df0c28d09f922ff54afe6f2e9ad7c936a2effbc870995825b584'}.items():assert sha(P/n)==h
old=json.loads((D/'research/nine-sharing-quartic65-sign33-candidate/seed.json').read_text());new=json.loads((D/'research/nine-sharing-sign32-sextic-candidate-v2/seed.json').read_text());names=[x['gate'] for x in new['residuals']];assert names==[x['gate'] for x in old['residuals'][1:]] and len(names)==23 and len(set(names))==23
rows=json.loads((P/'source-manifest.json').read_text())['rows'];hashes=['7b10cc2caeaa064ce01c95bf6fde1cff3d3f4e3f8c9baf08fcc7e05a8f523525','68e71940d4eb7a56ab823e9f5473a202ee807fa0e8726d34f66517d7f8615274','10824e56a20598cf907bb995887ea223b9088c10e8fc844da266d45275fca468','82b4f997ab21a584696b74d8a1dd713a1422ec0feb032f2b4d5b6db826a124a8'];modules=['Sign32ForwardAssembly00','Sign32ForwardAssembly01','Sign32ForwardAssembly02','Sign32ForwardAssemblyAll'];imports=['Sign32Substitution07']+modules[:-1];assert len(rows)==4
contents=[]
for r,m,h,im in zip(rows,modules,hashes,imports):
 p=P/'src/DiophantineConsistency'/f'{m}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+m and r['imports']==['DiophantineConsistency.'+im]==re.findall(r'^import ([\w.]+)$',s,re.M);contents.append(s)
allproof='\n'.join(contents[:3]); expected_groups={'q3':0,'X':1,'Y':1,'E':1,'kY':2,'ell':2,'Delta':2,'main_root':3,'c2':3,'Dc2':3,'N1':4,'gap':4,'tau':4,'N0':5,'Nt':5,'f2':5,'cTminusR':6,'V':6,'normalized_S':6,'normalized_S2':7,'V2minusY2':7,'Na':7,'scaled_Ns':7};aliases={'main_root':'mainRoot','normalized_S':'normalizedS','normalized_S2':'normalizedS2','scaled_Ns':'scaledNs'}
assert set(names)==set(expected_groups)
for n in names:
 alias=aliases.get(n,n);g=expected_groups[n];m=re.search(r'^theorem '+re.escape(alias)+r'_zero\b(.*?)(?=^theorem |^end )',allproof,re.M|re.S);assert m,n;t=m[1]
 assert '(v : Fin 33 → V)' in t and 'InternalZero e v' in t and 'Sign32Substitution00.lift beta v' in t
 assert f'Sign32Substitution{g:02d}.old'+('Q3' if n=='q3' else alias)+' p' in t
 if n=='q3':assert 'Sign32Substitution00.old_q3_eval p beta v hp0' in t and 'List.mem_cons_self' in t
 else:assert f'Sign32Substitution{g:02d}.new_{alias}_row p' in t and f'Sign32Substitution{g:02d}.{alias}_eval p beta v' in t
 assert ('(hp0 :' in t)==(n in ('q3','tau','cTminusR'))
 if n in ('q3','tau','cTminusR'):assert '((p 0 : ℤ) : DiffRing V) = ι beta' in t and 'p beta v hp0' in t
z=contents[3];enum=z.split('theorem old_rows',1)[1].split(':= by',1)[0];listed=re.findall(r'Sign32Substitution\d+\.old(\w+) p',enum);assert listed==[('Q3' if n=='q3' else aliases.get(n,n)) for n in names]
assert 'SharingSeed33.firstResidual p :: SharingSeed33.remainingResiduals p' in enum and len(listed)==23
body=z.split('theorem source32_to_source33',1)[1];assert 'InternalZero (SharingSeed32Sextic.seed p) v' in body and 'InternalZero (SharingSeed33.seed p) (Sign32Substitution00.lift beta v)' in body and '((p 0 : ℤ) : DiffRing V) = ι beta' in body
assert body.count('rfl |')==23 and 'Sign32Substitution00.old_q2_zero p beta v hp0' in body
calls=re.findall(r'^  · exact (\w+)_zero p beta v(?: hp0)? hn$',body,re.M);assert calls==[aliases.get(n,n) for n in names]
pre=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not pre.stderr;x=json.loads(pre.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==4
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'transfer_count':23,'old_enumeration':24,'cast_dependent':['q3','tau','cTminusR'],'scope':'forward proposed same-valuation 32→33 zero-set only; no Lean or reverse bridge'},indent=2,sort_keys=True))
