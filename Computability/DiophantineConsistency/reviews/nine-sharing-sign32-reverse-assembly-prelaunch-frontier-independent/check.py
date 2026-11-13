#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-reverse-assembly-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'6ee167bb1003f83708923037e0107378d7fdd533d3ad572daeb47a16824ae07b','survey.py':'c188b08dd16285174f5c88952e63f5b9b927f0a1ea599f0002672c7040fb4304','providers.json':'f46e4aad54ea1f5659b671fb6f677f6b9d3bb95098adbd04526125def9d5e987','source-manifest.json':'11498d0b7d0c2a34f73236be1101530854baedcf6bac722369d84fd75bc27736'}.items():assert sha(P/n)==h
old=json.loads((D/'research/nine-sharing-quartic65-sign33-candidate/seed.json').read_text());new=json.loads((D/'research/nine-sharing-sign32-sextic-candidate-v2/seed.json').read_text());names=[x['gate'] for x in new['residuals']];assert names==[x['gate'] for x in old['residuals'][1:]] and len(names)==23 and len(set(names))==23
rows=json.loads((P/'source-manifest.json').read_text())['rows'];hashes=['51922775c5abdb1765209e95212ccce6d009fe626442b0d7799260f65345d0e6','affc7e9ad7e8b836ceee6def5e26804a5b2c0528c22fcf22fbbcbf8cd69e1cb2','5444f6f2a58e21c515f4ca8bb67660c61813fa6ae31d831732093eea9abff2af','1f257ea723c607b5774641886ff9499030dd7428c62b6bce84897036561cfc12'];modules=['Sign32ReverseAssembly00','Sign32ReverseAssembly01','Sign32ReverseAssembly02','Sign32ReverseAssemblyAll'];imports=['Sign32CoordinateReconstruct']+modules[:-1];assert len(rows)==4
contents=[]
for r,m,h,im in zip(rows,modules,hashes,imports):
 p=P/'src/DiophantineConsistency'/f'{m}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+m and r['imports']==['DiophantineConsistency.'+im]==re.findall(r'^import ([\w.]+)$',s,re.M);contents.append(s)
allproof='\n'.join(contents[:3]); expected_groups={'q3':0,'X':1,'Y':1,'E':1,'kY':2,'ell':2,'Delta':2,'main_root':3,'c2':3,'Dc2':3,'N1':4,'gap':4,'tau':4,'N0':5,'Nt':5,'f2':5,'cTminusR':6,'V':6,'normalized_S':6,'normalized_S2':7,'V2minusY2':7,'Na':7,'scaled_Ns':7};aliases={'main_root':'mainRoot','normalized_S':'normalizedS','normalized_S2':'normalizedS2','scaled_Ns':'scaledNs'}
assert set(names)==set(expected_groups)
for n in names:
 alias=aliases.get(n,n);g=expected_groups[n];m=re.search(r'^theorem '+re.escape(alias)+r'_zero\b(.*?)(?=^theorem |^end )',allproof,re.M|re.S);assert m,n;t=m[1]
 assert '(v : Fin 33 → V)' in t and 'InternalZero e (Sign32Substitution00.lift beta v)' in t
 if n=='q3':assert 'InternalZero (SharingSeed32Sextic.firstResidual p) v' in t and 'Sign32Substitution00.old_q3_head p' in t and '← Sign32Substitution00.old_q3_eval p beta v hp0' in t
 else:assert f'InternalZero (Sign32Substitution{g:02d}.new{alias} p) v' in t and f'Sign32Substitution{g:02d}.old_{alias}_row p' in t and f'← Sign32Substitution{g:02d}.{alias}_eval p beta v' in t
 assert ('(hp0 :' in t)==(n in ('q3','tau','cTminusR'))
 if n in ('q3','tau','cTminusR'):assert '((p 0 : ℤ) : DiffRing V) = ι beta' in t and 'p beta v hp0' in t
z=contents[3];enum=z.split('theorem new_rows',1)[1].split(':= by',1)[0];listed=re.findall(r'Sign32Substitution\d+\.new(\w+) p',enum);assert listed==[aliases.get(n,n) for n in names[1:]]
assert 'SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p' in enum and len(listed)==22
body=z.split('theorem source33_to_source32',1)[1];assert 'InternalZero (SharingSeed33.seed p) v' in body and 'InternalZero (SharingSeed32Sextic.seed p) (Sign32CoordinateRecover.drop v)' in body and '((p 0 : ℤ) : DiffRing V) = ι beta' in body
assert body.count('rfl |')==22 and 'Sign32CoordinateRecover.lift_drop p beta v hp0 hz' in body
calls=re.findall(r'^  · exact (\w+)_zero p beta \(Sign32CoordinateRecover.drop v\)(?: hp0)? ho$',body,re.M);assert calls==[aliases.get(n,n) for n in names]
pre=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not pre.stderr;x=json.loads(pre.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==4
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'transfer_count':23,'new_enumeration':23,'cast_dependent':['q3','tau','cTminusR'],'scope':'reverse proposed same-valuation 33→32 zero-set only; no Lean or full iff'},indent=2,sort_keys=True))
