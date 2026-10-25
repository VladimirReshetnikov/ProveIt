#!/usr/bin/env python3
"""Independent exact source/contraction review, data-only; no author imports."""
from pathlib import Path
from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
import json
from copy import deepcopy
from tempfile import TemporaryDirectory
R=Path(__file__).resolve().parents[1];D=R;OUT=R/'review'
def need(b,m):
 if not b:raise ValueError(m)
def read(p):return json.loads(p.read_text())
def h(p):return sha256(p.read_bytes()).hexdigest()
def canon(x):return sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def collect(ts):
 z=defaultdict(int)
 for c,m in ts:z[tuple(sorted(m))]+=c
 return {m:c for m,c in z.items() if c}
def plus(*ps):return collect((c,m) for p in ps for m,c in p.items())
def neg(p):return {m:-c for m,c in p.items()}
def times(p,q):return collect((a*b,m+n) for m,a in p.items() for n,b in q.items())
def sub(p,q):return plus(p,neg(q))
def atom(x):return {(x,):1}
def literal(x):return {():x} if x else {}
def named(eq,row):return collect((c,tuple(eq['variables'][i]['name'] for i in m)) for c,m in row['terms'])
def source_check(old,new):
 need(old['domain']==new['domain']=='nonnegative integers','domains')
 op=[named(old,r) for r in old['residuals']];np=[named(new,r) for r in new['residuals']]
 need(len({v['name'] for v in new['variables']})==len(new['variables']),'names')
 gone=[];fresh=[]
 def bind(rows,seq,name,rhs):
  v=sub(atom(name),rhs);hits=[i for i,p in enumerate(rows) if p==v];need(len(hits)==1,'literal definition '+name);seq.extend(hits);return atom(name)
 # Independently identify all removed square definitions from the actual row containing the gate.
 delta=sub(atom('crt.encoded.S'),atom('crt.encoded.Sp'))
 mnames=['mul.'+str(k) for k in (339,341,343,345,347,349,351,353)]
 ds=[delta]+[sub(delta,atom(k)) for k in mnames]
 ds +=[sub(atom('crt.encoded.a'),atom('crt.encoded.c')),sub(atom('crt.encoded.b'),atom('crt.encoded.c')),
       sub(atom('mul.355'),atom('mul.357')),sub(delta,atom('mul.358')),
       sub(atom('mul.363'),atom('mul.369')),sub(atom('mul.372'),atom('mul.373'))]
 for i,t in enumerate(ds):bind(op,gone,'sqd.'+str(i),times(t,t))
 bind(op,gone,'mul.355',times(atom('sqd.9'),atom('sqd.10')))
 dd=plus(atom('crt.encoded.d'),literal(2));bind(op,gone,'mul.357',times(dd,dd))
 v=atom('sqd.0')
 for k in range(1,9):v=bind(op,gone,'mul.'+str(373+k),times(v,atom('sqd.'+str(k))))
 v=bind(op,gone,'mul.382',times(v,plus(atom('sqd.11'),atom('sqd.12'))))
 v=bind(op,gone,'mul.383',times(v,atom('sqd.13')));v=bind(op,gone,'mul.384',times(v,atom('sqd.14')))
 gs=[neg(t) for t in ds[:9]]+[neg(ds[13]),ds[14]]
 w=gs[0]
 for k,g in enumerate(gs[1:],1):w=bind(np,fresh,'oriented.product'+str(k),times(w,g))
 ee=bind(np,fresh,'oriented.inequality_product',times(ds[9],ds[10]))
 z=bind(np,fresh,'oriented.inequality_minus',times(w,sub(ee,dd)))
 z=bind(np,fresh,'oriented.inequality_branch',times(z,plus(ee,dd)))
 t=bind(np,fresh,'oriented.axiom_branch',times(w,neg(ds[12])))
 oe=plus(v,atom('sqd.15'),atom('sqd.16'),neg(atom('mul.407')))
 ne=plus(times(z,z),times(t,t),atom('sqd.15'),atom('sqd.16'),neg(atom('mul.407')))
 oi=[i for i,r in enumerate(old['residuals']) if r['label']=='crt.nonnegative_evaluation'];ni=[i for i,r in enumerate(new['residuals']) if r['label']=='crt.oriented_nonnegative_evaluation']
 need(len(oi)==len(ni)==1,'evaluation row retained');need(op[oi[0]]==oe and np[ni[0]]==ne,'source values')
 oldremain=[(r['label'],op[i]) for i,r in enumerate(old['residuals']) if i not in gone+oi]
 newremain=[(r['label'],np[i]) for i,r in enumerate(new['residuals']) if i not in fresh+ni]
 need(oldremain==newremain,'all untouched rows')
 # Whole source identity over four formal inputs Q,E,D,G.
 Q,E,Dd,G=map(atom,['Q','E','D','G']);z=times(Q,times(sub(E,Dd),plus(E,Dd)));t=times(Q,G)
 need(plus(times(z,z),times(t,t))==times(times(Q,Q),plus(times(sub(times(E,E),times(Dd,Dd)),sub(times(E,E),times(Dd,Dd))),times(G,G))),'whole formal identity')
 need((len(gone),len(fresh),len(oldremain),len(new['variables']),len(new['residuals']))==(28,14,247,310,262),'census')
 need({i for row in new['residuals'] for c,m in row['terms'] for i in m}==set(range(310)),'raw liveness')
 return {'old_file_sha256':h(D/'inherited/cofinal_raw/equation.json'),'new_file_sha256':h(D/'raw/equation.json'),'old_object_sha256':canon(old),'new_object_sha256':canon(new),'unchanged_rows':247,'removed_rows':28,'added_rows':14,'identity':'PASS'}
def subst(poly,v,r):
 ts=[]
 for m,c in poly.items():
  z=literal(c)
  for a in m:z=times(z,r if a==v else atom(a))
  ts.extend((c,m) for m,c in z.items())
 return collect(ts)
def contraction(raw,path):
 target=read(path/'equation.json');cert=read(path/'elimination_certificate.json')
 need(cert['source_equation_sha256']==canon(raw),'source object hash');need(cert['target_equation_sha256']==canon(target),'target object hash')
 rows={i:collect((c,m) for c,m in row['terms']) for i,row in enumerate(raw['residuals'])};live=set(range(len(raw['variables'])));negative=[]
 for sn,step in enumerate(cert['steps']):
  row,v,sign=step['source_row_id'],step['variable_original_index'],step['pivot_sign'];restore=collect((c,m) for c,m in step['restoration'])
  need(row in rows and v in live and sign in (-1,1),'pivot '+str(sn));need(v not in {a for m in restore for a in m},'self-referential restore')
  need(all(isinstance(c,int) and set(m)<=live for m,c in restore.items()),'integral live restore')
  need(rows[row]==collect((c,m) for c,m in step['row_before']),'recorded pivot')
  need(rows[row]==plus({(v,):sign},{m:-sign*c for m,c in restore.items()}),'monic identity')
  nn=step['nonnegative_certificate'];total=literal(0)
  for c,m in nn['nonnegative_remainder']:
   need(c>0 and set(m)<=live,'nonnegative monomial');total=plus(total,{tuple(m):c})
  for sq in nn['squares']:
   weight=Fraction(*sq['weight']);need(weight>0,'positive square weight');aff=collect((Fraction(*c),m) for c,m in sq['affine_form']);need(all(len(m)<=1 and set(m)<=live for m in aff),'affine square');total=plus(total,{m:weight*c for m,c in times(aff,aff).items()})
  need(total==restore,'complete positivity certificate')
  if any(c<0 for c in restore.values()):negative.append({'step':sn,'variable':step['variable_name'],'restoration':step['restoration'],'certificate':nn})
  del rows[row];live.remove(v)
  rows={i:subst(p,v,restore) for i,p in rows.items()};need(all(len(m)<=2 for p in rows.values() for m in p),'quadratic preserved')
 ids=[i for i,p in rows.items() if p];need(ids==cert['surviving_source_row_ids_in_target_order'],'row order')
 retained=cert['retained_original_indices_in_target_order'];unused=cert['unused_original_indices_restored_to_zero'];need(set(retained)|set(unused)==live and not set(retained)&set(unused),'live partition');need(len(set(retained))==len(retained),'unique retained');need(set(retained)=={a for poly in rows.values() for m in poly for a in m},'exact coordinate liveness');need([i for i,p in rows.items() if not p]==cert['zero_source_row_ids'],'zero rows');ren={x:i for i,x in enumerate(retained)}
 need(target['domain']==raw['domain']=='nonnegative integers','target domain');need(target['variables']==[raw['variables'][i] for i in retained],'variables exact')
 need(len(target['residuals'])==len(ids),'rowcount')
 for rid,tr in zip(ids,target['residuals']):need(collect((c,[ren[i] for i in m]) for m,c in rows[rid].items())==collect((c,m) for c,m in tr['terms']) and tr['label']==raw['residuals'][rid]['label'],'all final rows')
 full=plus(*(times(collect((c,m) for c,m in r['terms']),collect((c,m) for c,m in r['terms'])) for r in target['residuals']))
 need(full==collect((c,m) for c,m in read(path/'expanded_polynomial.json')['terms']),'every expanded coefficient')
 return {'path':str(path.relative_to(R)) if path.is_relative_to(R) else str(path),'equation_sha256':h(path/'equation.json'),'expansion_sha256':h(path/'expanded_polynomial.json'),'certificate_sha256':h(path/'elimination_certificate.json'),'variables':len(retained),'rows':len(ids),'degree':max(map(len,full)),'terms':len(full),'height':max(map(abs,full.values())),'eliminations':len(cert['steps']),'negative_coefficient_restorations':negative,'status':'PASS'}
def main():
 old=read(D/'inherited/cofinal_raw/equation.json');raw=read(D/'raw/equation.json')
 need(h(D/'inherited/cofinal_raw/equation.json')=='c0bad9e9b861410b9dad70ff6bb2138e52448dcd27f13e665bf749389d7d7e61','parent exact frozen file binding')
 result={'scope':'Independent source delta, exact identities, all selected monic/nonnegative restorations and complete coefficient lists; no incoming code executed','source':source_check(old,raw),'endpoints':[contraction(raw,D/name) for name in ('dimension206','projected207','projected208')]}
 negative=[]
 def rejects(label,fn):
  try:fn()
  except ValueError as err:negative.append({'case':label,'rejection':str(err)})
  else:raise ValueError('negative control accepted: '+label)
 x=deepcopy(raw);x['residuals']=[r for r in x['residuals'] if r['label']!='crt.oriented_nonnegative_evaluation'];rejects('missing source evaluation',lambda:source_check(old,x))
 x=deepcopy(raw);x['residuals'][-1]['terms'][0][0]+=1;rejects('wrong new branch coefficient',lambda:source_check(old,x))
 x=deepcopy(raw);x['residuals'][0]['terms'][0][0]+=1;rejects('unrelated old source edit',lambda:source_check(old,x))
 x=deepcopy(raw);x['domain']='unrestricted integers';rejects('widened source domain',lambda:source_check(old,x))
 # Exercise the complete contraction checker in disposable copies only.
 base=D/'dimension206'
 for mode in ('negative square weight','wrong restoration','corrupt expansion'):
  with TemporaryDirectory(prefix='round20-natural-review-') as tmp:
   td=Path(tmp)
   for name in ('equation.json','elimination_certificate.json','expanded_polynomial.json'):(td/name).write_bytes((base/name).read_bytes())
   if mode=='corrupt expansion':
    v=read(td/'expanded_polynomial.json');v['terms'][0][0]+=1;(td/'expanded_polynomial.json').write_text(json.dumps(v))
   else:
    v=read(td/'elimination_certificate.json')
    if mode=='negative square weight':
     step=next(z for z in v['steps'] if z['nonnegative_certificate']['squares']);step['nonnegative_certificate']['squares'][0]['weight'][0]*=-1
    else:v['steps'][0]['restoration'][0][0]+=1
    (td/'elimination_certificate.json').write_text(json.dumps(v))
   rejects(mode,lambda:contraction(raw,td))
 result['negative_controls_rejected']=negative
 (OUT/'PORTABLE_INDEPENDENT.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='endpoints'},indent=2))
 for e in result['endpoints']:print(e['path'],tuple(e[k] for k in ('variables','rows','degree','terms','height')),'negative restores',len(e['negative_coefficient_restorations']))
if __name__=='__main__':main()
