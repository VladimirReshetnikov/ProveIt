#!/usr/bin/env python3
"""Independent finite checker. Imports no builder or sparse-arithmetic producer."""
import argparse,copy,hashlib,json,subprocess,sys,tempfile
from pathlib import Path
from collections import defaultdict
ROOT=Path(__file__).resolve().parent
SOURCE='incoming210/equations/principal210/equation.json'
SHA='20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a'
def need(x,s):
 if not x:raise ValueError(s)
def raw(x):return(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def sha(x):return hashlib.sha256(raw(x)).hexdigest()
def read(p):return json.loads((ROOT/p).read_text())
def poly(ts,n=None,degree=4):
 d={}
 for c,m in ts:
  need(type(c)is int and c!=0 and type(m)is list and all(type(i)is int and i>=0 and(n is None or i<n)for i in m)and m==sorted(m)and len(m)<=degree,'literal term types, support and degree');t=tuple(m);need(t not in d,'duplicate monomial');d[t]=c
 return d
def plus(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return{m:c for m,c in d.items()if c}
def scale(p,c):return{m:a*c for m,a in p.items()if a*c}
def mul(p,q):
 d=defaultdict(int)
 for m,c in p.items():
  for n,e in q.items():d[tuple(sorted(m+n))]+=c*e
 return{m:c for m,c in d.items()if c}
def sq(p):
 d=defaultdict(int);ts=sorted(p.items())
 for i,(m,c)in enumerate(ts):
  d[tuple(sorted(m+m))]+=c*c
  for n,e in ts[i+1:]:d[tuple(sorted(m+n))]+=2*c*e
 return{m:c for m,c in d.items()if c}
def substitute(p,v,f):
 ans={}
 for m,c in p.items():
  q={tuple(i for i in m if i!=v):c}
  for _ in range(m.count(v)):q=mul(q,f)
  ans=plus(ans,q)
 return ans
def terms(p):return[[c,list(m)]for m,c in sorted(p.items())]
def rows(e):
 need(e.get('domain')=='unrestricted integers','unrestricted integer domain')
 return[poly(r['terms'],len(e['variables']),2)for r in e['residuals']]
def verify_bundle(name,desc,b):
 src=read(SOURCE);ps=rows(src);vars=copy.deepcopy(src['variables']);names={v['name']:i for i,v in enumerate(vars)};V=lambda s:{(names[s],):1};labels={r['label']:i for i,r in enumerate(src['residuals'])};cert=b['certificate'];sc=cert['semantic'];m=desc['m'];need(m in [4,16]and sc['m']==m and sc['centered']==desc['centered'],'proved semantic profile');need(sc['source_sha256']==SHA,'source certificate pin');t,z=names['t0'],names['cofinal.horizon_root'];h=labels['cofinal.horizon'];f={():m,(z,):2*m};need(sc['horizon_row']==h and ps[h]==plus(V('t0'),{():-16,(z,z):-4}),'horizon source binding');ps[h]=plus(V('t0'),scale(f,-1));atom_info={}
 if desc['centered']:
  cc=sc['frame'];T,F=V('t0'),V('growth.F');C=scale(V('crt.even_index_half'),2);q=plus(V('pow2.output'),{():-1});D=plus({():2},scale(F,2),scale(C,2));reps=[V('crt.encoded.'+s)for s in ['a','b','c','d','S','Sp','u','vq']]+[C]
  atoms=[T,plus(T,{():1}),plus(F,T),V('x'),T,V('choose0.output'),F,V('beta.y_plus_one')]+reps+[V('pow1.output'),q,V('pow2.output'),D]+[V('pow%d.output'%i)for i in [3,4,5,7,8,9,10,11,12,13,14,15,16]];fi=labels['shared.frame_definition'];need(len(atoms)==34 and cc['row']==fi and [poly(x)for x in cc['old_atoms']]==atoms,'literal old atom ledger');need(ps[fi]==plus(V('shared.W'),{():-2},*[scale(sq(a),-1)for a in atoms]),'old exact square frame')
  actual=[substitute(a,t,f)for a in atoms];support=sorted({i for a in actual for mon in a for i in mon});bounds=[abs(a.get((),0))+sum(c*c//4 for mon,c in a.items()if mon)for a in actual];constant=max(bounds)+1;l1=max(sum(map(abs,a.values()))for a in actual);need([poly(x)for x in cc['actual_atoms']]==actual and cc['coordinates']==support and cc['bounds']==bounds and cc['constant']==constant and cc['maximum_affine_l1']==l1,'actual affine frame and sharp bounds');need(names['growth.F']in support and constant==m*m+m+2 and l1==3*m+1,'F frame lower bound and Cauchy budget')
  # Bind every actual power port, especially q^t, not a name-only argument.
  requests=[(V('choose0.output'),V('x'),V('pow1.output')),(D,V('x'),q)]
  index_names=['growth.F+t','crt.encoded.a','crt.encoded.b','crt.encoded.c','crt.encoded.d','crt.encoded.S','crt.encoded.Sp','crt.encoded.u','crt.encoded.vq','C']
  ix=[plus(F,T)]+reps[:6]+[reps[6],reps[7],C]
  outputs=[3,5,7,8,9,10,12,13,15,16]
  for k,j in zip(ix,outputs):requests.append((V('pow2.output'),k,V('pow%d.output'%j)))
  requests += [(q,T,V('pow4.output')),(q,V('beta.y_plus_one'),V('pow11.output')),(q,V('x'),V('pow14.output'))]
  need(len(requests)==15 and all(a in atoms for r in requests for a in r),'all fifteen actual power ports in frame');need((q,T,V('pow4.output'))in requests,'retained q^t request')
  # Literal source pooled identities carry this physical q^t request.
  qrows=[ps[labels['radix.bilinear_aggregate']],ps[labels['radix.pooled_norm']]];out=names['pow4.output'];yy=names['index0.Y'];dd=names['index0.X_minus_AY'];need(qrows[0].get(tuple(sorted((out,yy))))==-2 and qrows[1].get((out,out))==1 and qrows[1].get(tuple(sorted((out,dd))))==-2,'physical q^t output and pair pool binding')
  ps[fi]=plus(V('shared.W'),{():-constant},*[{(i,i):-1}for i in support]);oi=labels['cap.pooled_index_residue'];protected={t,names['growth.F'],names['index0.Y'],names['index2.Y']};incoming_ops=read('incoming210/equations/principal210/certificate.json')['operations'];need(all((op['coordinate'] not in protected) if op['type']=='coordinate' else (op['source']!=oi) for op in incoming_ops),'difference delta commutes with all inherited charts and row basis operations');Y0,Y2=V('index0.Y'),V('index2.Y');delta=plus(sq(plus(Y2,scale(Y0,-1),scale(F,-1))),scale(sq(plus(Y2,scale(T,-1),scale(F,-1))),-1));need(sc['difference']['row']==oi and poly(sc['difference']['delta'])==delta,'difference error identity');ps[oi]=plus(ps[oi],delta);atom_info={'atoms':34,'actual_requests':15,'q_to_t_authenticated':True,'underlying_coordinates':len(support),'constant':constant,'maximum_affine_l1':l1}
 unsplit=copy.deepcopy(src);unsplit['variant']='round23_modified_semantic_source'
 for r,p in zip(unsplit['residuals'],ps):r['terms']=terms(p)
 need(unsplit==b['unsplit_modified_source']and sha(unsplit)==sc['output_sha256'],'every unsplit semantic source byte')
 sp=cert['split'];exps=desc.get('split',[]);need(sp['exponents']==exps and sp['input_sha256']==sha(unsplit),'split profile pin');defs=[]
 if exps:
  need(sum(exps)==19 and all(type(a)is int and a>=0 for a in exps),'factorization of 2^19');F,u=names['growth.F'],names['growth_pell.odd_half'];target={(F,):1,(t,):-2**19,tuple(sorted((t,u))):-2**20};jj=[j for j,p in enumerate(ps)if p==target];need(len(jj)==1,'literal growth factorization source');j=jj[0];last=t
  for k,a in enumerate(exps[:-1]):
   w=len(vars);vars.append({'name':f'growth_pell.split{k}','kind':'unit_defined_wire'});d={(w,):1,(last,):-2**a};defs.append({'coordinate':w,'previous':last,'factor':2**a,'row':len(ps)});ps.append(d);last=w
  ps[j]={(F,):1,(last,):-2**exps[-1],tuple(sorted((last,u))):-2**(exps[-1]+1)};need(sp['definitions']==defs and sp['row']==j and sp['last']==last and sp['last_factor']==2**exps[-1],'all monic definitions')
  # Exact composed insertion/forgetting pullback: every added row vanishes.
  lifted=copy.deepcopy(ps)
  for d in reversed(defs):lifted=[substitute(p,d['coordinate'],{(d['previous'],):d['factor']})for p in lifted]
  need(lifted[:len(unsplit['residuals'])]==rows(unsplit)and all(not p for p in lifted[len(unsplit['residuals']):]),'complete monic insertion identities')
 modified=copy.deepcopy(unsplit);modified['variables']=vars
 for k,p in enumerate(ps):
  if k<len(modified['residuals']):modified['residuals'][k]['terms']=terms(p)
  else:modified['residuals'].append({'label':f'growth.split{k-len(unsplit["residuals"])}','terms':terms(p)})
 need(modified==b['modified_source'],'complete split source bytes')
 if exps:need(sp['output_sha256']==sha(modified),'split output pin')
 pc=cert['projection'];keep=[i for i in range(len(vars))if i!=t];need(pc['input_sha256']==sha(modified)and pc['eliminated_coordinate']==t and pc['deleted_row']==h and pc['retained_indices']==keep and poly(pc['replacement'])==f,'unit affine projection map');need(substitute(ps[h],t,f)=={},'deleted horizon row identity');ren={i:j for j,i in enumerate(keep)};projected=[{tuple(ren[i]for i in mon):c for mon,c in substitute(p,t,f).items()}for j,p in enumerate(ps)if j!=h]
 projection={'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers','variables':[vars[i]for i in keep],'residuals':[{'label':f'R{j}','terms':terms(p)}for j,p in enumerate(projected)],'variant':'round23_affine_projection'};need(sha(projection)==pc['output_sha256'],'projection output pin')
 operations=cert['row_operations'];expected_ops=read(desc['row_certificate'])['operations']if desc.get('row_certificate')else[];need(operations==expected_ops,'row certificate selected');out=copy.deepcopy(projected)
 for i,j,k in operations:need(type(k)is int and i!=j and 0<=i<len(out)and 0<=j<len(out),'row operation invertibility');out[i]=plus(out[i],scale(out[j],k))
 inverse=copy.deepcopy(out)
 for i,j,k in reversed(operations):inverse[i]=plus(inverse[i],scale(inverse[j],-k))
 need(inverse==projected,'composed inverse row identity');eq=copy.deepcopy(projection);eq['variant']='round23:'+name
 for r,p in zip(eq['residuals'],out):r['terms']=terms(p)
 need(eq==b['equation']and sha(eq)==cert['output_sha256'],'complete endpoint bytes');full=plus(*[sq(p)for p in out]);need(full==poly(b['expanded_polynomial']['terms'],len(keep),4),'independent unordered-pair SOS expansion');metric={'variables':len(keep),'rows':len(out),'degree':max(map(len,full)),'monomials':len(full),'height':max(map(abs,full.values())),'row_height':max(abs(c)for p in out for c in p.values())};need(metric==b['metrics'],'exact metrics');need(metric['degree']==4 and sorted({v for mon in full for v in mon})==list(range(len(keep))),'quartic degree and every variable live');return{'status':'PASS','metrics':metric,'frame':atom_info,'row_operations':len(operations),'monic_definitions':len(defs),'equation_sha256':sha(eq)}
def bundle(name):return{n:read(f'{name}/{n}.json')for n in ['equation','expanded_polynomial','metrics','certificate','modified_source','unsplit_modified_source']}
def mutations(name,desc,b):
 cases=[]
 def reject(label,mutate):
  bad=copy.deepcopy(b);mutate(bad)
  try:verify_bundle(name,desc,bad)
  except(ValueError,KeyError,IndexError,TypeError):cases.append(label)
  else:raise ValueError('mutation accepted: '+label)
 reject('horizon multiplier',lambda b:b['certificate']['semantic'].__setitem__('m',8))
 reject('unrestricted domain changed',lambda b:b['equation'].__setitem__('domain','nonnegative integers'))
 reject('literal residual coefficient',lambda b:b['equation']['residuals'][0]['terms'][0].__setitem__(0,99))
 reject('expanded coefficient',lambda b:b['expanded_polynomial']['terms'][0].__setitem__(0,99))
 reject('metric height',lambda b:b['metrics'].__setitem__('height',1))
 reject('projection inverse expression',lambda b:b['certificate']['projection']['replacement'][0].__setitem__(0,99))
 if desc['centered']:
  reject('affine atom bound',lambda b:b['certificate']['semantic']['frame']['bounds'].__setitem__(0,999))
  reject('orientation difference',lambda b:b['certificate']['semantic']['difference']['delta'][0].__setitem__(0,999))
 if desc.get('split'):reject('monic growth scale',lambda b:b['certificate']['split']['definitions'][0].__setitem__('factor',3))
 if b['certificate']['row_operations']:reject('residual inverse step',lambda b:b['certificate']['row_operations'][0].__setitem__(2,999))
 return{'rejected':len(cases),'cases':cases}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);ap.add_argument('--deep',action='store_true');ap.add_argument('--skip-manifest',action='store_true');args=ap.parse_args();need(hashlib.sha256((ROOT/SOURCE).read_bytes()).hexdigest()==SHA,'incoming literal source bytes');result={'status':'PASS','optimized_python':bool(sys.flags.optimize),'source_sha256':SHA,'endpoints':{}}
 for name,desc in read('ENDPOINTS.json').items():
  b=bundle(name);result['endpoints'][name]=verify_bundle(name,desc,b);result['endpoints'][name]['mutations']=mutations(name,desc,b)
 need(hashlib.sha256((ROOT/'conservative209/equation.json').read_bytes()).hexdigest()=='27eec42f8010ef84ed427a0e78c1f7ffe2c5bd1baf712d87cfb0f18f23dd4d63','frozen reciprocal source')
 python=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[])
 for command in [['build.py','--check'],['coordinate_maps.py','check']]+([['incoming210/verify.py']]if args.deep else[]):
  p=subprocess.run(python+[str(ROOT/command[0])]+command[1:],capture_output=True,text=True,cwd=ROOT);need(p.returncode==0,'subprocess '+str(command)+' '+p.stderr+' '+p.stdout[-1000:]);result[' '.join(command)]=json.loads(p.stdout)
 if not args.skip_manifest:
  manifest=read('MANIFEST_SHA256.json');need(set(manifest)==set(read('WHITELIST.json')['files'])-{'MANIFEST_SHA256.json','WHITELIST.json'},'manifest inventory equality')
  for fn,h in manifest.items():need(hashlib.sha256((ROOT/fn).read_bytes()).hexdigest()==h,'manifest '+fn)
  result['manifest_files']=len(manifest)
 s=json.dumps(result,indent=2)+'\n';print(s,end='')
 if args.receipt:args.receipt.write_text(s)
if __name__=='__main__':main()
