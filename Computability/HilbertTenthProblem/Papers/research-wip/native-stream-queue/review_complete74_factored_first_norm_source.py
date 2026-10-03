#!/usr/bin/env python3
"""Independent bounded literal-source audit. Standard-library, authenticated inputs."""
import argparse,copy,hashlib,json,random,tempfile,subprocess,sys
from pathlib import Path
from collections import Counter
from fractions import Fraction
if not __debug__:raise RuntimeError('Run without -O')
AUTHOR_PINS={
 'complete74_factored_first_norm.py':'7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908',
 'complete74_factored_first_norm.json':'7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28',
 'complete74_factored_first_norm.md':'119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f'}
PINS={
 'complete75_half_binomial.py':'5383b009a41abc19bb4c94e3f25c96ccfd4122d6a016c27b54fda0a75f7acab5',
 'complete75_half_binomial.json':'a46ffb29e0d0db2f6c531edb442f0b5adb0f29a8a3f13dcdd8be9c64b4d17ea0',
 'complete75_positive_elimination.py':'70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749',
 'complete75_positive_elimination.json':'03743efca27972fd97667501af214626481acb4993ed006b9d4033766c0ec703',
 'complete75_signed_projection_elimination101.py':'5a781fdacabab7feda2a8879c1cc207936045a1e4aa063c064a0bfffcdc9b4c8',
 'complete75_signed_projection_elimination101.json':'00de69d028b79d3837bbd892a202d78d95092711d68ca6f40bf7d5e2ab20c3e3'}
CONST=('Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF')
MODES=('raw30','positive22','signed20')
def require(ok,msg):
 if not ok:raise AssertionError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def same(a,b):return canonical(a)==canonical(b)
def plus(a,b,sign=1):
 c=a.copy()
 for m,v in b.items():c[m]=c.get(m,0)+sign*v
 return {m:v for m,v in c.items() if v}
def times(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   z=tuple(sorted(m+n));c[z]=c.get(z,0)+v*w
 return {m:v for m,v in c.items() if v}
def atom(x):return {():x} if type(x)is int else {(x,):1}
def poly_run(rows,initial):
 e=dict(initial)
 for n,op,a,b in rows:
  if n in e:continue
  if (type(a)is int or a in e) and (type(b)is int or b in e):
   aa=atom(a) if type(a)is int else e[a];bb=atom(b) if type(b)is int else e[b]
   e[n]=times(aa,bb) if op=='*' else plus(aa,bb,1 if op=='+' else -1)
 return e
def scalar(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
  e[n]={'*':lambda:a*b,'+':lambda:a+b,'-':lambda:a-b}[op]()
 return e
def finish(rows,pairs):
 out=copy.deepcopy(rows);squares=[]
 for i,(a,b) in enumerate(pairs):
  r=f'residual_{i}';s=f'square_{i}';out += [[r,'-',a,b],[s,'*',r,r]];squares.append(s)
 acc=squares[0]
 for i,s in enumerate(squares[1:],1):n=f'sum_{i}';out.append([n,'+',acc,s]);acc=n
 return out,acc
def ledger(rows,ports):
 names={r[0] for r in rows};free={x for r in rows for x in r[2:] if type(x)is str and x not in names};seen=set(free);table={}
 require(len(names)==len(rows),'unique names')
 for n,op,a,b in rows:
  require(n not in seen and op in ('+','-','*'),'DAG row')
  require(all(type(x)is int or type(x)is str and x in seen for x in (a,b)),'closed exact DAG')
  table[n]=(a,b);seen.add(n)
 live=set();todo=list(ports)
 while todo:
  x=todo.pop()
  if type(x)is int or x in free or x in live:continue
  require(x in table,'live terminal');live.add(x);todo.extend(table[x])
 require(live==names,'all charged gates live')
 c=Counter(r[1] for r in rows)
 return {'M':c['*'],'A':c['+']+c['-'],'operations':len(rows),'free':sorted(free),'all_gates_live':True}
def upper_leaders(rows,pairs,mode):
 # Exact top homogeneous coefficients at conservative formal degrees.
 # All six fixed numerals have weight zero; every supplied input has weight one.
 env={};free=ledger(rows,[x for p in pairs for x in p])['free']
 for x in free:env[x]=(0 if x in CONST else 1,atom(x))
 def add(a,b,sgn=1):
  d=max(a[0],b[0]);pa=a[1] if a[0]==d else {};pb=b[1] if b[0]==d else {}
  return d,plus(pa,pb,sgn)
 def mul(a,b):return a[0]+b[0],times(a[1],b[1])
 def val(x):return (0,atom(x)) if type(x)is int else env[x]
 for n,op,a,b in rows:env[n]=mul(val(a),val(b)) if op=='*' else add(val(a),val(b),1 if op=='+' else -1)
 d={n:(op,a,b) for n,op,a,b in rows};res=[]
 for l,r in pairs:
  v=add(val(l),val(r),-1)
  if mode!='raw30' and (l,r) in [('L15','R15'),('mu2','norm_rhs')]:
   if l=='L15':
    require(d['L15']==('*','R14','R14') and d['R14']==('+','D1','gam') and d['D1']==('+','wn2','cam2') and d['cam2']==('*','R10a','R12'),'main norm literal cone')
    z=val('R10a');extra=add(val('wn2'),val('gam'))
   else:
    require(d['mu2']==('*','exponent_rhs','exponent_rhs') and d['exponent_rhs']==('+','exponent_partial','modulus_multiple') and d['exponent_partial']==('+','W','difference_multiple') and d['difference_multiple']==('*','index_rhs','R12'),'input norm literal cone')
    z=val('index_rhs');extra=add(val('W'),val('modulus_multiple'))
   require(d['A']==('+','a_square','a4m5') and d['a_square']==('*','R12','R12'),'actual discriminant')
   # (az+v)^2-(a²+H)z²-1 = 2azv+v²-Hz²-1.
   v=add(add(add(mul((0,atom(2)),mul(mul(val('R12'),z),extra)),mul(extra,extra)),mul(val('a4m5'),mul(z,z)),-1),(0,atom(1)),-1)
  res.append(v)
 D=max(d for d,p in res);top={}
 for d,p in res:
  if d==D:top=plus(top,times(p,p))
 if mode=='raw30':mon=tuple(sorted(['w']*4+['s']*8+['k']*4+['q']*36));coef=1;wantD=52
 else:mon=tuple(sorted(['Bm1']*60+['delta']*4+['w']*10+['s']*10+['Jrep']*60));coef=16;wantD=84
 require(2*D==wantD and top=={mon:coef},'uniform exact top homogeneous term')
 return {'residual_degree_upper_bounds':[d for d,p in res],'exact_degree':2*D,'top_coefficient':coef,'top_monomial':dict(Counter(mon))}
def verify(root,source_root):
 for n,h in PINS.items():require(digest((root/n).read_bytes())==h,'parent pin '+n)
 for n,h in AUTHOR_PINS.items():require(digest((source_root/n).read_bytes())==h,'author pin '+n)
 raw=json.loads((root/'complete75_half_binomial.json').read_text())['source']
 pos=json.loads((root/'complete75_positive_elimination.json').read_text())
 sig=json.loads((root/'complete75_signed_projection_elimination101.json').read_text())['source']
 receipt=json.loads((source_root/'complete74_factored_first_norm.json').read_text())
 path=source_root/'complete74_factored_first_norm.py';api={'__name__':'_independent_complete74','__file__':str(path)};exec(compile(path.read_bytes(),str(path),'exec'),api)
 counts=Counter();forms=[];rng=random.Random(74130)
 # Independent symbolic proof of both needed cancellation identities.
 X,Y,K,A,Z,V,H=[atom(n) for n in ('X','Y','K','A','Z','V','H')]
 L=times(times(X,Y),times(K,Y))
 require(times(plus(times(times(X,Y),times(X,Y)),X),times(times(K,Y),times(K,Y)))==times(L,plus(L,K)),'universal factor identity')
 require(plus(times(plus(times(A,Z),V),plus(times(A,Z),V)),times(plus(times(A,A),H),times(Z,Z)),-1)==plus(plus(times(atom(2),times(times(A,Z),V)),times(V,V)),times(H,times(Z,Z)),-1),'norm cancellation identity')
 for mode in MODES:
  if mode=='raw30':rows=raw['schedule'];pairs=[x['equality'] for x in raw['sources']]
  elif mode=='positive22':rows=pos['polynomial_schedule'][:75];pairs=pos['retained_equalities']
  else:rows=sig['polynomial_schedule'][:75];pairs=sig['comparisons']
  p=next(x['packet'] for x in receipt['forms'] if x['mode']==mode);c=api['rewrite'](root,mode)
  require(same(p,c),'actual emitted saved source')
  k='k' if mode=='raw30' else 'R10b';old={n:[op,a,b] for n,op,a,b in rows}
  require(old['UM']==['*','wn2','sn2'] and old['ksn2']==['*',k,'sn2'],'actual coefficient ports')
  private={'UM2':'scaled_norm_coefficient','scaled_norm_coefficient':'L9','ratio_product2':'L9'}
  for n,user in private.items():
   require([r[0] for r in rows if n in r[2:]]==[user] and all(n not in q for q in pairs),'privacy')
   counts['private_consumer_checks']+=1
  oldfiltered=[r for r in rows if r[0] not in {*private,'L9'}]
  newfiltered=[r for r in p['source'] if r[0] not in {'first_root_base','first_next','L9'}]
  require(oldfiltered==newfiltered and pairs==p['comparisons'],'all other source rows and comparisons exact')
  counts['unchanged_actual_rows']+=len(oldfiltered)
  for r in [['first_root_base','*','UM','ksn2'],['first_next','+','first_root_base',k],['L9','*','first_root_base','first_next']]:require(r in p['source'],'literal replacement')
  cut={'wn2':atom('X'),'sn2':atom('Y'),k:atom('K')}
  a=poly_run(rows,cut)['L9'];b=poly_run(p['source'],cut)['L9'];require(a==b,'actual cone expanded identity');counts['literal_coefficient_identities']+=1
  oldpoly,oldout=finish(rows,pairs);newpoly,newout=finish(p['source'],pairs)
  require(newpoly==p['polynomial_source'] and newout==p['output'],'complete SOS exact')
  require(newpoly[len(p['source']):]==oldpoly[len(rows):],'every finalizer gate unchanged')
  counts['same_complete_SOS_polynomials']+=1;counts['same_residual_polynomials']+=len(pairs)
  oldled=ledger(rows,[x for q in pairs for x in q]);newled=ledger(p['source'],[x for q in pairs for x in q]);fullled=ledger(newpoly,[newout])
  require(oldled==api['canonical_parent'](root,mode)['certificate_ledger'] and newled==p['certificate_ledger'] and fullled==p['polynomial_ledger'],'all reported ledgers')
  require((newled['M'],newled['A'])==(40,34),'74 exact count')
  require(newled['free']==oldled['free'] and set(newled['free'])==set(p['witnesses'])|set(CONST)|{'x'},'identical complete free coordinate sets')
  degree=upper_leaders(p['source'],pairs,mode)
  require(degree['exact_degree']==p['exact_polynomial_degree'],'degree metadata')
  for case in range(48):
   values={n:rng.randrange(-5,6) for n in newled['free']}
   if case<16:values={n:abs(v)+1 for n,v in values.items()}
   elif case>=32:values={n:Fraction(v,7) for n,v in values.items()}
   aa=scalar(oldpoly,values);bb=scalar(newpoly,values)
   require(aa[oldout]==bb[newout],'whole all-value numeric check')
   for n in set(aa)&set(bb):require(aa[n]==bb[n],'every surviving source value');counts['shared_register_numeric_checks']+=1
   for l,r in pairs:require(aa[l]-aa[r]==bb[l]-bb[r],'every actual residual');counts['residual_numeric_checks']+=1
   counts['whole_numeric_checks']+=1
   if case>=32:counts['rational_checks']+=1
   else:require(api['evaluate'](root,p,values,signed=case>=16)==bb[newout],'public evaluator');counts['public_evaluations']+=1
  def rejects(f):
   try:f()
   except ValueError:counts['malformed_rejections']+=1
   else:raise AssertionError('malformed accepted')
  for i,row in enumerate(newpoly):
   q=copy.deepcopy(p);q['polynomial_source'][i][1]='+' if row[1]!='+' else '*';rejects(lambda q=q:api['checked'](root,q))
  for key in p:
   q=copy.deepcopy(p);q.pop(key);rejects(lambda q=q:api['checked'](root,q))
  q=copy.deepcopy(p);q['certificate_ledger']['M']=40.0;rejects(lambda:api['checked'](root,q))
  q=copy.deepcopy(p);q['polynomial_source'][0]=tuple(q['polynomial_source'][0]);rejects(lambda:api['checked'](root,q))
  vals={n:1 for n in newled['free']}
  for bad in [True,1.0,Fraction(1),None]:
   v=dict(vals);v['x']=bad;rejects(lambda v=v:api['evaluate'](root,p,v,True))
  for flag in [0,1,None,'True']:rejects(lambda flag=flag:api['evaluate'](root,p,vals,flag))
  for v in [dict(vals,extra=1),{n:x for n,x in vals.items() if n!='x'}]:rejects(lambda v=v:api['evaluate'](root,p,v,True))
  q=api['checked'](root,p);q['source'][0][0]='poison';q['transformation']['new_registers'].append('poison');require(same(api['rewrite'](root,mode),p),'fresh isolation');counts['copy_isolation']+=1
  # Explicit raw30 negative test: substituting R10b for supplied k is false off-zero.
  if mode=='raw30':
   vals={n:1 for n in newled['free']};vals['k']=3;v=scalar(p['source'],vals);require(v['R10b']!=vals['k'] and v['first_root_base']*(v['first_root_base']+v['R10b'])!=v['L9'],'wrong actual-k counterexample')
  forms.append({'mode':mode,'comparison_ledger':newled,'polynomial_ledger':fullled,'witnesses':len(p['witnesses']),'comparisons':len(pairs),'degree':degree})
 # Pin checks must be performed again on a warm author namespace.
 with tempfile.TemporaryDirectory(prefix='review-complete74-') as temp:
  tmp=Path(temp)
  for n in PINS:(tmp/n).write_bytes((root/n).read_bytes())
  for n in PINS:
   old=(tmp/n).read_bytes();(tmp/n).write_bytes(old+b'\n')
   try:api['canonical_parent'](tmp)
   except ValueError:counts['warm_dependency_pin_rejections']+=1
   else:raise AssertionError('modified dependency accepted')
   (tmp/n).write_bytes(old)
 proc=subprocess.run([sys.executable,'-O',str(path),'--root',str(root)],capture_output=True,text=True,timeout=30)
 require(proc.returncode!=0 and 'without -O' in proc.stderr,'optimized mode rejected')
 counts['optimized_mode_rejections']+=1
 return {'status':'PASS_INDEPENDENT_COMPLETE74','review_source_sha256':digest(Path(__file__).read_bytes()),'author_pins':AUTHOR_PINS,'parent_pins':PINS,'counts':dict(counts),'forms':forms,'scope':'Complete literal-source factor transfer, all-value comparison/SOS identity, exact uniform degree for fixed admissible compiler numerals, paid counts and bounded API guards. Inherits existing universality proof; no complete positive Pell accepting tuple materialized; no arbitrary program-admissibility checker claimed.'}
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--source-root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();r=verify(v.root,v.source_root)
 if v.expect:require(same(r,json.loads(v.expect.read_text())),'exact saved receipt')
 if v.output:v.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts']},sort_keys=True))
if __name__=='__main__':main()
