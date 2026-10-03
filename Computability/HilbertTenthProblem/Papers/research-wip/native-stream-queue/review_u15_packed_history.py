#!/usr/bin/env python3
"""Independent source/composition audit; no production changes."""
import argparse,copy,hashlib,importlib.util,json,random,sys
from pathlib import Path
import sympy as sp
if not __debug__:raise RuntimeError('Assertions required')
SOURCE_SHA='ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318'
LOADER_SHA='90b5cdf912b34b57cebe6a1b9c9bd3d5bcfd44c234c80e4d3ae774f8d696ce00'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):
 sys.path.insert(0,str(p.parent));s=importlib.util.spec_from_file_location('u15_audited',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def manual_raw(v,rs):
 E=[v[f'edge{i}']-1 for i in range(29)];J=sum(E);D=v['L0']+v['R0']+v['height'];B=64*D;P=(B-1)*J+1
 H,G,U,ZL,ZR,ZU=(v[n] for n in ('H','G','U','ZL','ZR','ZU'))
 Q,S,N,Dir,W=[sum(t[c]*e for t,e in zip(rs,E)) for c in range(5)];WD=sum(t[3]*t[4]*e for t,e in zip(rs,E))
 K=sum(P**i for i in range(29));Ec=sum(e*P**i for i,e in enumerate(E));Rmask=(D-1)*J
 A=H+P*G+P**2*U+P**3*H+P**4*G+P**5*Ec
 M=(B-1)*Dir*(1+P)+P**2*Dir+(P**3+P**4)*Rmask+P**5*J*K
 Z=ZL+P*ZR+P**2*ZU+P**3*H+P**4*G+P**5*Ec
 cap=B*P**34;T=2*WD+ZU;Lf=v['Lfhat']-1;Rf=v['Rf']
 outer=[2*(H-v['L0']+P*Lf)-B*(4*H-3*ZL+2*W-T),
        2*(G-v['R0']+P*Rf)-B*(G+3*ZR+T-U),B*N-Q-9*P,B*U-S-P,H+G+ZL+ZR+ZU+v['bound']-P]
 at=lambda n:v['native__'+n]
 q=16*cap;F0,F1,F2=(at(n) for n in ('F0','F1','F2'));F3=16*Z+8
 r=F0+q*F1+q*q*F2+q*q*q*F3;s=2*at('odd_half')+1;k=at('eta')+at('zeta')
 X=q*(r+at('bound_beta'));Y=s*q;a=Y*(X+1);c=k*Y+at('eta')
 d=X+a*c+at('ga')*(4*a+3);delta=a*a+4*a+3;u=at('j')*c-(2*r+1);ic22=(at('i')*c*c)**2;y=at('y_aux')
 native=[F0+F1+F2+F3+1-q,
  ((X*Y)**2+X)*(Y*k)**2-at('tau')*(at('tau')+1),
  k-r-1-at('h')*X*Y,d*d-1-delta*c*c,ic22-delta*(at('f')**2-1),
  ic22*(u*u-y*y)-(1-y*y),u+c-at('o')*at('f'),F1+F3-(16*A+12),F2+F3-(16*M+10)]
 return outer+native,dict(J=J,D=D,B=B,P=P,Hjoin=A,Mjoin=M,Zjoin=Z,scale=cap)

def formal_prefix(m):
 p=m.build();reg=p['registers'];env={n:sp.Symbol(n) for n in p['parameters']+p['auxiliaries']}
 symbols={n:sp.Symbol(n) for n in ('J','D','B','P','Q','S','N','Dir','W','WD','Lf')}
 E=[sp.Symbol(f'edge{i}')-1 for i in range(29)]
 cuts={reg[n]:n for n in symbols}
 expected={'J':sum(E),'D':sp.Symbol('L0')+sp.Symbol('R0')+sp.Symbol('height'),
 'B':64*symbols['D'],'P':(symbols['B']-1)*symbols['J']+1,'Lf':sp.Symbol('Lfhat')-1}
 for n,col in (('Q',0),('S',1),('N',2),('Dir',3),('W',4)):
  expected[n]=sum(t[col]*e for t,e in zip(m.RULES,E))
 expected['WD']=sum(t[3]*t[4]*e for t,e in zip(m.RULES,E))
 checks=0
 for name,op,a,b in p['source']:
  if name.startswith('native__'):break
  x=env[a] if type(a) is str else sp.Integer(a);y=env[b] if type(b) is str else sp.Integer(b)
  env[name]=x*y if op=='*' else x+y if op=='+' else x-y
  if name in cuts:
   label=cuts[name];assert sp.expand(env[name]-expected[label])==0,label
   env[name]=symbols[label];checks+=1
 B,D,J,P=[symbols[n] for n in ('B','D','J','P')]
 H,G,U,ZL,ZR,ZU=[sp.Symbol(n) for n in ('H','G','U','ZL','ZR','ZU')]
 K=sum(P**i for i in range(29));Ec=sum(e*P**i for i,e in enumerate(E));R=(D-1)*J;Dir=symbols['Dir']
 exp={'K29':K,'Ec':Ec,'Mc':J*K,'range_mask':R,'direction_mask':(B-1)*Dir,'HP':H+P*G,
 'Hjoin':H+P*G+P**2*U+P**3*H+P**4*G+P**5*Ec,
 'Mjoin':(B-1)*Dir*(1+P)+P**2*Dir+(P**3+P**4)*R+P**5*J*K,
 'Zjoin':ZL+P*ZR+P**2*ZU+P**3*H+P**4*G+P**5*Ec,'scale':B*P**34}
 for n,x in exp.items():assert sp.expand(env[reg[n]]-x)==0,n;checks+=1
 T=2*symbols['WD']+ZU
 ex=[2*(H-sp.Symbol('L0')+P*symbols['Lf'])-B*(4*H-3*ZL+2*symbols['W']-T),
  2*(G-sp.Symbol('R0')+P*sp.Symbol('Rf'))-B*(G+3*ZR+T-U),
  B*symbols['N']-symbols['Q']-9*P,B*U-symbols['S']-P,H+G+ZL+ZR+ZU+sp.Symbol('bound')-P]
 for (a,b),x in zip(p['comparisons'][:5],ex):assert sp.expand(env[a]-env[b]-x)==0;checks+=1
 return checks

def verify(source):
 assert digest(source)==SOURCE_SHA and digest(source.with_name('u15_raw_half_tape_loader.py'))==LOADER_SHA
 m=load(source);counts={};inc=lambda k,n=1:counts.__setitem__(k,counts.get(k,0)+n)
 counts['formal_compositional_prefix_identities']=formal_prefix(m)
 raw=m.build();ordinary=m.build(True);core=m.native.build('and',scaled=True,fields=m.native.VARIANTS['six'])
 alias={'P':raw['registers']['scale'],'Hhat':raw['registers']['Hjoin'],'Mhat':raw['registers']['Mjoin'],'Zhat':raw['registers']['Zjoin']}
 rename=lambda x:alias.get(x,'native__'+x) if type(x) is str else x
 expected=[]
 for n,op,a,b in core['source']:
  if n in ('padded_A','padded_B','F3'):op='+';b={'padded_A':12,'padded_B':10,'F3':8}[n]
  expected.append(('native__'+n,op,rename(a),rename(b)))
 assert [row for row in raw['source'] if row[0].startswith('native__')]==expected
 assert raw['comparisons'][5:]==[(rename(a),rename(b)) for a,b in core['comparisons']]
 for hat,scaled,padded in (('Hhat','scaled_A','padded_A'),('Mhat','scaled_B','padded_B'),('Zhat','scaled_Z','F3')):
  assert [n for n,op,a,b in core['source'] if hat in (a,b)]==[scaled]
  assert [n for n,op,a,b in core['source'] if scaled in (a,b)]==[padded]
 inc('complete_native_source_and_comparison_substitution')
 # Exact ordinary prefix and raw suffix maps, including the omitted identity.
 ld=m.loader.build(False)
 lmap=lambda x: {'x':'x','L0':'program_L','R0':'input_R0',**{n:n for n in ('program_L','program_A','program_B','program_D')}}.get(x,'input__'+x) if type(x) is str else x
 rmap=lambda x:{'L0':'program_L','R0':'input_R0'}.get(x,x)
 assert ordinary['source'][:138]==[(lmap(n),op,lmap(a),lmap(b)) for n,op,a,b in ld['source']]
 assert ordinary['source'][138:]==[(n,op,rmap(a),rmap(b)) for n,op,a,b in raw['source']]
 assert ordinary['comparisons'][:35]==[(lmap(a),lmap(b)) for a,b in ld['comparisons'] if (a,b)!=('L0','program_L')]
 assert ordinary['comparisons'][35:]==[(rmap(a),rmap(b)) for a,b in raw['comparisons']]
 inc('complete_ordinary_source_and_comparison_substitution')
 rng=random.Random(654104)
 for isordinary,p in ((False,raw),(True,ordinary)):
  names=p['parameters']+p['auxiliaries'];assert len(names)==len(set(names))
  available=set(names);hist={'M':0,'A':0}
  for n,op,a,b in p['polynomial_source']:
   assert n not in available and op in ('+','-','*')
   assert all(type(v) is int or type(v) is str and v in available for v in (a,b));available.add(n);hist['M' if op=='*' else 'A']+=1
  assert hist=={x:p['ledger']['polynomial'][x] for x in ('M','A')}
  assert len(p['polynomial_source'])==len(p['source'])+3*len(p['comparisons'])-1
  for fixed in (set(p['fixed_parameters']),set()):
   deg={n:0 if n in fixed else 1 for n in names}
   for n,op,a,b in p['polynomial_source']:
    da=deg[a] if type(a) is str else 0;db=deg[b] if type(b) is str else 0
    deg[n]=da+db if op=='*' else max(da,db)
   assert deg[p['output']]==1936
  inc('formal_degree_upper_bound_checks',2)
  live={p['output']}
  for n,op,a,b in reversed(p['polynomial_source']):
   if n in live:live.update(v for v in (a,b) if type(v) is str)
  assert all(n in live for n,op,a,b in p['polynomial_source'])
  inc('literal_source_counts_and_closure')
  for i in range(128):
   v={n:rng.randrange(1,8) if i<64 else rng.randrange(-4,5) for n in names}
   if isordinary:
    vr={n:v[n] for n in raw['auxiliaries']};vr.update(L0=v['program_L'],R0=v['input_R0'])
    lv={n:v[lmap(n)] for n in ld['parameters']+ld['auxiliaries'] if n!='L0'};lv['L0']=v['program_L']
    first=m.loader.bridge.independent(m.loader.bridge.recoder(32),lv)
    first.append(m.loader.DENOM*v['input_R0']+v['program_D']-v['program_A']*lv['q']**32-v['program_B']*lv['z'])
   else:vr=v;first=[]
   rr,regs=manual_raw(vr,m.RULES);rr=first+rr
   env=m.execute(p['polynomial_source'],v)
   actual=[m.get(env,a)-m.get(env,b) for a,b in p['comparisons']]
   assert actual==rr and env[p['output']]==sum(x*x for x in rr)
   assert m.evaluate(p,v,signed=True)==env[p['output']]
   for n,x in regs.items():assert m.get(env,p['registers'][n])==x
   inc('complete_manual_residual_and_SOS_cases');inc('signed_cases',i>=64)
  # Bounded guards target metadata types, polynomial signs, source and cache copies.
  def reject(f):
   try:f()
   except (ValueError,TypeError):inc('malformed_rejected');return
   raise AssertionError('Malformed accepted')
  vals={n:1 for n in names}
  for name in names[:5]+p['auxiliaries'][-5:]:
   for bad in (True,1.0,-1):
    z=dict(vals);z[name]=bad;reject(lambda z=z:m.evaluate(p,z))
  for field in ('source','comparisons','parameters','auxiliaries','registers','polynomial_source'):
   z=copy.deepcopy(p);z[field]=None;reject(lambda z=z:m.checked(z))
  z=copy.deepcopy(p);z['ledger']['equations']=float(z['ledger']['equations']);reject(lambda:m.checked(z))
  z=copy.deepcopy(p);z['polynomial_source'][-1]=('poison','*',1,1);reject(lambda:m.checked(z))
  z=copy.deepcopy(p);z['ledger'].clear();z['source'].clear();assert m.build(isordinary)==p;inc('defensive_nested_exports')
  reject(lambda:m.evaluate(p,vals,signed=1))
  reject(lambda:m.evaluate(p,dict(vals,extra=1)))
  altered=dict(vals);del altered[names[0]];reject(lambda:m.evaluate(p,altered))
  for bad in (0,1,None,'False'):reject(lambda bad=bad:m.build(bad))
 # Ordinary orientation, independently reading literal source configurations.
 for q,h in ((2,2),(3,3),(5,2)):
  prod={(j,i):((i%q)+1,j+1) for j in range(1,h) for i in range(1,q+1)}
  pa=m.loader.parameters(q,h,prod,q,q-1)
  for x in (1,2,3,4,7,8,15,16,31,63):
   for pad in (0,1,2):
    n=max(2,x.bit_length()+pad);bits=[(x>>j)&1 for j in range(n)]
    data=[('e',1)]+[('a',a) for b in bits for a in ((1,2) if b==0 else (2,1))]+[('a',q),('a',q-1)]
    tape,pos=m.loader.nw.encoded_configuration(q,h,prod,data)
    low=lambda s:sum((c=='b')<<j for j,c in enumerate(s))
    L=low(tape[:pos][::-1]);R=low(tape[pos+1:]);z=sum(b<<(32*j) for j,b in enumerate(bits));Q=1<<(32*n)
    assert tape[pos]=='c' and L==pa['program_L']
    assert m.loader.DENOM*R+pa['program_D']==pa['program_A']*Q+pa['program_B']*z
    inc('independent_literal_loader_orientations')
 for L,R in ((6,0),(6,4),(14,0),(22,0)):
  v,meta=m.outer_fixture(L,R,100);rr,reg=manual_raw(v,m.RULES)
  assert rr[:5]==[0]*5 and reg['Hjoin']&reg['Mjoin']==reg['Zjoin']
  assert v['Rf']>=1 and all(v[n]>0 for n in ('H','G','ZL','ZR','ZU','U'));inc('positive_outer_fixtures')
 return dict(status='PASS',source_sha256=SOURCE_SHA,loader_sha256=LOADER_SHA,counts=counts,
  raw_ledger=raw['ledger'],ordinary_ledger=ordinary['ledger'],
  scope='Full source, formal compositional prefix identities, literal native/loader graph substitutions, independent14/49-residual and SOS evaluations; no materialized full Pell witnesses. Total degree1936 remains a declared upper bound, not an exact-degree claim.')
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--source',type=Path,required=True);a.add_argument('--receipt',type=Path,required=True);v=a.parse_args();r=verify(v.source.resolve());v.receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
