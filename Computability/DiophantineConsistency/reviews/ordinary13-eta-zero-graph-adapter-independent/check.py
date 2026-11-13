#!/usr/bin/env python3
"""Independent graph factor, substitution and P72Early audit; no Lean."""
from pathlib import Path
from hashlib import sha256
import itertools,json,random,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path('research/ordinary13-eta-zero-graph-adapter-audit')
fs=[p/'README.md',p/'check.py',p/'result.json',p/'prototype.json',
Path('research/ordinary13-natural-forced-w86/candidate.json'),
Path('Lean/DiophantineConsistency/Compact44/P72Early.lean'),
Path('Lean/DiophantineConsistency/Compact44/FreeJMainOrientation.lean'),
Path('research/ordinary13-eta-zero-index-parity-contradiction-draft/EtaZeroIndexParity.lean.src')]
raw=[f.read_bytes() for f in fs]; old=json.loads(raw[4]);g=json.loads(raw[3]);o=old['source'];z=g['source']
assert old['witnesses']==g['witnesses'] and old['fixed_numerals']==g['fixed_numerals'] and old['output']==g['output']
assert sum(row==['eta','+','n_eta',1] for row in o)==1
transformed=[]
for row in o:
 if row==['eta','+','n_eta',1]:continue
 transformed.append([('n_eta' if t=='eta' else t) for t in row])
assert z==transformed and len(z)+1==len(o)
P72=raw[5].decode();start=P72.index('theorem early (');head=P72[start:P72.index(':= by',start)]
assert '(hqt : q = 3 * t + 2)' in head
assert '(hS : S = 4 * (Y * q)) (hM : M = S * q)' in head
assert '(M * γ + S * X + R + 1)' in head
fm=raw[6].decode(); start=fm.index('def FreeJMainCongruence');end=fm.index('/-- Positive transport',start)
assert 'H*(E*q+R+1)' in fm[start:end]
assert '(hc : c = Y * k)' in raw[7].decode()
# Direct evaluation checks every displayed intermediate and the four output
# factors. Port and witness values include zeros, odd/even and negative
# signed internal expressions; equality here is exact integer arithmetic.
rng=random.Random(6007); count=0;negative_C=0
for case in range(350):
 vals={key:rng.randrange(0,4) for key in g['witnesses']+g['fixed_numerals']}
 if case<100:vals['n_eta']=0
 e=vals.copy()
 for name,op,l,r in z:
  x=l if isinstance(l,int) else e[l]; y=r if isinstance(r,int) else e[r]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 J,F,al,f,i,T,w,s0,r,eta,ze,y,gamma=(vals[x] for x in g['witnesses'])
 beta,K0,MC,MF=(vals[x] for x in g['fixed_numerals'])
 F+=1;al+=1;i+=1;T+=1;s0+=1;ze+=1
 b=J*beta;q=1+b;X=q*w;Y=q**3*s0;U=Y*q*q;E=X*Y;k=eta+ze;c=eta+Y*k
 a=E+Y;H=3+4*a;D=a*a+H;ell=E*Y*k;C=q-F-al;Bt=C*(X+K0)-F
 Z=b*(ell+k+r-k*Bt)-Bt;R=(al+(q-F)*b)*(q*q-1)+J*(MC+MF*q)
 ds=U*(X+a*c)+H*(U*gamma+R+1-k);I=i*c*c;Q=D*(f*f-1);V=f*f*(T*c-R)-c
 expected={'q':q,'X':X,'Y':Y,'U':U,'k':k,'c':c,'a':a,'H':H,'Delta':D,'ell':ell,'C':C,'Bt':Bt,'Z':Z,'R':R,'Dstar':ds,'I':I,'Q':Q,'V':V,
 'F0':1+Z*Z-b*b*(1+ell*(ell+k)), 'F1':1+ds*ds-U*U*(1+D*c*c),
 'Fa':y*y-Q*(y*y-V*V),'Fs':1+I*I-Q}
 for key,val in expected.items():assert e[key]==val,(case,key)
 assert e['out']==expected['F0']*expected['F1']*expected['Fa']*expected['Fs']-1
 negative_C+=C<0;count+=1
assert negative_C>0
# Exhaustive mod-4 exclusions on the structural free values; signed ring
# lift and unit factorization within arbitrary models remain separate proofs.
for b,x,s,k,z0 in itertools.product(range(4),repeat=5):
 q=b+1;Y=q**3*s;ell=x*Y*Y*k
 assert (1+z0*z0-b*b*(1+ell*(ell+k)))%4!=3
for a,u,c,d in itertools.product(range(4),repeat=4):
 D=a*a+4*a+3
 assert (1+d*d-u*u*(1+D*c*c))%4!=3
for a,f,I,y,V in itertools.product(range(4),repeat=5):
 D=a*a+4*a+3;Q=D*(f*f-1)
 assert (y*y-Q*(y*y-V*V))%4!=3
 assert (1+I*I-Q)%4!=3
assert subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,check=True).stdout==raw[2]
print(json.dumps({'sha256':{str(f):sha256(b).hexdigest() for f,b in zip(fs,raw)},
 'source_rows':len(z),'integer_graph_factor_controls':count,'negative_C_controls':negative_C,
 'full_mod4_factor_exclusions_checked':True,'author_receipt_reproduced':True,
 'P72Early_requires_q_equals_3t_plus_2':True,'P72Early_carrier_not_same_as_prototype':True,
 'scope':'bounded independent source and integer checks; no model unit proof, zero maps or Lean',
 'lean_executed':False},sort_keys=True,indent=2))
