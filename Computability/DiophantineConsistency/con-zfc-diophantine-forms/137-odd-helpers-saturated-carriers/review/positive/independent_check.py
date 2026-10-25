#!/usr/bin/env python3
"""Independent exact audit. Never imports or executes producer code.
Local polynomial certificates use fresh indeterminates at verified cutpoints.
Induction/substitution therefore certifies full multivariate identities, not rays.
Sympy is used only as an exact Z-polynomial normalizer.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import copy, gzip, json, re
import sympy as S
ROOT=Path(__file__).resolve().parents[2]/'positive'
CHECKS=0

def need(ok,label):
 global CHECKS
 if not ok: raise ValueError(label)
 CHECKS+=1

def eq(a,b,label): need(S.expand(a-b)==0,label)

def digest(p): return sha256(p.read_bytes()).hexdigest()

# Independent literal reconstruction from the retained complete printed recipe.
def rebuild_tuple():
 alphabet='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
 seed=('BxEnhvy6NipzkWmROo0GsA3uK3twWLxscLq20UTumy5Cdu461LwD6g7RDNzF8Y'
 'iYDFTpB8ehAypd7d6OsOL4APamnJeNXQypUezCmW9n4oXP6XfgmiWuAWZ8ZJ7U'
 'OP7gu4kVdlGZqZHULQMar1dXNeJW4i7oNVI8usp8BlovjjZbwPCovZI328fRUq'
 '4q92R81s5GjWQaQfGhkq9UYMK3rRMaBmsOIBkJqc2cj2VRIZ6mjzkBIOkW9SjZ'
 'FzeA6J5u4j3sBL3SdgwXzM9mHvQivu8EJ1TBTpRhHDqZIbmYgwQ8VqTAFotl6F'
 'We1YC554GKrVHsA8oUGKSA6F6k5KREBSD0Tgd7bFALY84LLbpw574BQyvdoHrl'
 '0Oe35uwDf15DpT6VJWZBjSbHPpPAINYTte0eUxnTFTKBlGj8Am6sb1gLldh8WZ8P')
 need(len(seed)==436,'seed length')
 spec=(ROOT/'source/provenance/indexed_constant_specification.tex').read_text()
 for line in [seed[i:i+62] for i in range(0,436,62)]: need(line in spec,'printed seed chunk')
 packed=0
 for ch in seed: packed=packed*62+alphabet.index(ch)
 N=packed%(1<<636); T0=(packed>>636)%(1<<1675); E0=packed>>2311
 sigma=0; tau=0; actions=[]
 for q in range(215):
  marker=(N>>(430+q))&1; Fq=14 if not marker else (E0>>(4*tau))&15; tau+=marker
  for b in (0,1):
   j=2*q+b; nu=(N>>j)&1
   target=1+sigma if nu else (T0//(216**(j-sigma)))%216
   sigma+=nu
   actions.append((target,(Fq>>(2*b))&1,(Fq>>(2*b+1))&1))
 need(actions[0]==(1,1,1),'renamed first action')
 R=sorted({u for u,v,d in actions if d==1}); L=sorted({u for u,v,d in actions if d==0})
 rr={q:6+j for j,q in enumerate(R)}; ll={q:205+j for j,q in enumerate(L)}
 need((len(R),len(L))==(199,45),'right and left target counts')
 tiles={}
 def put(j,t): need(j not in tiles,'unique tile index'); tiles[j]=t
 def h(q,b): return 2*(q+1)+b
 put(0,(2,435,3,1)); put(1,(5,0,0,0))
 for j,(u,v,d) in enumerate(actions): put(j+2,((1-d)*ll.get(u,0),h(j//2,j%2),d*rr.get(u,0),v))
 for b in (0,1): put(432+b,(0,h(215,b),0,h(215,b))); put(434+b,(0,b,0,b))
 for q in R:
  for b in (0,1): put(424+2*rr[q]+b,(rr[q],b,0,h(q,b)))
 for q in L:
  for b in (0,1): put(424+2*ll[q]+b,(0,b,ll[q],h(q,b)))
 for j in range(4): put(924+j,(0,j+430*(j//2),0,438))
 for j,t in enumerate([(2,434,2,0),(3,436,4,4),(4,436,4,0)]): put(928+j,t)
 for t in (434,435,436): put(497+t,(1,438,1,t))
 for a in (0,1,4):
  for b in (0,1,2): put(934+3*a+b-6*(a//4),(a,437,b,437))
 need(set(tiles)==set(range(943)) and len(set(tiles.values()))==943,'complete distinct indexed tiles')
 vals={j:w+(n<<8)+(e<<17)+(s<<25)+(127<<34) for j,(w,n,e,s) in tiles.items()}
 need(all(1<=v<2**41 for v in vals.values()),'native payload bounds')
 coeff={j:1+(1<<10)*((1<<41)-v) for j,v in vals.items()}
 clauses=[(10,1023,8),(18,1013,9),(27,1003,8),(35,983,9),(44,1031,1),(45,1022,1),(46,1011,1),(47,992,1),(48,1095,1),(49,2195,1),(50,3296,1)]
 for b,e,m in clauses:
  for j in range(m): need(e+j not in coeff,'nonoverlapping clause coefficient'); coeff[e+j]=1<<(b+j)
 support=set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296}
 need(len(support)==986 and set(coeff)==support-{1063,1064},'whole support')
 rho=1<<67; B=1<<(67*8807); beta=B-1
 rp=lambda e:1<<(67*e)
 MC=beta-sum(rp(e) for e in support-{1})-2*rp(1063)
 MF=beta+4+((1<<51)-2)*(rp(4393)+rp(5495))+sum(rp(e) for e in range(1013,1023))+sum(rp(e) for e in range(1065,1074))+rp(2195)+rp(3296)+((1<<65)-1)*sum(rp(e) for e in range(8792,8805))+((1<<19)-1)*rp(8805)
 DC=sum(rp(e) for e in (30,62,1100,2201))+sum(c*(rp(4393-e)+rp(5495-e)) for e,c in coeff.items())
 K0=DC+rp(8849)
 native=MF-beta
 need(MC.bit_count()==590069-986 and native.bit_count()==986,'native mask populations')
 need(MC%4==2 and native%8==4 and 0<DC<B,'native low bits and DC box')
 clause_mass=sum(coeff.values())
 need(2*clause_mass+4<rho,'twice clause mass bound (not full inherited carry certificate)')
 units=[]
 for p,want in [(67,(46,38,23)),(8807,(456,5374,3359)),(581197,(348469,573553,404489))]:
  got=(B%p,(B*B-1)%p,(1+B*DC+B*B*(rp(42)+1))%p)
  need(got==want and all(x for x in got),'fresh indexed controller units')
  units.append([p,*got])
 return dict(beta=beta,K0=K0,MC=MC,MF=MF),{'tiles':943,'actions':430,'support':986,'clause_coefficient_mass':clause_mass,'controller_units':units}

WIT=['J','F','alpha','i','T','w','s','n','eta','zeta']; PORTS=['beta','K0','MC','MF']
# Names prefixed sem_ are independent semantic cutpoint indeterminates.
q,Y,X,k,c,mu,A,D,v0,E,U,a,F0,Fsq,Q,R,B,b,V,Kp,Z,M,radG,RG=S.symbols('sem_q sem_Y sem_X sem_k sem_c sem_mu sem_A sem_D sem_v0 sem_E sem_U sem_a sem_F0 sem_Fsq sem_Q sem_R sem_B sem_b sem_V sem_Kp sem_Z sem_M sem_radG sem_RG')
J,F,alpha,i,T,w,s,n,eta,zeta,beta,K0,MC,MF=S.symbols('J F alpha i T w s n eta zeta beta K0 MC MF')
var=dict(zip(WIT+PORTS,[J,F,alpha,i,T,w,s,n,eta,zeta,beta,K0,MC,MF]))

def certify(d,old=False):
 inputs=[x if x!='s' else 'Y' for x in WIT] if old else WIT
 env={x:(Y if x=='Y' else var[x]) for x in inputs+PORTS}
 L=V**2 if d['transport_weight']=='V2' else b*V
 h=q-1; H=4*A-5; P=q**3*h if old else h
 outer=P*mu**2
 zform=outer*(H*(n-L*B)+Kp)+(H*(mu**2*(h*Y-q**3*B)-P*(k-R-1)) if old else -H*(mu**2*B+h*(k-R-1)))
 expect={
 'bJ':beta*J,'q':beta*J+1,'q2':q*q,'q3':q**3,'Y':q**3*s,
 'qmF':q-F,'C':q-F-alpha,'X':w*q,'k':eta+zeta,'kY':k*Y,'c':k*Y+eta,
 'mu':q*q+1,'Xp1':X+1,'muY':mu*Y,'Am1':mu*Y*(X+1),
 '4Am1':4*(A-1),'Hp':H,'Ap1':A+1,'muY2':mu**2*Y**2,'V0':X*mu**2*Y**2,
 'V0k':v0*k,'V0kk':(v0+1)*k,'V0k2':v0*(v0+1)*k*k,'Dtau':1+v0*(v0+1)*k*k,
 'G1':h*(q-F),'G':h*(q-F)+alpha,'q2m1':q*q-1,'Gq':(h*(q-F)+alpha)*(q*q-1),
 'qMF':q*MF,'MCqMF':MC+q*MF,'RJ':(MC+q*MF)*J,'R':(h*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J,
 'kR':k-R,'e':k-R-1,'K0w':K0+w,'K0wC':(K0+w)*(q-F-alpha),'Bt':(K0+w)*(q-F-alpha)-F,
 'c2':c*c,'U':i*c*c,'UE':U*E,'Delta':A*A-1,'SE':D*U*E,'DpI2':D*U*U*E,'Df':1+a,
 'aF0':a*F0,'fouraF0':4*a*F0,'Fsqr':1+4*a*F0,'Q':D*(Fsq-1),
 'Tp':T+alpha,'cT':c*(T+alpha),'cTR':c*(T+alpha)-R,'DfcTR':Fsq*b,'V':Fsq*b-c,
 'V2':V*V,'L':b*V,'mu2':mu*mu,'P1':q**3*h,'P1mu2':outer,
 'LBt':L*B,'center':n-L*B,'Hn':H*(n-L*B),'threec':3*c,'twoX':2*X,'gap':3*c-2*X,
 'Kpos0':X*(3*c-2*X),'Kpos':X*(3*c-2*X)+2,'lin':H*(n-L*B)+Kp,
 'Zpart1':outer*(H*(n-L*B)+Kp),'qm1Y':h*Y,'q3Bt':q**3*B,'inner':h*Y-q**3*B,
 'mu2inner':mu**2*(h*Y-q**3*B) if old else mu**2*B,'P1e':P*(k-R-1),
 'brk':mu**2*(h*Y-q**3*B)-P*(k-R-1) if old else mu**2*B+h*(k-R-1),
 'Zpart2':H*(mu**2*(h*Y-q**3*B)-P*(k-R-1)) if old else H*(mu**2*B+h*(k-R-1)),
 'Znum':zform,'Mtot':outer*H,'M2':M*M,'Dg':E*F0,'Z2':Z*Z,'RG':M*M*radG,
 'RGV2':RG*V*V,'inside':Z*Z-RG*V*V,'Qinside':Q*(Z*Z-RG*V*V),
 'correction':RG-Z*Z,'N':(Q-1)*Z*Z-RG*(Q*V*V-1)}
 cuts={'q':q,'Y':Y,'X':X,'k':k,'c':c,'mu':mu,'Am1':A-1,'V0':v0,'Dtau':E,'R':R,'Bt':B,'U':U,'Delta':D,'DpI2':a,'Df':F0,'Fsqr':Fsq,'Q':Q,'cTR':b,'V':V,'Kpos':Kp,'Znum':Z,'Mtot':M,'Dg':radG,'RG':RG}
 seen=set(env); used=set()
 for name,op,left,right in d['source']:
  need(name not in seen and name in expect,'unique expected gate '+name)
  need(op in ('+','-','*'),'operator '+name)
  need(all(type(x) is int or x in env for x in (left,right)),'topology '+name)
  av=env[left] if isinstance(left,str) else S.Integer(left); bv=env[right] if isinstance(right,str) else S.Integer(right)
  val=av+bv if op=='+' else av-bv if op=='-' else av*bv
  eq(val,expect[name],'exact gate polynomial '+name)
  env[name]=cuts.get(name,expect[name]); seen.add(name); used.add(name)
  if name=='q': env['bJ']=q-1
  if name=='Fsqr': env['fouraF0']=Fsq-1
 live={d['output']}
 for name,op,left,right in reversed(d['source']):
  if name in live: live.update(x for x in (left,right) if isinstance(x,str))
 need(live==seen,'all gates, inputs and ports live')
 expected_names=set(expect)-({'L'} if d['transport_weight']=='V2' else set())-({'Y'} if old else {'P1','qm1Y','q3Bt','inner'})
 need(used==expected_names,'all and only independently specified gates')
 return len(used)

# Exact global highest-homogeneous replay with beta a symbolic degree-zero
# coefficient. All ten input degrees are one. Coefficients are integer polynomials.
def leading_certificate(d):
 leaves=dict(var); degrees={x:1 for x in WIT}|{x:0 for x in PORTS}; forms=dict(leaves)
 for name,op,left,right in d['source']:
  la=forms[left] if isinstance(left,str) else S.Integer(left); ra=forms[right] if isinstance(right,str) else S.Integer(right)
  ld=degrees[left] if isinstance(left,str) else 0; rd=degrees[right] if isinstance(right,str) else 0
  if op=='*': degree=ld+rd; form=S.factor(la*ra)
  else:
   degree=max(ld,rd); form=S.factor((la if ld==degree else 0)+(1 if op=='+' else -1)*(ra if rd==degree else 0))
  need(form!=0,'nonvanishing homogeneous gate '+name)
  degrees[name]=degree; forms[name]=form
 q0=beta*J; kk=eta+zeta; tt=T+alpha; cc=q0-F-alpha
 want=2**14*q0**506*w**46*s**108*i**20*kk**64*tt**4*cc**2 if d['transport_weight']=='V2' else -2**10*q0**384*w**34*s**80*i**14*kk**46*tt**2
 eq(forms['N'],want,'complete exact highest homogeneous form')
 cert_degrees={'Am1':8,'c':5,'U':11,'Dtau':30,'DpI2':68,'Df':68,'Dg':98,'Fsqr':136,'Q':152,'cTR':6,'V':142,'Mtot':13,'Bt':2,'Znum':299 if d['transport_weight']=='V2' else 163}
 need(all(degrees[x]==v for x,v in cert_degrees.items()),'all displayed component degrees')
 degree=750 if d['transport_weight']=='V2' else 560
 need(degrees['N']==degree and d['exact_degree']==degree,'attained total degree')
 # Extract an exact symbolic integer coefficient at the claimed distinct monomial.
 mon=J**506*w**46*s**108*i**20*eta**64*T**4*F**2 if degree==750 else J**384*w**34*s**80*i**14*eta**46*T**2
 coeff=S.Poly(forms['N'],*[var[x] for x in WIT]).coeff_monomial(mon)
 wantcoeff=2**14*beta**506 if degree==750 else -2**10*beta**384
 eq(coeff,wantcoeff,'actual tuple nonzero coefficient certificate')
 return {'degree':degree,'full_leading_form':str(want),'selected_monomial':str(mon),'selected_coefficient':str(coeff),'component_degrees':cert_degrees}

def full_identities():
 h,H,L,mu,q,n,s,B,e,Kp,Z,M,G,V,Q=S.symbols('h H L mu q n s B e Kp Z M G V Q')
 znew=h*mu**2*(H*(n-L*B)+Kp)-H*(mu**2*B+h*e)
 zold=q**3*h*mu**2*(H*((n-s)-L*B)+Kp)+H*(mu**2*(h*q**3*s-q**3*B)-q**3*h*e)
 eq(zold,q**3*znew,'full free polynomial normalized carrier')
 eq(q**3*h*mu**2*H,q**3*(h*mu**2*H),'full normalized denominator')
 output=lambda zz,mm:Q*(zz**2-mm**2*G*V**2)+(mm**2*G-zz**2)
 eq(output(q**3*Z,q**3*M),q**6*output(Z,M),'full norm scaling exponent six')
 eq(output(Z,M),(Q-1)*Z**2-M**2*G*(Q*V**2-1),'full norm finalizer')
 eq(znew,h*mu**2*H*(n+Kp/H-(1+h*L)*B/h-e/mu**2),'full cross-multiplied rational carrier')
 D,U,E,a=S.symbols('D U E a')
 eq(1+4*a*(1+a),(1+2*a)**2,'Pell doubled trace')
 aa=D*U**2*E
 eq(D*4*aa*(1+aa),4*D**2*U**2*(E*(1+aa)),'whole G divisibility polynomial')
 f0,tau=S.symbols('f0 tau')
 # Formal congruence remainder of doubled norm modulo seed norm and E=tau².
 eq((1+2*aa)**2-D*(2*U)**2*E*(1+aa),1,'doubled norm identity with G')
 v,y=S.symbols('v y')
 vp=(2*Q-1)*v-2*(Q-1)*y; yp=(2*Q-1)*y-2*Q*v
 eq(Q*vp**2-(Q-1)*yp**2,Q*v**2-(Q-1)*y**2,'adjacent rational descent norm')
 eq(aa**2-E*(1+aa),E*((D*U**2)*E*(D*U**2-1)-1),'strict g<a difference')
 need(S.expand(output(q**3*Z,q**3*M)-q**12*output(Z,M))!=0,'wrong scaling exponent rejected')
 need(S.expand(zold.subs(n,n+2*s)-q**3*znew)!=0,'wrong shear sign rejected')
 return 10

def main():
 manifest=json.loads((ROOT/'MANIFEST.json').read_text())
 for path,hashed in manifest.items(): need(digest(ROOT/path)==hashed,'complete frozen manifest '+path)
 ports,native=rebuild_tuple(); binding=json.loads((ROOT/'coefficients/BINDING.json').read_text()); pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
 for path,hashed in pins['source_files'].items(): need(digest(ROOT/path)==hashed,'source pin '+path)
 ledger=json.loads((ROOT/'source/provenance/SOURCE_LEDGER.json').read_text())
 for name,item in ledger['files'].items():
  path=ROOT/'source/provenance'/name
  if path.exists(): need(digest(path)==item['sha256'],'transitive copied source pin '+name)
 for name,ent in binding['ports'].items():
  data=(ROOT/'coefficients'/ent['file']).read_bytes(); raw=gzip.decompress(data)
  val=int.from_bytes(raw,'little')
  need(val==ports[name],'independent exact indexed numeral '+name)
  need(raw==val.to_bytes((val.bit_length()+7)//8,'little'),'canonical numeral encoding '+name)
  need(sha256(data).hexdigest()==ent['gzip_sha256'] and sha256(raw).hexdigest()==ent['raw_sha256'] and val.bit_length()==ent['bits'],'byte binding '+name)
 need(ports['beta']>=31 and ports['beta']%2==1 and ports['K0']>0 and 0<ports['MC']<ports['beta']<ports['MF']<2*ports['beta'],'whole actual coefficient box')
 reports=[]
 for count,oldcount in [(81,84),(82,85)]:
  d=json.loads((ROOT/f'equation_{count}.json').read_text()); old=json.loads((ROOT/f'source/equation_{oldcount}.json').read_text())
  need(d['domain']=='strictly positive integers' and d['witnesses']==WIT and d['fixed_numerals']==PORTS and d['output']=='N','complete positive signature')
  need(d['coefficient_binding']==binding,'whole binding metadata')
  need(d['parent_sha256']==digest(ROOT/f'source/equation_{oldcount}.json'),'immediate source pin')
  for name in PORTS: need(old['coefficient_binding']['ports'][name]['raw_sha256']==binding['ports'][name]['raw_sha256'],'same complete source133 coefficient '+name)
  need(certify(d)==count and certify(old,True)==oldcount,'exact full source and normalized gate coverage')
  counts=dict(Counter(row[1] for row in d['source']))
  need(len(d['source'])==count==d['operations'] and counts==d['operation_breakdown']=={'*':48+(count==82),'+':19,'-':14},'literal operation costs')
  lead=leading_certificate(d)
  # Each actual gate is separately corrupted; this exact checker must reject it.
  rejected=0
  for rowidx,row in enumerate(d['source']):
   mutant=copy.deepcopy(d); mutant['source'][rowidx][1]='-' if row[1] in ('+','*') else '+'
   try: certify(mutant)
   except ValueError: rejected+=1
   else: raise ValueError('undetected actual gate corruption '+row[0])
  need(rejected==count,'every actual gate corruption rejected')
  # Topological and source-sensitive targeted controls, including exponent/shear errors.
  for target,col,val in [('Y',2,'q2'),('fouraF0',2,3),('Q',3,'DpI2'),('brk',1,'-'),('Znum',1,'+'),('inside',1,'+')]:
   mutant=copy.deepcopy(d)
   for row in mutant['source']:
    if row[0]==target: row[col]=val
   try: certify(mutant)
   except ValueError: pass
   else: raise ValueError('targeted mutation accepted '+target)
  reports.append({'file':f'equation_{count}.json','sha256':digest(ROOT/f'equation_{count}.json'),'operations':count,'breakdown':counts,'old_gates_certified':oldcount,'all_actual_gate_corruptions_rejected':rejected,'targeted_mutations_rejected':6,'leading_certificate':lead})
 identities=full_identities()
 report={'status':'PASS','checks':CHECKS,'arithmetic_backend':'sympy exact integer polynomials; no numerical/modular identity sampling','independent_indexed_tuple':native,'universal_full_polynomial_identities':identities,'wrong_scaling_and_shear_controls_rejected':2,'frozen_manifest_files':len(manifest),'circuits':reports,'scope':'Exact finite certificates plus separately written ordinary-proof review; inherited native/refutation theorems are not recreated as a new formal endpoint.'}
 print(json.dumps(report,indent=2,sort_keys=True))
if __name__=='__main__': main()
