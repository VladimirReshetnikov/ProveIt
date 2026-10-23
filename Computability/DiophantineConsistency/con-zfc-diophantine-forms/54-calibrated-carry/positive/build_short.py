"""New independent literal DAGs. Reads no executable from upstream."""
import json, collections
from pathlib import Path
ROOT=Path(__file__).resolve().parent
class DAG:
 def __init__(self): self.rows=[]; self.cache={}
 def op(self,o,a,b,n):
  key=(o,*(sorted((a,b),key=str) if o in ['+','*'] else [a,b]))
  if key in self.cache:return self.cache[key]
  self.rows.append([n,o,a,b]);self.cache[key]=n;return n
 def add(self,a,b,n):return self.op('+',a,b,n)
 def sub(self,a,b,n):return self.op('-',a,b,n)
 def mul(self,a,b,n):return self.op('*',a,b,n)
 def sq(self,a,n):return self.mul(a,a,n)

def build(name,finalizer,first_gap=False,aux_gap=False,squared=True):
 d=DAG();a,m,s,ss=d.add,d.mul,d.sub,d.sq
 qm=m('beta','J','qm');q=a(qm,1,'q');q2=ss(q,'q2');q3=m(q2,q,'q3')
 X=m('w',q,'X');Y=m('s',q3,'Y');E=m(X,Y,'E');k=a('eta','zeta','k');kY=m(k,Y,'kY');ell=m(E,kY,'ell')
 if first_gap:
  r2=ss('r','r2');twice=m(2,'r','twice_r');gap=s(twice,k,'first_gap');N0=a(r2,m(ell,gap,'first_product'),'N0')
 else:N0=s(ss('tau','tau2'),m(ell,a(ell,k,'ell_plus_k'),'first_product'),'N0')
 c=a(kY,'eta','c');aa=a(E,Y,'a');H=a(m(4,aa,'four_a'),3,'H');Delta=a(ss(aa,'a2'),H,'Delta')
 ac=m(aa,c,'ac');D=a(a(X,ac,'main_base'),m('gamma',H,'gammaH'),'main_root');c2=ss(c,'c2');Dc2=m(Delta,c2,'Dc2');N1=s(ss(D,'main_square'),Dc2,'N1')
 qF=s(q,'F','qF');C=s(qF,'alpha','C');G=a(m(qm,qF,'gap_product'),'alpha','gap');R=a(m(G,s(q2,1,'q2minus1'),'rproduct'),m(a('MC',m(q,'MF','qMF'),'maskfactor'),'J','mask'),'R')
 Nk=s(s(k,m('h',E,'hE'),'index_partial'),R,'Nk');Nt=s(a(m(a('K0','w','Kw'),C,'transport'),qF,'transport_partial'),m('z',qm,'zqm'),'Nt')
 f2=ss('f','f2')
 if squared:V=s(m(f2,s(m(c,'T','cT'),R,'cTminusR'),'f2inner'),c,'V')
 else:V=s(m(c,s(m('T','f','Tf'),1,'Tfminus1'),'cTfminus1'),m(R,f2,'Rf2'),'V')
 I=m('i',c2,'I');I2=ss(I,'I2');A0=m(Delta,s(f2,1,'f2minus1'),'A0')
 auxcoef=A0
 if finalizer=='normalized_scaled_product':auxcoef=ss(m('i',Dc2,'normalized_S'),'normalized_S2')
 if aux_gap:
  y0=a(V,'u','restored_y');Na=s(ss(y0,'restored_y2'),m(auxcoef,m('u',a(V,y0,'VplusY'),'gap_product_aux'),'scaled_gap_aux'),'Na')
 else:Na=a(m(auxcoef,s(ss(V,'V2'),ss('y','y2'),'V2minusY2'),'aux_product'),'y2','Na')
 if finalizer=='ordinary_minimum3':
  fm=m(N0,N1,'first_main');aux=m(m(Na,Nk,'aux_index'),Nt,'aux_index_transport');ar=s(aux,2,'aux_minus_two');sr=s(I2,A0,'strong_residual')
  out=a(a(ss(fm,'first_main2'),m(aux,ar,'aux_falling_product'),'sum12'),ss(sr,'strong_residual2'),'polynomial')
 elif finalizer=='normalized_minimum4':
  Ns=s(f2,m(Delta,I2,'strong_scaled_square'),'Ns');p=m(m(N1,Nk,'main_index'),Nt,'main_index_transport');r=s(p,1,'coupled_residual')
  total=a(a(a(ss(N0,'N02'),ss(Na,'Na2'),'sum12'),ss(Ns,'Ns2'),'sum123'),ss(r,'coupled_residual2'),'sum1234');out=s(total,3,'polynomial')
 elif finalizer=='normalized_scaled_product':
  Ns=s(m(Delta,f2,'scaled_f2'),auxcoef,'scaled_Ns');p=N0
  for j,n in enumerate([N1,Na,Nk,Nt,Ns]):p=m(p,n,'product'+str(j))
  out=s(p,Delta,'polynomial')
 elif finalizer=='ordinary_product':
  Ns=a(s(I2,A0,'strong_residual'),1,'Ns');p=N0
  for j,n in enumerate([N1,Na,Nk,Nt,Ns]):p=m(p,n,'product'+str(j))
  out=s(p,1,'polynomial')
 else:raise ValueError(finalizer)
 witnesses=['J','F','alpha','z','f','h','i','T','s','w','r' if first_gap else 'tau','eta','zeta','u' if aux_gap else 'y','gamma']
 needed={out}
 for n,o,x,y in d.rows[::-1]:
  if n in needed:needed.update([x,y])
 rows=[r for r in d.rows if r[0] in needed]
 ports=['beta','K0','MC','MF']
 if set(witnesses+ports)-needed:raise ValueError('Dead input')
 obj={'name':name,'witness_domain':'strictly positive integers','witnesses':witnesses,'fixed_numerals':ports,'source':rows,'output':out,'operations':len(rows),'operation_counts':dict(collections.Counter(r[1] for r in rows)), 'first_gap':first_gap,'auxiliary_gap':aux_gap,'squared_modulus':squared,'finalizer':finalizer,'coefficient_binding':{'file':'../native/COEFFICIENT_BINDING.json','aliases':{'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}},'proof':'SHORT_COMPOSITIONS_PROOF.md','proof_boundary':'Ordinary mathematical proof, inherited compiler and ordinary strong-rank theorem; not a new proof-assistant certificate.'}
 return obj

def main():
 specs=[('p66_degree157','normalized_scaled_product',False,False,True,157),('p73_degree68','normalized_minimum4',False,False,True,68),('p70_degree80','ordinary_minimum3',False,False,True,80),('p71_degree78','ordinary_minimum3',True,False,True,78),('p72_degree64','ordinary_minimum3',True,True,True,64),('p73_degree62','ordinary_minimum3',True,True,False,62),('p68_degree101','ordinary_product',False,False,True,101),('p70_degree84','ordinary_product',True,True,True,84)]
 receipt=[]
 for name,fin,fg,ag,sqm,degree in specs:
  obj=build(name,fin,fg,ag,sqm);obj['exact_degree']=degree
  directory=ROOT/'comparisons' if name in ['p73_degree68','p70_degree84'] else ROOT
  directory.mkdir(exist_ok=True)
  if directory!=ROOT:obj['coefficient_binding']['file']='../../native/COEFFICIENT_BINDING.json'
  (directory/(name+'.json')).write_text(json.dumps(obj,indent=2)+'\n');receipt.append({k:obj[k] for k in ['name','operations','operation_counts','exact_degree']})
 (ROOT/'SHORT_BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
