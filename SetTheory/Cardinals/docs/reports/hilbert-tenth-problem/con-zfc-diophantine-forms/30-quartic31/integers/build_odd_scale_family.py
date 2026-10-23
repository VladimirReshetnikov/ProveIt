if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""New-owned emitters. Upstream and earlier circuits are parsed as inert JSON only."""
import json,hashlib
from pathlib import Path
H=Path(__file__).resolve().parent
OLD=H/'parents'
class Circuit:
 def __init__(self): self.rows=[];self.n=0
 def op(self,op,a,b,name=None):
  self.n+=1;name=name or f'g{self.n}'
  self.rows.append([name,op,a,b]);return name
 def add(self,a,b,name=None):return self.op('+',a,b,name)
 def sub(self,a,b,name=None):return self.op('-',a,b,name)
 def mul(self,a,b,name=None):return self.op('*',a,b,name)
 def square(self,a,name=None):return self.mul(a,a,name)

def positive_substitutions(c,ports):
 vs=[]
 for x in ports:
  a,b,d=[x+'_positive_'+q for q in 'abc'];vs += [a,b,d]
  aa=c.square(a);bb=c.square(b);dd=c.mul(d,c.add(d,1));c.add(c.add(c.add(aa,bb),dd),1,x)
 for x in ['i','s']:c.add(c.mul(2,x+'_integer'),1,x);vs.append(x+'_integer')
 c.square('w_integer','w');vs.append('w_integer');return vs

def packet(c,name,vs,fixed,output,degree,meta=None):
 return dict(name=name,witness_domain='unrestricted integers',witnesses=vs,variable_count=len(vs),fixed_numerals=fixed,source=c.rows,output=output,exact_degree=degree,ledger={'operations':len(c.rows),'multiplications':sum(x[1]=='*' for x in c.rows),'additions_subtractions':sum(x[1]!='*' for x in c.rows)},**(meta or {}))

def save(p):
 path=H/(p['name']+'.json');path.write_text(json.dumps(p,indent=2)+'\n');print(p['name'],p['ledger'])

# New optimized pair norm, with all six positive guards, two odd ports, and square w.
c=Circuit();positive=['J','F','alpha','z','eta','zeta'];vs=positive_substitutions(c,positive)+['h','T','t']
rep=c.mul('beta','J');q=c.add(rep,1,'q');q2=c.square(q);q3=c.mul(q2,q);X=c.mul('w',q,'X');Y=c.mul('s',q3,'Y');E=c.mul(X,Y,'E');k=c.add('eta','zeta','k');kY=c.mul(k,Y);ell=c.mul(E,kY,'ell');A=c.add(c.mul(ell,c.add(ell,k)),1,'A');cc=c.add(kY,'eta','c');a=c.add(E,Y,'a');P0=c.add(X,c.mul(a,cc),'P0');Hh=c.add(c.mul(4,a),3,'H');Delta=c.add(c.square(a),Hh,'Delta');c2=c.square(cc,'c2');G=c.add(c.mul(Delta,c2),1,'G')
qF=c.sub(q,'F');CW=c.sub(qF,'alpha');R=c.add(c.mul(c.add(c.mul(rep,qF),'alpha'),c.sub(q2,1)),c.mul(c.add('MC',c.mul(q,'MF')),'J'),'R');Nk=c.sub(c.sub(k,c.mul('h',E)),R,'Nk');Nt=c.sub(c.add(c.mul(c.add('K0','w'),CW),qF),c.mul('z',rep),'Nt')
I=c.mul('i',c2,'I');S=c.mul(Delta,I,'S');Q=c.square(S,'Q');D=c.add(c.mul(I,S),1,'D');d=c.sub(Q,1,'d');v2=c.mul(c2,c.square('T'),'v2');b=c.add(cc,c.mul(R,D),'b');p=c.mul(Q,c.mul(D,v2),'p');z0=c.mul(Q,c.square(b),'z0');e=c.sub(c.add(p,z0),1,'e');W=c.add(c.add(v2,D),c.mul(2,b),'W');P=c.mul(Hh,W,'Pweight');K=c.add(P,1,'K');Z=c.add(c.mul(Hh,'t'),c.mul(K,P0),'Z');u=c.mul(3,P,'u');H2=c.square(Hh,'H2')
# Norm in tau first, then g. x=Z+K*g, tau^2=A, g^2=G.
x20=c.add(c.square(Z),c.mul(c.square(K),G),'x20');x21=c.mul(2,c.mul(Z,K),'x21');u2A=c.mul(c.square(u),A,'u2A');C0=c.sub(c.mul(d,c.add(x20,u2A)),c.mul(H2,e),'C0');C1=c.mul(d,x21,'C1');jscale=c.mul(4,c.mul(c.square(d),u2A),'jscale');J0=c.mul(jscale,x20,'J0');J1=c.mul(jscale,x21,'J1');Zterm=c.mul(4,c.mul(c.square(H2),c.mul(p,z0)),'Zterm')
def pairsquare(x0,x1):return c.add(c.square(x0),c.mul(G,c.square(x1))),c.mul(2,c.mul(x0,x1))
C20,C21=pairsquare(C0,C1);T0=c.sub(c.sub(C20,J0),Zterm,'T0');T1=c.sub(C21,J1,'T1');T20,T21=pairsquare(T0,T1);fourZ=c.mul(4,Zterm);F0=c.sub(T20,c.mul(fourZ,J0),'F0');F1=c.sub(T21,c.mul(fourZ,J1),'F1');Norm=c.sub(c.square(F0),c.mul(G,c.square(F1)),'Norm');out=c.sub(c.mul(c.mul(Nk,Nt),c.add(Norm,1)),1,'polynomial')
p24=packet(c,'integer24_pair_norm165_degree2256',vs,['beta','K0','MC','MF'],out,2256,{'positive_ports':positive,'norm_degree':2240,'factor_degrees':{'Nk':12,'Nt':4,'unit':2240},'proof':'SIGNED_ODD_SCALE_FAMILY_PROOF.md','coefficient_binding':'COEFFICIENT_BINDINGS.json; one complete original06, compact Wang943, or independently verified complete new tuple. MF is shifted.'})
# Name uses actual count, not a guess.
p24['name']=f"integer24_pair_norm{len(c.rows)}_degree2256";save(p24)
# Lift earlier inert arithmetic circuits to six guards, odd s, odd i, square w.
for oldname,num,degree in [('integer28_normalized_amalgam128_degree258.json',26,236),('integer27_weighted_root136_degree1116.json',25,920)]:
 old=json.loads((OLD/oldname).read_text());c=Circuit();ports=[x for x in old['positive_ports'] if x!='s'];vs=positive_substitutions(c,ports)
 prior=old['source'][52:];assert not any(r[0] in ports+['i','s','w'] for r in prior)
 vs += [x for x in old['witnesses'] if not x.endswith(('_positive_a','_positive_b','_positive_c')) and x not in ['i_integer','w_integer']]
 if num==25:
  # The five strong gates have the same cost; choose low-degree M=I^2+T^2.
  # Existing symbols verified below, replace Qr/Q/ic2/Dm1/D dependency block.
  for row in prior:
   if row[0]=='Qr': row[:]=['Qr','*','i','c2']
   elif row[0]=='Q': row[:]=['I2','*','Qr','Qr']
   elif row[0]=='ic2': row[:]=['Dm1','*','A','I2']
   elif row[0]=='Dm1': row[:]=['D','+','Dm1',1]
   elif row[0]=='D': row[:]=['Q','*','A','Dm1']
   elif row[0]=='v': row[:]=['T2','*','auxiliary_quotient','auxiliary_quotient']
   elif row[0]=='v2': row[:]=['v2','*','c2','T2']
   elif row[0]=='M':row[:]=['M','+','I2','T2']
 c.rows += prior
 name=f'integer{num}_'+('small_weight' if num==25 else 'two_root')+f'{len(c.rows)}_degree{degree}'
 p=packet(c,name,vs,old['fixed_numerals'],old['output'],degree,{'positive_ports':ports,'proof':'SIGNED_ODD_SCALE_FAMILY_PROOF.md','source_parent':str((OLD/oldname).relative_to(H.parent.parent)),'source_parent_sha256':hashlib.sha256((OLD/oldname).read_bytes()).hexdigest()})
 save(p)
# Ordinary-strong 26-integer sharpening; retained main Pell rank makes A<Q.
p=json.loads((H/'integer26_two_root123_degree236.json').read_text())
for r in p['source']:
 if r[0]=='normalized_strong_term':r[:]=['ordinary_strong_difference','-','I2','Kaux']
 elif r[0]=='Ns':r[:]=['Ns','+','ordinary_strong_difference',1]
for r in p['source']:
 if r[0]=='ordinary_strong_difference':r[3]='A0'
p['ledger']={'operations':len(p['source']),'multiplications':sum(r[1]=='*' for r in p['source']),'additions_subtractions':sum(r[1]!='*' for r in p['source'])}
p['name']='integer26_ordinary_two_root123_degree214';p['exact_degree']=214;p['ordinary_strong']=True
save(p)
# Sharpened separator: coefficient two is sufficient, and one leading root branch cancels.
p=json.loads((H/'integer24_pair_norm165_degree2256.json').read_text())
for r in p['source']:
 if r[0]=='u':assert r==['u','*',3,'Pweight'];r[2]=2
p['name']='integer24_sharp_pair_norm165_degree2240';p['exact_degree']=2240;p['norm_degree']=2224;p['separator_multiplier']=2;p['factor_degrees']['unit']=2224
save(p)
# Literal comparison systems, with dead finalizer gates pruned.
for filename,outputs,degree in [
 ('integer24_sharp_pair_norm165_degree2240.json',[['Nk',1],['Nt',1],['Norm',0]],2224),
 ('integer25_small_weight131_degree920.json',[['norm_main',1],['norm_index',1],['norm_transport',1],['norm13',0]],872),
 ('integer26_ordinary_two_root123_degree214.json',[['N1',1],['Nk',1],['Nt',1],['Ns',1],['res',0]],128)]:
 p=json.loads((H/filename).read_text());live={x[0] for x in outputs};rows=[]
 for row in p['source'][::-1]:
  if row[0] in live: rows.append(row);live.update(x for x in row[2:] if isinstance(x,str))
 p['source']=rows[::-1];p.pop('output');p['outputs']=outputs;p['exact_degree']=degree;p['equation_count']=len(outputs)
 p['ledger']={'operations':len(rows),'multiplications':sum(r[1]=='*' for r in rows),'additions_subtractions':sum(r[1]!='*' for r in rows)}
 p['name']=f"integer{p['variable_count']}_system{len(rows)}_degree{degree}";save(p)
