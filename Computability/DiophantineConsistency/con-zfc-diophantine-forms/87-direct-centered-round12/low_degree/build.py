"""Newly authored factored polynomial compiler. No upstream code is executed."""
import ast,copy,json,hashlib
from pathlib import Path
import sympy as S
R=Path(__file__).resolve().parent
ports=['beta','K0','MC','MF','cone_A','cone_B']
basevars=['J3','F','alpha','z','f','h','r','v_scale','w3','tau','eta','y','gamma','o','j','E','c','a','V','I','t','p','qpos','rpos']
def parse(x):return ast.parse(x,mode='eval').body
def sub(n,defs):
 if isinstance(n,ast.Name) and n.id in defs:return copy.deepcopy(defs[n.id])
 z=copy.deepcopy(n)
 for field,value in ast.iter_fields(z):
  if isinstance(value,ast.AST):setattr(z,field,sub(value,defs))
  elif isinstance(value,list):setattr(z,field,[sub(v,defs) if isinstance(v,ast.AST) else v for v in value])
 return z
def inline(s,defs):return sub(parse(s),defs)
def text(n):return ast.unparse(n)
def fail(x,m):
 if not x:raise ValueError(m)
regs={}
for n,x in [('q','beta*(3*J3+1)+1'),('W','4*(3*w3+1)'),('X','q*W'),('Y','(2*v_scale+1)*q**3'),('C','q-F-alpha'),('k','1-V+j*c+h*E'),('H','4*a+3'),('Delta','a*a+H'),('R','((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*(3*J3+1)'),('T','cone_A*F*cone_B*C-(q-cone_A*F-cone_B*C)**2'),('Z','eta*(k-eta)'),('Pos','1+p*p+qpos*qpos+rpos*(rpos+1)')]:regs[n]=inline(x,regs)
rows=['a-E-Y','E-X*(a-E)','c-eta-k*(a-E)','tau*tau+(2*tau-k)*E*(c-eta)-1','X*X+2*X*(a*c+gamma*H)+H*(2*a*c*gamma+gamma*gamma*H-c*c)-1','c*j-V-R','(K0+W)*C-F-z*(q-1)','V+c-f*o','I-(2*r+1)*c*c','I*I-Delta*(f*f-1)','I*I*(V*V-y*y)+y*y-1','T*Z-(t*t-T-Z+1)**2-Pos']
base=[inline(x,regs) for x in rows]
# Exact degree upper bounds plus sparse homogeneous top components. Fixed ports are coefficients.
def top(n,vs):
 zero=(0,)*len(vs)
 if isinstance(n,ast.Constant):return 0,({zero:S.Integer(n.value)} if n.value else {})
 if isinstance(n,ast.Name):
  if n.id in vs:
   k=list(zero);k[vs.index(n.id)]=1;return 1,{tuple(k):S.Integer(1)}
  fail(n.id in ports,'undeclared '+n.id);return 0,{zero:S.Symbol(n.id)}
 if isinstance(n,ast.UnaryOp):
  d,p=top(n.operand,vs);return d,{m:-c for m,c in p.items()}
 if isinstance(n.op,ast.Pow):
  d,p=top(n.left,vs);power=ast.literal_eval(n.right);out={zero:S.Integer(1)}
  for _ in range(power):out=mul(out,p)
  return d*power,out
 d,p=top(n.left,vs);e,q=top(n.right,vs)
 if isinstance(n.op,ast.Mult):return d+e,mul(p,q)
 if isinstance(n.op,ast.Sub):q={m:-c for m,c in q.items()}
 out={}
 if d>=e:out.update(p)
 if e>=d:
  for m,c in q.items():out[m]=S.expand(out.get(m,0)+c)
 return max(d,e),{m:c for m,c in out.items() if c!=0}
def mul(p,q):
 out={}
 for a,c in p.items():
  for b,d in q.items():
   m=tuple(x+y for x,y in zip(a,b));out[m]=S.expand(out.get(m,0)+c*d)
 return {m:c for m,c in out.items() if c!=0}
def emit(name,defs,deleted,degree,cert,aux=False):
 # defs ordered: each right side expands previous definitions then source registers.
 restore={}
 for n,x in defs:
  restore[n]=sub(inline(x,regs),restore)
 rs=copy.deepcopy(base)
 if aux:rs[10]=inline('(f*o+y)**2-Delta*(f*f-1)*(c+y)*(2*f*o+y-c)-1',regs)
 # aux row uses new y already; other rows do not mention y.
 rs=[sub(x,restore) for i,x in enumerate(rs) if i not in deleted]
 vs=[x for x in basevars if x not in restore]
 if 'F' in restore:vs.append('C')
 if 'E' in restore and 'a' in restore and any(isinstance(v,ast.Name) and v.id=='Yfree' for x in restore.values() for v in ast.walk(x)):vs.append('Yfree')
 ds=[];cs=S.Integer(0);target=tuple(cert.get(n,0) for n in vs)
 for x in rs:
  d,p=top(x,vs);ds.append(d)
  if 2*d==degree:
   for m,c in p.items():
    other=tuple(a-b for a,b in zip(target,m))
    if min(other)>=0:cs+=c*p.get(other,0)
 fail(max(ds)*2==degree,name+' upper degree '+str(ds));cs=S.factor(cs)
 fail(cs!=0,name+' vanished certificate')
 fail(all(c>0 for c in S.Poly(cs,*map(S.Symbol,ports)).coeffs()),'positive port coeff')
 packet={'name':name,'domain':'unrestricted integers','variables':vs,'variable_count':len(vs),'fixed_numerals':ports,'residuals':[text(x) for x in rs],'equation_count':len(rs),'single_polynomial':'sum of the squares of every residual','exact_degree':degree,'residual_degree_bounds':ds,'degree_certificate':{'monomial':cert,'coefficient':str(cs)},'restoration':{n:text(x) for n,x in restore.items()},'deleted_source_rows':deleted,'first_root_restoration':'tau_old=tau+E*(c-eta)','auxiliary_root_shear':aux,'coefficient_binding':'BINDING.json','proof':'PROOF.md'}
 (R/(name+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
 print(name,len(vs),len(rs),degree,cs)
pivot=[('F','(K0+W)*C-z*(q-1)'),('alpha','q-F-C')]
# C on right is new free coordinate, not source's expanded q-F-alpha.
# Correct the pivot by using a protected identifier then renaming.
regs['C']=parse('C')
common=[('V','f*o-c'),('I','(2*r+1)*c*c')]+pivot
emit('integer21_degree16',common,[6,7,8],16,{'w3':8,'C':8},aux=True)
emit('integer20_degree20',common+[('a','E+Y')],[0,6,7,8],20,{'f':4,'v_scale':4,'J3':12})
emit('integer19_degree32',common+[('E','X*Y'),('a','(X+1)*Y')],[0,1,6,7,8],32,{'eta':4,'h':4,'w3':4,'v_scale':4,'J3':16})
emit('integer18_degree88',common+[('E','X*Y'),('a','(X+1)*Y'),('eta','c-Y*k')],[0,1,2,6,7,8],88,{'h':8,'w3':8,'v_scale':16,'J3':56})
emit('integer20_degree20_free_scale',common+[('E','X*Yfree'),('a','(X+1)*Yfree')],[1,6,7,8],20,{'eta':4,'h':4,'J3':4,'w3':4,'Yfree':4})
