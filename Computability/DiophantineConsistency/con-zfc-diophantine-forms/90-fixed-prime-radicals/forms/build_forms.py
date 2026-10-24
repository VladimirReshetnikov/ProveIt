#!/usr/bin/env python3
from pathlib import Path
import ast,json,hashlib,zipfile,gzip
from norm_dag import DAG

HERE=Path(__file__).resolve().parent
OUT=HERE
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
VARS13=['j','C','z','h','r','v','w','T','c','s','p1','p2','xi']
DEFS=[
 ('J','6*j+1'),('q','beta*J+1'),('W','4*(3*w+1)'),
 ('F','(K0+W)*C-z*(q-1)'),('alpha','q-F-C'),
 ('X','q*W'),('Y','(2*v+1)*q**3'),('E','X*Y'),('a','(X+1)*Y'),
 ('H','4*a+3'),('Delta','a**2+H'),
 ('R','(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*J'),
 ('k','R+1+h*E'),('eta','c-Y*k'),('zeta','k-eta'),
 ('u','E*Y*k'),('Afirst','u*(u+k)+1'),
 ('m','(2*r+1)*c**2'),('Df','1+Delta*m**2'),
 ('I','Delta*m'),('Q','I**2'),('delta','Q-1'),
 ('V','Df*(c*T-R)-c'),('D0','X+a*c'),('Cmain','Delta*c**2+1'),
 ('Gnative','cone_A*F*cone_B*C-(q-cone_A*F-cone_B*C)**2'),
 ('Zeta','eta*zeta'),('Nguard','Gnative*Zeta-(s**2-Gnative-Zeta+1)**2'),
]

def compile_expr(expr,d,values):
 def go(n):
  if isinstance(n,ast.Constant) and isinstance(n.value,int):return n.value
  if isinstance(n,ast.Name):return values[n.id]
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return d.sub(0,go(n.operand))
  if isinstance(n,ast.BinOp):
   if isinstance(n.op,ast.Pow):
    if not isinstance(n.right,ast.Constant) or not isinstance(n.right.value,int) or n.right.value<0:raise ValueError('nonfixed exponent')
    return d.pow(go(n.left),n.right.value)
   a,b=go(n.left),go(n.right)
   if isinstance(n.op,ast.Add):return d.add(a,b)
   if isinstance(n.op,ast.Sub):return d.sub(a,b)
   if isinstance(n.op,ast.Mult):return d.mul(a,b)
  raise ValueError(ast.dump(n))
 return go(ast.parse(expr,mode='eval').body)

def build(n,centered):
 variant = centered if isinstance(centered,str) else ('auxiliary' if centered else 'none')
 variables=VARS13 if n==13 else VARS13[:-1]+['p3','xi']
 d=DAG(variables+PORTS);values={x:x for x in d.inputs};defs=list(DEFS)
 if n==13:
  defs += [('Spositivity','24*Nguard-21-(6*p1-1)**2-(6*p2-1)**2')]
 else:defs += [('guard','Nguard-1-p1**2-p2**2-p3*(p3+1)')]
 defs += [('rad_A','9*H**2*Afirst'),('rad_B','81*H**2*Df'),('rad_D','Cmain')]
 if n==13:defs += [('rad_G','6561*H**2*Spositivity')]
 defs += [('Cnum','729*H**2*(Q*V**2-1)')]
 if variant=='full':
  carrier='D0+H*(xi+27*V+3*u+9*(a+2)*m)'
 elif variant=='half':
  defs += [('rad_A','4*rad_A'),('rad_B','4*rad_B'),('rad_D','4*rad_D'),('Cnum','4*Cnum')]
  carrier='2*D0+H*(xi+54*V+6*u+3*k+18*(a+2)*m)'
 else:carrier='D0+H*(xi+27*V)' if centered else 'D0+H*xi'
 defs += [('norm_z',carrier)]
 for name,expr in defs:values[name]=compile_expr(expr,d,values)
 radicands=[values[x] for x in ['rad_A','rad_B','rad_D']+(['rad_G'] if n==13 else [])]
 co=d.norm_coefficients(radicands)
 norm=d.clear_last(co,values['norm_z'],values['Cnum'],values['delta'])
 out=norm if n==13 else d.sub(d.mul(d.add(1,d.mul(4,norm)),d.add(1,d.mul(4,values['guard']))),1)
 degree=(1392 if centered else 1408) if n==13 else {'none':748,'auxiliary':700,'full':664,'half':652}[variant]
 meta={'name':f'integer{n}_degree{degree}','domain':'unrestricted integers','variables':variables,'variable_count':len(variables),'fixed_ports':PORTS,'coefficient_binding':'coefficients/BINDING.json','exact_degree':degree,'prefix_abbreviations':defs,'root_count':5 if n==13 else 4,'denominator_exponent':16 if n==13 else 8,'auxiliary_centered':bool(centered),'carrier_variant':variant,'norm_identity':'delta**(2**(root_count-1)) * product over all root signs of (norm_z + signed roots of rad_A,rad_B,rad_D,'+('rad_G,' if n==13 else '')+'Cnum/delta)','finalizer':'norm=0' if n==13 else '(1+4*norm)*(1+4*guard)-1=0','degree_certificate':'DEGREE_PROOF.md','norm_output':norm,'proof_dependencies':['Normalized CRT native endpoint with complete coefficient tuple','Distinct valuation radical recovery','Adjacent-coefficient rational Pell descent']+(['Three generalized pentagonal numbers'] if n==13 else [])}
 return d.finish(out,meta)

def coefficients():
 # The six immutable payloads are inputs; rebuilding never manufactures them.
 from verify_final_forms import load_constants
 load_constants(OUT)


def main():
 OUT.mkdir(parents=True,exist_ok=True);metrics=[]
 for n in [13,14]:
  for centered in ([False,True] if n==13 else [False,True,'full','half']):
   p=build(n,centered);name=p['name']+'.json';(OUT/name).write_text(json.dumps(p,indent=2)+'\n')
   m={k:p[k] for k in ['name','variable_count','exact_degree','live_binary_operations','auxiliary_centered','carrier_variant']};metrics.append(m);print(m)
 coefficients();(OUT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
if __name__=='__main__':main()
