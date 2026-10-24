#!/usr/bin/env python3
"""Independent fresh audit; reads frozen sources but imports no emitter."""
from collections import Counter
import gzip,hashlib,itertools,json,sys
from pathlib import Path
import sympy as S
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json'
COEFFICIENTS=ROOT/'con-zfc-diophantine-forms/36-small-tuple/coefficients'
def need(b,label):
    if not b:raise RuntimeError(label)
def eq(a,b,label):need(S.expand(a-b)==0,label)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

parent=json.loads(PARENT.read_text());dependent={'f'};retained=[]
for row in parent['source']:
    if any(type(x)is str and x in dependent for x in row[2:]):dependent.add(row[0])
    else:retained.append(row)
need(len(retained)==50 and len(dependent)-1==17,'exact f dependency closure')
need([r for r in parent['source']if 'f'in r[2:]]==[['L16','*','f','f'],['auxiliary_Tf','*','T','f']],'exact f consumers')
need([r for r in parent['source']if 'T'in r[2:]]==[['auxiliary_Tf','*','T','f']],'exact T consumer')

packets={n:json.loads((HERE/(n+'.json')).read_text())for n in ['field73','unit75']}
results={}
for name,p in packets.items():
    need(p['source'][:50]==retained,'literal retained prefix')
    need(p['witnesses']==[x for x in parent['witnesses']if x!='f']and p['fixed_numerals']==parent['fixed_numerals'],'exact retained inputs')
    known=set(p['witnesses']+p['fixed_numerals']);parents={}
    for n,op,a,b in p['source']:
        need(n not in known and op in ['+','-','*'],'fresh arithmetic node')
        need(all(type(x)is int or x in known for x in [a,b]),'topological operands')
        known.add(n);parents[n]=(a,b)
    live=set();todo=[p['output']]
    while todo:
        x=todo.pop()
        if type(x)is int or x in live:continue
        live.add(x);todo.extend(parents.get(x,()))
    need(live==known,'all gates and ports live')
    need(len(p['source'])==(73 if name=='field73' else 75),'exact operation count')
    results[name]=dict(operations=len(p['source']),operation_counts=dict(Counter(r[1]for r in p['source'])),all_gates_and_inputs_live=True,circuit_sha256=sha(HERE/(name+'.json')))

# Exact expressions at abstract factors: no huge prefix is unfolded.
D,u,b,Q,y,P0,Nk,Nt=S.symbols('D u b Q y P0 Nk Nt');P=P0*Nk*Nt
a=Q*(D*u*u+b*b)-(Q-1)*y*y-1;B=2*Q*u*b
field=(P*(a+1)-1)**2-D*(P*B)**2
unit=P*(a*a-D*B*B+1)-1
for name,p in packets.items():
    pre='field'if name=='field73'else'unit'
    cuts={pre+'_D':D,pre+'_p':D*u*u,pre+'_b2':b*b,
          'norm_pair':P0,'norm_index':Nk,'norm_transport':Nt,'R16':Q,'aux_y2':y*y}
    needed={p['output']}
    for n,op,x,z in reversed(p['source']):
        if n in needed and n not in cuts:needed.update((x,z))
    e=dict(cuts)
    def get(x):return x if type(x)is int else e[x]
    for n,op,x,z in p['source']:
        if n not in needed or n in e:continue
        xx,zz=get(x),get(z);e[n]=xx+zz if op=='+'else xx-zz if op=='-'else xx*zz
    eq(e[p['output']],field if name=='field73'else unit,'exact emitted tail identity')
eq(field,P*unit+(P-1)*(2*P*a-1),'whole field/unit relationship')
c,R,T,f=S.symbols('c R T f');uu=c*T;bb=c+R*D;ef=f*f-D
V=uu*f-c-R*f*f;Na=Q*V*V-(Q-1)*y*y
aa=Q*(D*uu*uu+bb*bb)-(Q-1)*y*y-1;BB=2*Q*uu*bb
qaux=Q*(uu*uu-2*R*uu*f+2*R*bb+R*R*ef)
eq(Na-1,aa-BB*f+ef*qaux,'full auxiliary remainder identity')

# Exact shifted-mask polynomial identity, before any zero is imposed.
q,C,F,MC,MF,J=S.symbols('q C F MC MF J')
rank=(q*(q-F)-C)*(q*q-1)+(MC+q*(MF+(q-1)/J))*J
Sword=C-1+q*F;Tword=MC*J+1+q*(MF*J-1)
eq(rank,(q*q-Sword)*(q*q-1)+Tword,'actual C low-word binding using beta J=q-1')

# Square residues prove negative-unit exclusions universally.
residues=0
for a0,ff,z in itertools.product(range(4),repeat=3):
    delta=a0*a0+4*a0+3
    need((ff*ff-delta*z*z)%4!=3,'normalized strong negative unit');residues+=1
for s,vv,yy in itertools.product(range(4),repeat=3):
    need((s*s*vv*vv+(1-s*s)*yy*yy)%4!=3,'auxiliary negative unit');residues+=1
for aa0,dd,bb0 in itertools.product(range(4),range(4),[0,2]):
    need((aa0*aa0-dd*bb0*bb0+1)%4!=3,'unit norm guard negative unit');residues+=1

# Uniform coefficient witnesses, independently derived from source factors.
Jj,Ff,al,z,h,ga,ii,eta,ze,w,ss,beta=S.symbols('J F alpha z h gamma i eta zeta w s beta')
q0=beta*Jj;k0=eta+ze;transport=w*(q0-Ff-al)-z*q0
Ptop=8*h*ga*k0**3*w**5*ss**8*q0**29*transport
Qtop=ii**2*k0**4*w**4*ss**8*q0**28
Dtop=ii**2*k0**4*w**2*ss**6*q0**20
Rtop=q0**3*(q0-Ff)
vs=[Jj,Ff,al,z,h,ga,ii,eta,ze,w,ss]
heads={'field73':Ptop**2*Qtop**2*Rtop**4*Dtop**4,'unit75':Ptop*Qtop**2*Rtop**4*Dtop**4}
monomials={'field73':Jj**212*h*h*ga*ga*ii**12*eta**30*w**26*ss**56*z*z,
           'unit75':Jj**182*h*ga*ii**12*eta**27*w**21*ss**48*z}
coefficients={'field73':64*beta**212,'unit75':-8*beta**182}
for name in heads:
    poly=S.Poly(S.expand(heads[name]),*vs)
    degree=342 if name=='field73' else 293
    need(poly.total_degree()==degree,'head degree')
    eq(poly.coeff_monomial(monomials[name]),coefficients[name],'uniform distinguished coefficient')
    results[name].update(exact_degree=degree,selected_monomial=str(monomials[name]),selected_coefficient=str(coefficients[name]))

# Independent byte authentication and the entire arithmetic port contract.
binding_path=COEFFICIENTS/'COEFFICIENT_BINDING.json';binding=json.loads(binding_path.read_text())
ports={};hashes={}
for e in binding['materialization']['files']:
    p=COEFFICIENTS/e['file'];raw=gzip.decompress(p.read_bytes())
    need(sha(p)==e['gzip_sha256']and hashlib.sha256(raw).hexdigest()==e['sha256'],'whole tuple hashes')
    n=int.from_bytes(raw,'little');need(n.bit_length()==e['bits'],'port bit length')
    ports[e['port']]=n;hashes[e['port']]=e['sha256']
need(set(ports)=={'beta','K','MC','MF_source'},'whole source36 tuple')
d=binding['d'];beta0=ports['beta'];base=beta0+1;high=ports['MF_source']-beta0
need(base==1<<d and d>=4 and ports['K']>0,'base/transport hypotheses')
need(0<ports['MC']<beta0 and 0<high<beta0,'native mask bounds')
need(ports['MC']%4==2 and high%8==4,'native mask trailing bits')
need(ports['MC'].bit_count()+high.bit_count()==d,'native population balance')
out=dict(status='PASS',scope='Independent exact finite algebra/data. Ordinary signed-T proof review in INDEPENDENT_REVIEW.md; no Lean or frozen-emitter execution.',
 python_optimization=sys.flags.optimize,sympy=S.__version__,parent_sha256=sha(PARENT),retained_rows=50,removed_rows=17,
 exact_tail_and_remainder_identities=True,actual_shifted_C_word_identity=True,negative_unit_residue_cases=residues,
 circuits=results,whole_tuple_raw_hashes=hashes,whole_binding_sha256=sha(binding_path),d=d,
 proof_boundaries=['Pell classification/step-down and inverse population remain ordinary inherited mathematics','Whole native blank-K215 calibration inherited from source36','No encoded internal-ZFC derivation'])
name='INDEPENDENT_REVIEW_OPTIMIZED.json'if sys.flags.optimize else'INDEPENDENT_REVIEW.json'
(HERE/name).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
