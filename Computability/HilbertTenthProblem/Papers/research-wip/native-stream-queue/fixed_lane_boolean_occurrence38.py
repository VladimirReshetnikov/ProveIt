#!/usr/bin/env python3
"""Three complete quartics for a fixed, externally certified lane query.

Bounded standalone CLI. Historical files are authenticated as inert data only.
This is occurrence at a supplied index, not a turmite or first-hit compiler.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
import random

WIP = 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
PINS = {
 WIP+'presburger_congruence_five.py':'f33ba14f16009f4e825e00a91d1714696dadf34002ada3bf72fcbccc04a52cfc',
 WIP+'presburger_congruence_five.json':'a9bf8ced9cdc541fc918994b522b0675b961fe6acd74b6aef97e81f2723c5403',
 WIP+'presburger_congruence_five.md':'ee158f85fc74e1027de08433f4e4d9065c2c7b219670519047116a04aa931fa5',
 WIP+'review_presburger_congruence_five.md':'23e5142192d14bd98143a47a1a07a15d1d1ec115550957b0e7d42df88ac7c30e',
 WIP+'review_turmite_first_revisit38_intake.md':'0742f42aa92b2b9f5b292176a730550d4e58aefd512c5c4a1e6f7fdf56944b8a',
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits/source-packet-PROOF.md':'d4fa1ecec1b80d320a36ee464095c38fe671531757cc5dfcb85c3f8b62e30f12',
}
MODULI = {'A':4,'B':5,'C':3,'E':7}
MODES = ('shared_mux','expanded_dnf','optimized_mux')

def require(condition,message):
    if not condition: raise ValueError(message)

def exact(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,(list,tuple)): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def authenticated(repo):
    for path,digest in PINS.items():
        require(hashlib.sha256((repo/path).read_bytes()).hexdigest()==digest,'changed premise: '+path)

class Circuit:
    def __init__(self):
        self.gates=[]; self.witnesses=['lo','hi']; self.rows=[]; self.row_names=[]
    def op(self,name,kind,a,b):
        self.gates.append([name,kind,a,b]); return name
    def row(self,name,port):
        self.row_names.append(name);self.rows.append(port)
    def witness(self,name):
        self.witnesses.append(name);return name
    def congruence(self,label,L,d):
        qp,qm,b,s,h=[self.witness(label+'_'+v) for v in ('qp','qm','b','s','h')]
        f=lambda suffix,kind,a,c:self.op(label+'_'+suffix,kind,a,c)
        bs=f('bs','mul',b,s);rem=f('rem','add',bs,b)
        truth=f('truth','sub',1,b)
        r0=f('split','mul',qp,qm)
        quotient=f('q','sub',qp,qm);dq=f('dq','mul',d,quotient)
        r1=f('residue','sub',f('Ldq','sub',L,dq),rem)
        r2=f('range','sub',f('rh','add',rem,h),d-1)
        r3=f('boolean','mul',b,truth)
        r4=f('inactive','sub',bs,s)
        for suffix,port in zip(('split','residue','range','boolean','inactive'),(r0,r1,r2,r3,r4)):
            self.row(label+'_'+suffix,port)
        return truth,b
    def defining(self,z,kind,a,b):
        self.witness(z)
        if kind=='and':
            p=self.op(z+'_product','mul',a,b)
            r=self.op(z+'_row','sub',z,p)
        elif kind=='or':
            p=self.op(z+'_product','mul',a,b)
            v=self.op(z+'_sum','add',a,b)
            r=self.op(z+'_row','add',self.op(z+'_difference','sub',z,v),p)
        else: raise ValueError('unsupported gate')
        self.row(z+'_definition',r)
        return z
    def finish(self,mode,common_length):
        squares=[self.op('square_'+str(i),'mul',r,r) for i,r in enumerate(self.rows)]
        output=squares[0]
        for i,square in enumerate(squares[1:],1):output=self.op('sum_'+str(i),'add',output,square)
        return {'mode':mode,'inputs':['n'],'witnesses':self.witnesses,'instructions':self.gates,
          'residuals':self.rows,'residual_names':self.row_names,'output':output,
          'common_prefix_length':common_length,
          'ledger':{'M':sum(g[1]=='mul' for g in self.gates),'A':sum(g[1]!='mul' for g in self.gates),
                    'operations':len(self.gates),'witnesses':len(self.witnesses),'residuals':len(self.rows)},
          'exact_degree':4}

def build(mode):
    require(mode in MODES,'unknown mode')
    c=Circuit(); op=c.op
    n2=op('twice_n','add','n','n')
    x=op('x','add',n2,1)
    y=op('y','sub',op('three_n','add',n2,'n'),2)
    LA=op('L_A','sub',op('x_plus_y','add',x,y),1)
    LB=op('L_B','sub',op('twice_x_minus_y','sub',op('twice_x','add',x,x),y),3)
    LE=op('L_E','sub',y,1)
    upper=op('upper','sub',50,'n')
    c.row('domain_lower',op('lower_row','sub','n','lo'))
    c.row('domain_upper',op('upper_row','sub',upper,'hi'))
    truth={};complement={}
    for label,L in (('A',LA),('B',LB),('C',x),('E',LE)):
        truth[label],complement[label]=c.congruence(label,L,MODULI[label])
    common_length=len(c.gates)
    K=c.defining('K','and',complement['A'],complement['B'])
    if mode=='shared_mux':
        H=op('H','sub',1,K)
        left=c.defining('left','and',H,truth['C'])
        right=c.defining('right','and',K,truth['E'])
        final=op('query_row','sub',op('branches','add',left,right),1)
    elif mode=='expanded_dnf':
        ac=c.defining('AC','and',truth['A'],truth['C'])
        bc=c.defining('BC','and',truth['B'],truth['C'])
        ke=c.defining('KE','and',K,truth['E'])
        joined=c.defining('joined','or',ac,bc)
        final=op('query_row','sub',op('branches','add',joined,ke),1)
    else:
        diff=op('E_minus_C','sub',truth['E'],truth['C'])
        mixed=op('K_difference','mul',K,diff)
        final=op('query_row','sub',op('query_value','add',truth['C'],mixed),1)
    c.row('final_truth',final)
    return c.finish(mode,common_length)

# Independent sparse ring: monomials are sorted tuples of variable names.
def P(x):
    if isinstance(x,str):return {(x,):1}
    return {():x} if x else {}
def add(a,b):
    out=dict(a)
    for mon,coef in b.items():
        out[mon]=out.get(mon,0)+coef
        if not out[mon]:del out[mon]
    return out
def neg(a):return {m:-c for m,c in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}

def run(packet,values,polynomial=False):
    env=dict(values)
    def get(v):return P(v) if polynomial and type(v) is int else v if type(v) is int else env[v]
    for name,kind,a,b in packet['instructions']:
        a,b=get(a),get(b)
        env[name]=({'add':add,'sub':sub,'mul':mul}[kind](a,b) if polynomial else
                   a+b if kind=='add' else a-b if kind=='sub' else a*b)
    return env[packet['output']],[env[r] for r in packet['residuals']]

def reference(packet):
    v={x:P(x) for x in packet['inputs']+packet['witnesses']}
    n=v['n']
    # Direct affine formulas deliberately bypass coordinate producer sharing.
    Ls={'A':sub(mul(P(5),n),P(2)),'B':add(n,P(1)),
        'C':add(mul(P(2),n),P(1)),'E':sub(mul(P(3),n),P(3))}
    rows=[sub(n,v['lo']),sub(sub(P(50),n),v['hi'])]
    truths={};bits={}
    for label,d in MODULI.items():
        qp,qm,b,s,h=(v[label+'_'+x] for x in ('qp','qm','b','s','h'))
        remainder=mul(b,add(s,P(1)))
        truths[label]=sub(P(1),b);bits[label]=b
        rows += [mul(qp,qm),sub(sub(Ls[label],mul(P(d),sub(qp,qm))),remainder),
                 sub(add(remainder,h),P(d-1)),mul(b,sub(P(1),b)),mul(sub(b,P(1)),s)]
    K=v['K'];rows.append(sub(K,mul(bits['A'],bits['B'])))
    A,B,C,E=(truths[x] for x in ('A','B','C','E'))
    if packet['mode']=='shared_mux':
        rows += [sub(v['left'],mul(sub(P(1),K),C)),sub(v['right'],mul(K,E)),sub(add(v['left'],v['right']),P(1))]
    elif packet['mode']=='expanded_dnf':
        ac,bc,ke,j=(v[x] for x in ('AC','BC','KE','joined'))
        rows += [sub(ac,mul(A,C)),sub(bc,mul(B,C)),sub(ke,mul(K,E)),
                 sub(j,sub(add(ac,bc),mul(ac,bc))),sub(add(j,ke),P(1))]
    else:rows.append(sub(add(C,mul(K,sub(E,C))),P(1)))
    total={}
    for r in rows:total=add(total,mul(r,r))
    return rows,total

def canonical(n,mode):
    require(type(n) is int,'exact signed index required')
    values={'n':n,'lo':max(n,0),'hi':max(50-n,0)}
    truths={}
    for label,L in (('A',5*n-2),('B',n+1),('C',2*n+1),('E',3*n-3)):
        q,r=divmod(L,MODULI[label])
        ws=(max(q,0),max(-q,0),int(r>0),max(r-1,0),MODULI[label]-1-r)
        values.update(zip((label+'_'+s for s in ('qp','qm','b','s','h')),ws));truths[label]=int(r==0)
    A,B,C,E=(truths[x] for x in ('A','B','C','E'))
    K=(1-A)*(1-B);values['K']=K
    if mode=='shared_mux':values.update(left=(1-K)*C,right=K*E)
    elif mode=='expanded_dnf':values.update(AC=A*C,BC=B*C,KE=K*E,joined=int(bool(A*C or B*C)))
    return values

def query(n):
    x,y=2*n+1,3*n-2
    A=(x+y-1)%4==0;B=(2*x-y-3)%5==0;C=x%3==0;E=(y-1)%7==0
    return 0<=n<=50 and ((A or B) and C or not(A or B) and E)

def structure(packet):
    defined=set(packet['inputs']+packet['witnesses']);parents={}
    require(len(defined)==len(packet['inputs'])+len(packet['witnesses']),'duplicate input')
    for name,kind,a,b in packet['instructions']:
        require(name not in defined and kind in ('add','sub','mul'),'invalid gate')
        require(all(type(x) is int or type(x) is str and x in defined for x in (a,b)),'undefined operand')
        defined.add(name);parents[name]=[x for x in (a,b) if type(x) is str]
    live=set();stack=[packet['output']]
    while stack:
        name=stack.pop()
        if name in live:continue
        live.add(name);stack.extend(parents.get(name,[]))
    require(set(parents)<=live,'dead paid gate')
    require(set(packet['inputs']+packet['witnesses'])<=live,'unused coordinate')
    return len(parents)

def verify(repo):
    authenticated(repo)
    counts={}
    def check(label,ok):
        require(ok,label);counts[label]=counts.get(label,0)+1
    packets=[build(mode) for mode in MODES]
    expected=((45,76,121,25,26),(49,81,130,27,28),(42,72,114,23,24))
    forms=[]
    for packet,ledger in zip(packets,expected):
        check('complete_live_sources',structure(packet)==ledger[2])
        check('paid_ledgers',tuple(packet['ledger'][k] for k in ('M','A','operations','witnesses','residuals'))==ledger)
        symbols={x:P(x) for x in packet['inputs']+packet['witnesses']}
        total,rows=run(packet,symbols,True);ref_rows,ref_total=reference(packet)
        check('complete_residual_inventory',len(rows)==len(ref_rows)==ledger[4])
        for a,b in zip(rows,ref_rows):check('independent_residual_coefficients',a==b)
        check('independent_complete_polynomial_coefficients',total==ref_total)
        check('exact_quartic',max(map(len,total))==4 and total.get(tuple(sorted(('A_qp','A_qp','A_qm','A_qm'))))==1)
        forms.append({'packet':packet,'coefficient_count':len(total),
                      'polynomial':[[list(m),c] for m,c in sorted(total.items())]})
    base=packets[0];prefix=base['common_prefix_length']
    for packet in packets[1:]:
        check('same_paid_affine_atom_domain_prefix',packet['instructions'][:prefix]==base['instructions'][:prefix])
        check('same_atom_domain_coordinate_interface',packet['witnesses'][:22]==base['witnesses'][:22])
    # Formal all-value discrepancy: expanding the OR in DNF requires C^2=C.
    a,b,c,e=map(P,('a','b','c','e'));k=mul(sub(P(1),a),sub(P(1),b))
    ac,bc=mul(a,c),mul(b,c)
    expanded=add(sub(add(ac,bc),mul(ac,bc)),mul(k,e))
    optimized=add(c,mul(k,sub(e,c)))
    check('exact_boolean_reduction_defect',sub(expanded,optimized)==mul(mul(a,b),mul(c,sub(P(1),c))))
    for bits in range(16):
        A,B,C,E=((bits>>i)&1 for i in range(4));K=(1-A)*(1-B)
        mux=(1-K)*C+K*E;dnf=A*C+B*C-A*B*C*C+K*E
        check('complete_boolean_truth_table',mux==dnf==C+K*(E-C) and mux in (0,1))
    accepted=[n for n in range(51) if query(n)]
    fixtures=[]
    for n in list(range(-32,84))+[-10**30,10**30]:
        for packet in packets:
            values=canonical(n,packet['mode']);out,rows=run(packet,values)
            check('natural_canonical_assignment',all(values[x]>=0 for x in packet['witnesses']))
            check('signed_index_acceptance',bool(out==0)==query(n))
            check('canonical_atom_equations',not any(rows[2:22]))
            if query(n):
                check('genuine_complete_zero',not any(rows))
                fixtures.append({'mode':packet['mode'],'index':n,'witnesses':{x:values[x] for x in packet['witnesses']}})
                for name in packet['witnesses']:
                    changed=dict(values);changed[name]+=1
                    check('reject_mutated_unique_witness',run(packet,changed)[0]!=0)
    rng=random.Random(3805)
    for packet in packets:
        _,ref=reference(packet)
        for j in range(24):
            values={x:(Fraction(rng.randrange(-5,6),rng.randrange(1,5)) if j<8 else rng.randrange(-5,6)) for x in packet['inputs']+packet['witnesses']}
            value=0
            for mon,coef in ref.items():
                term=coef
                for x in mon:term*=values[x]
                value+=term
            check('whole_signed_rational_values',run(packet,values)[0]==value)
            if j<8:check('whole_rational_values',True)
    return {'status':'PASS','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'pins':dict(PINS),'counts':counts,'forms':forms,'accepted_indices':accepted,'zero_fixtures':fixtures,
      'lane':{'position':['2*n+1','3*n-2'],'time':'5*n+2','domain':[0,50],
              'certificate':'external premise only; no actual turmite realization is claimed'},
      'atom_moduli':dict(MODULI),'atom_affines':{'A':'5*n-2','B':'n+1','C':'2*n+1','E':'3*n-3'},
      'shared_query':'D AND ((H AND C) OR ((NOT H) AND E)), H=A OR B',
      'expanded_query':'D AND ((A AND C) OR (B AND C) OR ((NOT A) AND (NOT B) AND E))',
      'scope':'Three complete fixed-lane supplied-index occurrence quartics. Same outer and 22 atom/domain coordinates; different canonical gate coordinates. Natural-witness zero equivalence, not all-value equality between the three SOS polynomials. No lane certification, first-hit minimality, turmite implementation, universal bound, or optimality claim.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root',required=True,type=Path)
    parser.add_argument('--output',type=Path);parser.add_argument('--expect',type=Path)
    args=parser.parse_args();receipt=verify(args.repo_root.resolve())
    if args.expect:require(exact(receipt,json.loads(args.expect.read_text())),'saved receipt differs')
    if args.output:args.output.write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'counts':receipt['counts'],
                     'ledgers':[f['packet']['ledger'] for f in receipt['forms']]},sort_keys=True))
if __name__=='__main__':main()
