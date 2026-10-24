#!/usr/bin/env python3
"""Construct 14- and 13-integer equations as finite arithmetic DAGs.

The norm kernel is formed by exact repeated quadratic conjugation. All
kernel registers are polynomial abbreviations; none is quantified.
"""
import ast
import hashlib
import json
from pathlib import Path

from build import ROOT, PRIME, read_ports


def require(condition,message):
    if not condition:
        raise ValueError(message)


class Circuit:
    def __init__(self):
        self.nodes=[]
        self.memo={}
        self.numerals={}

    def number(self,n):
        return str(n)

    def op(self,op,a,b):
        if op in ('+','*') and a>b:
            a,b=b,a
        if op=='+':
            if a=='0': return b
            if b=='0': return a
        if op=='-':
            if b=='0': return a
            if a==b: return '0'
        if op=='*':
            if a=='0' or b=='0': return '0'
            if a=='1': return b
            if b=='1': return a
        try:
            aa,bb=int(a),int(b)
            if op=='+': return str(aa+bb)
            if op=='-': return str(aa-bb)
            if op=='*': return str(aa*bb)
        except ValueError:
            pass
        key=(op,a,b)
        if key in self.memo: return self.memo[key]
        name='n'+str(len(self.nodes)).zfill(4)
        self.nodes.append([name,a+op+b])
        self.memo[key]=name
        return name

    def add(self,a,b): return self.op('+',a,b)
    def sub(self,a,b): return self.op('-',a,b)
    def mul(self,a,b): return self.op('*',a,b)


def norm_kernel(n):
    """Norm of carrier - sum sqrt(rad_i), with an explicit trace."""
    cir=Circuit()
    rads=['rad'+str(i) for i in range(n)]
    value={0:'carrier'}
    value.update({1<<i:'-1' for i in range(n)})
    trace=[]

    def multiply(p,q):
        out={}
        for i,a in sorted(p.items()):
            for j,b in sorted(q.items()):
                t=cir.mul(a,b)
                for k in range(n):
                    if i & j & (1<<k):
                        t=cir.mul(t,rads[k])
                key=i^j
                out[key]=cir.add(out.get(key,'0'),t)
        return {k:v for k,v in out.items() if v!='0'}

    for i in range(n):
        bit=1<<i
        even={k:v for k,v in value.items() if not k&bit}
        odd={k^bit:v for k,v in value.items() if k&bit}
        esq=multiply(even,even)
        osq=multiply(odd,odd)
        new={}
        for k in sorted(set(esq)|set(osq)):
            new[k]=cir.sub(esq.get(k,'0'),cir.mul(rads[i],osq.get(k,'0')))
        value={k:v for k,v in new.items() if v!='0'}
        require(all(not(k & ((1<<(i+1))-1)) for k in value),'eliminated radical persists')
        trace.append({'radical_index':i,'even':even,'odd':odd,'result':value})
    require(set(value)=={0},'norm is not scalar')
    output=value[0]
    # Remove registers not needed by the final scalar (some cancelled trace entries remain).
    by_name=dict(cir.nodes)
    live=set()
    def walk(name):
        if name not in by_name or name in live: return
        live.add(name)
        for node in ast.walk(ast.parse(by_name[name],mode='eval')):
            if isinstance(node,ast.Name): walk(node.id)
    walk(output)
    nodes=[x for x in cir.nodes if x[0] in live]
    return {'radical_count':n,'carrier':'carrier','radicands':rads,
            'polynomial_abbreviations':nodes,'output':output,
            'binary_operations':len(nodes),
            'construction':'Repeated E^2-rad_i*O^2 in the free multiquadratic algebra',
            'trace':trace}


def source_definitions():
    return [
        ['Jnative','6*j+1'],
        ['q','beta*Jnative+1'],
        ['W','4*(3*w3+1)'],
        ['C','C_native'],
        ['c','2*c0+1'],
        ['i','2*r+1'],
        ['F','(K0+W)*C-z*(q-1)'],
        ['alpha','q-F-C'],
        ['X','q*W'],
        ['Y','(2*v_scale+1)*q**3'],
        ['E','X*Y'],
        ['a','E+Y'],
        ['H','4*a+3'],
        ['Delta','a**2+H'],
        ['R','(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*Jnative'],
        ['k','R+1+h*E'],
        ['eta','c-k*Y'],
        ['zeta','k-eta'],
        ['F2','1+Delta*i**2*c**4'],
        ['I','Delta*i*c**2'],
        ['V','F2*(c*T-R)-c'],
        ['Q','I**2'],
        ['delta','Q-1'],
        ['r_aux','Q*V**2-1'],
        ['Caux','delta*r_aux'],
        ['Afirst','1+X*Y**2*(X*Y**2+1)*k**2'],
        ['G','cone_A*F*cone_B*C-(q-cone_A*F-cone_B*C)**2'],
        ['Zeta','eta*zeta'],
        ['b_guard','G*Zeta-(pair_root**2-G-Zeta+1)**2-1-pair_pos1**2-pair_pos2**2'],
        ['Bguard','4*b_guard+1'],
        ['Dmain','1+Delta*c**2'],
        ['b0','X+a*c'],
        ['x_parity','2*t_parity+1'],
    ]


class Lead:
    """Safe degree upper bound together with that homogeneous coefficient."""
    def __init__(self,d,c): self.d,self.c=d,c%PRIME
    @staticmethod
    def lift(v): return v if isinstance(v,Lead) else Lead(0,v)
    def __add__(self,o):
        o=self.lift(o)
        d=max(self.d,o.d)
        return Lead(d,(self.c if self.d==d else 0)+(o.c if o.d==d else 0))
    __radd__=__add__
    def __neg__(self): return Lead(self.d,-self.c)
    def __sub__(self,o): return self+-self.lift(o)
    def __rsub__(self,o): return self.lift(o)+-self
    def __mul__(self,o):
        o=self.lift(o)
        return Lead(self.d+o.d,self.c*o.c)
    __rmul__=__mul__
    def __pow__(self,n): return Lead(self.d*n,pow(self.c,n,PRIME))


def calculate(text,env):
    def go(n):
        if isinstance(n,ast.Name): return env[n.id]
        if isinstance(n,ast.Constant): return n.value
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub): return -go(n.operand)
        if isinstance(n,ast.BinOp):
            a=go(n.left)
            if isinstance(n.op,ast.Pow):
                require(isinstance(n.right,ast.Constant) and n.right.value>=0,'exponent')
                return a**n.right.value
            b=go(n.right)
            if isinstance(n.op,ast.Add): return a+b
            if isinstance(n.op,ast.Sub): return a-b
            if isinstance(n.op,ast.Mult): return a*b
        raise ValueError(ast.dump(n))
    return go(ast.parse(text,mode='eval').body)


def make_packet(n,finalizer,shifted=False):
    variables=['j','C_native','z','h','r','v_scale','w3','T','c0',
               'pair_root','pair_pos1','pair_pos2','t_parity']
    if n==4: variables.insert(7,'gamma')
    kernel=norm_kernel(n)
    defs=source_definitions()
    if n==4:
        defs += [['D','b0+H*gamma'],['carrier','x_parity'],
                 ['rad0','Afirst'],['rad1','4*Bguard'],
                 ['rad2','4*F2'],['rad3','64*Caux']]
        rows=['D**2-Dmain',kernel['output']]
    else:
        if shifted:
            defs += [['Lshift','8*H*(2*Q-1)*V'],
                     ['Kshift','64*H**2*V**2+256*H**2*delta'],
                     ['Zbase','H*x_parity+b0'],
                     ['carrier','Zbase+Lshift']]
        else:
            defs += [['carrier','H*x_parity+b0']]
        defs += [['rad0','H**2*Afirst'],
                 ['rad1','Dmain'],['rad2','16*H**2*Bguard'],
                 ['rad3','16*H**2*F2'],['rad4','256*H**2*Caux']]
        rows=[kernel['output']]
    defs += kernel['polynomial_abbreviations']
    parent=(ROOT/'parent/degree88_17.json').read_bytes()
    return {
        'name': 'parity13_shifted' if shifted else ('parity14_' if n==4 else 'parity13_')+finalizer,
        'domain':'unrestricted integers',
        'variables':variables,'variable_count':len(variables),
        'fixed_numerals':['beta','K0','MC','MF','cone_A','cone_B'],
        'coefficient_binding':'coefficients/BINDING.json',
        'polynomial_abbreviations':defs,
        'factored_residuals':rows,'residual_count':len(rows),
        'finalizer':finalizer,
        'single_polynomial': ('the only listed residual' if finalizer=='direct' else
                             'sum of residual squares' if finalizer=='sos' else
                             'product(1+4*r_i for r_i in residuals)-1'),
        'norm_kernel':'norm'+str(n)+'_kernel.json',
        'norm_kernel_binary_operations':kernel['binary_operations'],
        'source_parent':'parent/degree88_17.json',
        'parent_sha256':hashlib.sha256(parent).hexdigest(),
        'new_semantic_steps':['normalized odd strong index',
                              'squared-modulus auxiliary CRT restriction',
                              'fixed-weight squareclass parity norm']+
                             (['main root congruence carried by the norm center'] if n==5 else [])+
                             (['integral midpoint shift of the auxiliary root carrier'] if shifted else []),
        'proof_status':'Ordinary universal proof relative to the explicitly identified inherited canonical native/Pell/refutation interface; not a new end-to-end kernel certificate.',
    },kernel


def main():
    ports=read_ports()
    receipt={}
    for n,finalizer,shifted in ((4,'sos',False),(4,'unit_product',False),(5,'direct',False),(5,'direct',True)):
        packet,kernel=make_packet(n,finalizer,shifted)
        slopes={v:(i+2)**2+1 for i,v in enumerate(packet['variables'])}
        env={k:Lead(0,v%PRIME) for k,v in ports.items()}
        env.update({v:Lead(1,s) for v,s in slopes.items()})
        for name,e in packet['polynomial_abbreviations']:
            env[name]=Lead.lift(calculate(e,env))
        rows=[Lead.lift(calculate(e,env)) for e in packet['factored_residuals']]
        if finalizer=='direct': out=rows[0]
        elif finalizer=='sos': out=sum((r*r for r in rows),Lead(0,0))
        else:
            out=Lead(0,1)
            for row in rows: out=out*(1+4*row)
            out=out-1
        naive_degree=out.d
        if shifted:
            require(env['Lshift'].d==59 and env['rad2'].d==56,'paired degree inputs')
            top=pow(2,16,PRIME)*pow(env['Lshift'].c,16,PRIME)*pow(env['rad2'].c,8,PRIME)%PRIME
            require(out.c==0,'expected top cancellation at the naive bound')
            out=Lead(1392,top)
            rows=[out]
        require(out.c!=0,'vanishing leading certificate')
        packet['exact_degree']=out.d
        packet['degree_certificate']={
            'method':'safe degree propagation and nonzero leading homogeneous specialization modulo a prime',
            'prime':PRIME,'slopes':slopes,'residual_degrees':[r.d for r in rows],
            'radicand_degrees':[env['rad'+str(i)].d for i in range(n)],
            'carrier_degree':env['carrier'].d,
            'final_degree':out.d,'leading_coefficient_mod_prime':out.c,
            'dominant_radicand_index':n-1,
            'dominant_radicand_leading_coefficient_mod_prime':env['rad'+str(n-1)].c,
            'norm_top_power':2**(n-1),
        }
        if shifted:
            packet['degree_certificate'].update({
                'method':'exact auxiliary-pair identity and unique leading weighted term, with authentic coefficient specialization',
                'naive_graph_degree_bound':naive_degree,
                'pair_identity':'Lshift**2-rad4=Kshift',
                'pair_factor':'(Zbase-S)**2+2*Lshift*(Zbase-S)+Kshift',
                'S':'arbitrary signed sum of square roots of rad0,rad1,rad2,rad3',
                'pair_factor_weighted_degree':87,
                'pair_factor_count':16,
                'highest_homogeneous_expression':'2**16 * leading(Lshift)**16 * leading(rad2)**8',
                'Lshift_degree':env['Lshift'].d,
                'Lshift_leading_coefficient_mod_prime':env['Lshift'].c,
                'rad2_degree':env['rad2'].d,
                'rad2_leading_coefficient_mod_prime':env['rad2'].c,
                'coordinate_bijection':'t_unshifted=t_parity+4*(2*Q-1)*V',
            })
        (ROOT/(packet['name']+'.json')).write_text(json.dumps(packet,indent=2,sort_keys=True)+'\n')
        (ROOT/('norm'+str(n)+'_kernel.json')).write_text(json.dumps(kernel,indent=2,sort_keys=True)+'\n')
        receipt[packet['name']]={'variables':packet['variable_count'],'degree':out.d,
                                'residual_degrees':[r.d for r in rows],
                                'kernel_operations':kernel['binary_operations'],
                                'leading_coefficient_mod_prime':out.c}
    (ROOT/'NORM_FAMILY_METRICS.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))


if __name__=='__main__': main()
