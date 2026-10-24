#!/usr/bin/env python3
"""Independent finite checks for the literal equation packets.

Uses SymPy only for a few exact ring identities. Degree certificates use a
separate sparse homogeneous-component engine and the actual fixed ports are
authenticated as integer bytes. The unbounded semantic proof is in PROOF.md.
"""
from pathlib import Path
import ast, gzip, hashlib, json, random, sys
sys.path.insert(0,str(Path(__file__).resolve().parent/'.runtime'))
import sympy as sp

sys.setrecursionlimit(20000)
ROOT = Path(__file__).resolve().parent

def need(ok, why):
    if not ok:
        raise ValueError(why)

def read(path): return json.loads(path.read_text())
def save(path, x): path.write_text(json.dumps(x,indent=2)+'\n')

def node(expression):
    n=ast.parse(expression,mode='eval').body
    for x in ast.walk(n):
        need(isinstance(x,(ast.Expression,ast.Name,ast.Load,ast.Constant,ast.BinOp,
                           ast.UnaryOp,ast.USub,ast.Add,ast.Sub,ast.Mult,ast.Pow)), 'restricted polynomial syntax')
        if isinstance(x,ast.Constant): need(type(x.value) is int,'integer literal')
        if isinstance(x,ast.BinOp) and isinstance(x.op,ast.Pow):
            need(isinstance(x.right,ast.Constant) and type(x.right.value) is int and 0<=x.right.value<=256,
                 'ordinary fixed exponent')
    return n

def evaluate(n, env, definitions=None, modulus=None):
    definitions=definitions or {}
    cache={}
    def f(x):
        if isinstance(x,ast.Name):
            if x.id in env:return env[x.id]
            need(x.id in definitions,'declared leaf '+x.id)
            if x.id not in cache:cache[x.id]=f(node(definitions[x.id]))
            return cache[x.id]
        if isinstance(x,ast.Constant):return x.value
        if isinstance(x,ast.UnaryOp):return -f(x.operand)
        a=f(x.left)
        if isinstance(x.op,ast.Pow):v=a**x.right.value
        else:
            b=f(x.right)
            if isinstance(x.op,ast.Add):v=a+b
            elif isinstance(x.op,ast.Sub):v=a-b
            else:v=a*b
        return v%modulus if modulus else v
    return f(n)

def sym(expression,env=None,definitions=None):
    env=env or {}
    names={x.id for x in ast.walk(node(expression)) if isinstance(x,ast.Name)}
    if definitions:
        names.update(y.id for e in definitions.values() for y in ast.walk(node(e)) if isinstance(y,ast.Name))
    atoms={n:env.get(n,sp.Symbol(n)) for n in names if not definitions or n not in definitions}
    return evaluate(node(expression),atoms,definitions)

class Leading:
    """Upper witness degree and its exact homogeneous component over Z[ports]."""
    def __init__(self,names,witnesses):
        self.names=sorted(names);self.index={n:i for i,n in enumerate(self.names)}
        self.witnesses=set(witnesses);self.zero=(0,)*len(self.names)
        self.memo={}
    def add(self,a,b,sgn=1):
        r=dict(a)
        for e,c in b.items():
            r[e]=r.get(e,0)+sgn*c
            if not r[e]:del r[e]
        return r
    def mul(self,a,b):
        r={}
        for e,c in a.items():
            for f,d in b.items():
                g=tuple(x+y for x,y in zip(e,f))
                r[g]=r.get(g,0)+c*d
        return {e:c for e,c in r.items() if c}
    def power(self,a,n):
        r={self.zero:1}
        while n:
            if n&1:r=self.mul(r,a)
            n//=2
            if n:a=self.mul(a,a)
        return r
    def get(self,n):
        key=ast.dump(n)
        if key in self.memo:return self.memo[key]
        if isinstance(n,ast.Constant):r=(0,{self.zero:n.value} if n.value else {})
        elif isinstance(n,ast.Name):
            e=list(self.zero);e[self.index[n.id]]=1
            r=(int(n.id in self.witnesses),{tuple(e):1})
        elif isinstance(n,ast.UnaryOp):
            d,p=self.get(n.operand);r=(d,{e:-c for e,c in p.items()})
        else:
            da,a=self.get(n.left)
            if isinstance(n.op,ast.Pow):r=(da*n.right.value,self.power(a,n.right.value))
            else:
                db,b=self.get(n.right)
                if isinstance(n.op,ast.Mult):r=(da+db,self.mul(a,b))
                else:
                    sg=-1 if isinstance(n.op,ast.Sub) else 1
                    if da>db:r=(da,a)
                    elif db>da:r=(db,{e:sg*c for e,c in b.items()})
                    else:r=(da,self.add(a,b,sg))
        self.memo[key]=r
        return r
    def whole(self,n):
        if isinstance(n,ast.Constant):return {self.zero:n.value} if n.value else {}
        if isinstance(n,ast.Name):
            e=list(self.zero);e[self.index[n.id]]=1;return {tuple(e):1}
        if isinstance(n,ast.UnaryOp):return {e:-c for e,c in self.whole(n.operand).items()}
        a=self.whole(n.left)
        if isinstance(n.op,ast.Pow):return self.power(a,n.right.value)
        b=self.whole(n.right)
        if isinstance(n.op,ast.Mult):return self.mul(a,b)
        return self.add(a,b,-1 if isinstance(n.op,ast.Sub) else 1)

def main():
    pins=read(ROOT/'SOURCE_PINS.json')
    for item in pins['files']:
        need(hashlib.sha256((ROOT/item['stored_path']).read_bytes()).hexdigest()==item['sha256'],
             'source authentication '+item['stored_path'])

    # Preserve the identities of exactly the six fixed numerals used here.
    inherited=read(ROOT/'upstream/guards__COEFFICIENT_BINDING.json')
    ports=['beta','K0','MC','MF','cone_A','cone_B'];values={};records={}
    for p in ports:
        data=(ROOT/'coefficients'/(p+'.bin.gz')).read_bytes();raw=gzip.decompress(data)
        info=inherited['payloads'][p]
        need(hashlib.sha256(raw).hexdigest()==info['raw_sha256'],'actual numeral '+p)
        need(hashlib.sha256(data).hexdigest()==info['gzip_sha256'],'compressed numeral '+p)
        values[p]=int.from_bytes(raw,'little')
        need(values[p].bit_length()==info['bits'] and len(raw)==info['raw_bytes'],'numeral length '+p)
        records[p]=dict(info,path=p+'.bin.gz')
    need(values['beta']==(1<<1064921)-1,'exact radix')
    need(values['cone_A']==1<<1113 and values['cone_B']==1<<666104,'exact determinant scales')
    binding={'backend':inherited['backend'],'format':'gzip of minimal unsigned little-endian integer bytes',
             'MF_convention':'already shifted by beta','payloads':records,
             'total_raw_bytes':sum(v['raw_bytes'] for v in records.values()),
             'total_compressed_bytes':sum((ROOT/'coefficients'/(p+'.bin.gz')).stat().st_size for p in ports),
             'source':'../upstream/guards__COEFFICIENT_BINDING.json'}
    save(ROOT/'coefficients/BINDING.json',binding)

    packets=[read(p) for p in sorted((ROOT/'forms').glob('*.json')) if not p.name.endswith('_dag.json')]
    results=[]
    for packet in packets:
        variables=packet['variables']; names=set(variables+ports)
        need(len(variables)==len(set(variables))==packet['variable_count'],'unique coordinate list')
        rows=packet['residuals'];need(len(rows)==packet['residual_count'],'row count')
        occurring={n.id for e in rows for n in ast.walk(node(e)) if isinstance(n,ast.Name)}
        need(occurring<=names,'no hidden variables')
        need(set(variables)<=occurring,'all coordinates live')
        lead=Leading(names,variables)
        components=[lead.get(node(e)) for e in rows]
        if packet['name']=='center18_degree80':
            dS=max(2*d for d,p in components[:-1]);S={}
            for d,p in components[:-1]:
                if 2*d==dS:S=lead.add(S,lead.mul(p,p))
            dG,G=components[-1];degree=dS+dG;top=lead.mul(S,G)
        else:
            degree=max(2*d for d,p in components);top={}
            for d,p in components:
                if 2*d==degree:top=lead.add(top,lead.mul(p,p))
        need(degree==packet['exact_degree'],'degree bound '+packet['name'])
        witness=packet['degree_witness'];mon=lead.whole(node(witness['monomial']))
        need(len(mon)==1 and list(mon.values())==[1],'single certificate monomial')
        target=next(iter(mon));coeff={}
        for e,c in top.items():
            if all(e[lead.index[v]]==target[lead.index[v]] for v in variables):
                f=list(e)
                for v in variables:f[lead.index[v]]=0
                coeff[tuple(f)]=c
        expected=lead.whole(node(witness.get('coefficient_expression',str(witness.get('coefficient')))))
        need(coeff==expected and bool(coeff),'exact nonzero leading coefficient '+packet['name'])
        results.append({'name':packet['name'],'variables':len(variables),'rows':len(rows),
                        'residual_degree_bounds':[d for d,p in components],
                        'exact_degree':degree,'leading_component_terms':len(top),
                        'degree_certificate':'PASS'})

    # Exact abstract ring identities; their substitution instances are universal.
    q,W,C,z,F,alpha=sp.symbols('q W C z F alpha');K0=sp.Symbol('K0')
    Fnew=(K0+W)*C-z*(q-1);anew=q-Fnew-C
    need(sp.expand((K0+W)*(q-Fnew-anew)-Fnew-z*(q-1))==0,'transport restoration')
    need(sp.expand(((q-1)*(q-Fnew)+anew)-(q*(q-Fnew)-C))==0,'packing identity')
    u,k,t,tau,I,s,B,delta,Q,A,nn=sp.symbols('u k t tau I s B delta Q A nn')
    midpoint=t*t+2*(2*u+k)*t+k*k-4
    need(sp.expand(midpoint.subs(t,2*tau-2*u-k)-4*(tau*tau-u*(u+k)-1))==0,'midpoint identity')
    center=nn*nn+2*I*(2*u+k)*nn+I*I*(k*k-4)
    raw=I*(2*u+k)+nn
    need(sp.expand(center-(raw*raw-4*I*I*(u*(u+k)+1)))==0,'centered norm identity')
    V0=sp.Symbol('V')
    A0=u*(u+k)+1;Q0=I*I;dd=Q0-1;bb=Q0*V0*V0-1
    jtail=dd*(center+4*V0*nn)-4*(V0*V0-1)
    htail=4*dd*I*(2*u+k)*V0
    n110=jtail*jtail+2*jtail*htail+64*dd*Q0*A0*(1-V0*V0)+16*dd*dd*Q0*(k*k-4)*V0*V0
    n112=(dd*center-4*bb)**2-64*dd*Q0*A0*bb
    need(sp.expand(n110-n112.subs(nn,nn+2*V0))==0,'double centering exact shear')
    generic=(delta*(4*s*s-4*Q*A)-4*B)**2-64*delta*Q*A*B
    target=16*((delta*(s*s-Q*A)-B)**2-4*delta*Q*A*B)
    need(sp.expand(generic-target)==0,'two-root norm factor 16')
    need(sp.expand(generic.subs({B:delta*sp.Symbol('y')**2,s:sp.Symbol('x')+sp.Symbol('y'),Q*A:sp.Symbol('x')**2}))==0,
         'two-root norm vanishes on genuine sums')
    # Deliberate coefficient corruption must be detected by the same identity.
    corrupted=(delta*(4*s*s-4*Q*A)-4*B)**2-63*delta*Q*A*B
    need(sp.expand(corrupted-target)!=0,'negative control: changed norm coefficient rejected')
    # Equal nonsquare radicands defeat an unscaled sum. The existing I factor
    # removes this branch arithmetically, without a new inequality witness.
    Q0,V0,A0,delta0,B0=4,2,5,3,15
    unscaled=(delta0*(0-A0)-B0)**2-4*delta0*A0*B0
    scaled=(delta0*(0-Q0*A0)-B0)**2-4*delta0*Q0*A0*B0
    need(unscaled==0 and scaled==2025,'unscaled equal-nonsquare negative control')

    # Literal byte-pinned parent restoration checks for all four projections.
    import copy
    class Restore(ast.NodeTransformer):
        def __init__(self,replacements):self.replacements=replacements
        def visit_Name(self,n):
            return node(self.replacements[n.id]) if n.id in self.replacements else n
    pivot_rows=0
    for packet in packets:
        if not packet['name'].startswith('pivot'):continue
        parent=read(ROOT/packet['parent']);deleted=packet['deleted_parent_row_zero_based']
        restored=[ast.dump(Restore(packet['parent_restoration']).visit(node(e)),include_attributes=False)
                  for i,e in enumerate(parent['residuals']) if i!=deleted]
        need(restored==[ast.dump(node(e),include_attributes=False) for e in packet['residuals']],
             'literal projection rows '+packet['name'])
        need(sp.expand(sym(parent['residuals'][deleted],env={p:sym(e) for p,e in packet['parent_restoration'].items()}))==0,
             'deleted literal transport row '+packet['name'])
        pivot_rows+=len(restored)

    # The four compact rows retained by the merger are exact source rows.
    compact=read(ROOT/'certificates/COMPACT_BASE18.json')
    base=read(ROOT/'forms/pivot18_degree88.json')
    for i in [1,2,3,5]:
        left=sym(base['residuals'][i]);right=sym(compact['rows'][i],definitions=compact['definitions'])
        # Usually SymPy's canonical expression construction already cancels all
        # shared large terms. Only the small packing identity needs expansion.
        difference=left-right
        need(difference==0 or sp.expand(difference)==0,'literal retained row '+str(i))
    # First Pell and auxiliary rows also agree exactly with the stated interface.
    for i in [0,4]:
        need(sp.expand(sym(base['residuals'][i])-sym(compact['rows'][i],definitions=compact['definitions']))==0,
             'literal root interface '+str(i))

    # Modular diagnostics bind every displayed compact equation to its fully
    # inlined packet, with authentic (not toy) fixed coefficients.
    rng=random.Random(20261023);moduli=[1000000007,1000000009,998244353]
    modular=0
    for packet in packets:
        if 'compact_residuals' not in packet:continue
        for modulus in moduli:
            for _ in range(12):
                env={p:v%modulus for p,v in values.items()}
                env.update({v:rng.randrange(-1000,1001)%modulus for v in packet['variables']})
                got=[evaluate(node(r),env,modulus=modulus) for r in packet['residuals']]
                expected=[evaluate(node(r),env,packet['definitions'],modulus) for r in packet['compact_residuals']]
                need(got==expected,'display/packet modular equality')
                modular+=len(got)
    circuit_records=[]
    for path in sorted((ROOT/'forms').glob('*_dag.json')):
        dag=read(path);packet=next(p for p in packets if p['name']==dag['name'])
        need(len(dag['nodes'])==dag['operation_count'],'literal DAG count')
        table={n['id']:n for n in dag['fixed_recipes']+dag['nodes']}
        need(len(table)==len(dag['fixed_recipes'])+len(dag['nodes']),'unique DAG IDs')
        live=set()
        def visit(key):
            if key in live:return
            live.add(key)
            if key in table:visit(table[key]['left']);visit(table[key]['right'])
        visit(dag['output'])
        need(set(table)<=live,'all emitted gates live')
        diagnostics=0
        for modulus in moduli:
            for _ in range(12):
                env={p:v%modulus for p,v in values.items()}
                env.update({v:rng.randrange(-1000,1001)%modulus for v in packet['variables']})
                regs={'v:'+v:env[v] for v in packet['variables']}
                regs.update({'c:'+p:env[p] for p in ports})
                def val(key):return int(key[2:])%modulus if key.startswith('n:') else regs[key]
                for gate in dag['fixed_recipes']+dag['nodes']:
                    a0,b0=val(gate['left']),val(gate['right'])
                    regs[gate['id']]=(a0+b0 if gate['op']=='add' else a0-b0 if gate['op']=='sub' else a0*b0)%modulus
                rr=[evaluate(node(e),env,modulus=modulus) for e in packet['residuals']]
                if packet['name']=='center18_degree80':
                    SS=sum(x*x for x in rr[:-1]);GG=rr[-1];expected=(GG+SS+GG*SS)%modulus
                else:expected=sum(x*x for x in rr)%modulus
                need(regs[dag['output']]==expected,'DAG versus polynomial')
                need([val(x) for x in dag['residual_outputs']]==rr,'every DAG residual')
                diagnostics+=1
        circuit_records.append({'name':dag['name'],'operations':dag['operation_count'],
                                'operation_histogram':dag['operation_histogram'],
                                'modular_diagnostics':diagnostics,'topology_liveness':'PASS'})
    # Rational norm and midpoint controls, independent of any ZFC refutation.
    controls=0
    from fractions import Fraction
    for u0 in range(-4,5):
        for k0 in range(-4,5):
            for tau0 in range(-4,5):
                t0=2*tau0-2*u0-k0
                need(t0*t0+2*(2*u0+k0)*t0+k0*k0-4==4*(tau0*tau0-u0*(u0+k0)-1),'midpoint signed control')
                controls+=1
    report={'status':'PASS','packets':results,'fixed_numerals':binding,
            'exact_identities':'transport, packing, midpoint, centered two-root norm, retained source rows',
            'modular_row_diagnostics':modular,'signed_midpoint_controls':controls,
            'literal_pivot_row_identities':pivot_rows,'circuits':circuit_records,
            'negative_controls':['changed norm coefficient 64 to 63 rejected',
              'unscaled equal-nonsquare roots I=2,V=2,A=5 falsely allow sum 0; scaled norm rejects it'],
            'proof_boundary':'Finite identities/bytes/degrees only; PROOF.md supplies the unbounded new semantic proof and names inherited dependencies.'}
    save(ROOT/'certificates'/('VERIFY_OPTIMIZED.json' if not __debug__ else 'VERIFY.json'),report)
    print(json.dumps({'status':'PASS','packets':results,'modular_row_diagnostics':modular},indent=2))

if __name__=='__main__':main()
