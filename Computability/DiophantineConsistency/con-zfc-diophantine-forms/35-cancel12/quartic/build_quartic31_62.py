#!/usr/bin/env python3
"""Exact audit of three positive-coordinate shifts of ProveIt's quartic31.

Requires only Python 3. Reads literal JSON only; no upstream code runs.
"""
import ast, collections, hashlib, json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'upstream' / 'quartic31.json'
PIN = '8c6eec9d19ef80538c8e61ff6e0180040583446a'

def require(ok, message):
    if not ok:
        raise ValueError(message)

class Ring:
    def __init__(self,names,nvars):
        self.names=names
        self.nvars=nvars
        self.zero=(0,)*len(names)
    def constant(self,n):
        return {self.zero:n} if n else {}
    def variable(self,x):
        m=list(self.zero)
        m[self.names.index(x)]=1
        return {tuple(m):1}
    def add(self,p,q,sign=1):
        out=dict(p)
        for m,c in q.items():
            out[m]=out.get(m,0)+sign*c
            if out[m]==0: del out[m]
        return out
    def mul(self,p,q):
        out={}
        for a,c in p.items():
            for b,d in q.items():
                m=tuple(x+y for x,y in zip(a,b))
                out[m]=out.get(m,0)+c*d
        return {m:c for m,c in out.items() if c}
    def parse(self,s,env):
        def walk(t):
            if isinstance(t,ast.Name): return env[t.id]
            if isinstance(t,ast.Constant) and type(t.value)==int: return self.constant(t.value)
            if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub): return {m:-c for m,c in walk(t.operand).items()}
            if isinstance(t,ast.BinOp):
                p=walk(t.left)
                if isinstance(t.op,ast.Pow):
                    require(isinstance(t.right,ast.Constant) and type(t.right.value)==int and 0<=t.right.value<=8,'Bad exponent')
                    result=self.constant(1)
                    for _ in range(t.right.value): result=self.mul(result,p)
                    return result
                q=walk(t.right)
                if isinstance(t.op,ast.Add): return self.add(p,q)
                if isinstance(t.op,ast.Sub): return self.add(p,q,-1)
                if isinstance(t.op,ast.Mult): return self.mul(p,q)
            raise ValueError(ast.dump(t))
        return walk(ast.parse(s.replace('^','**'),mode='eval').body)
    def degree(self,p): return max((sum(m[:self.nvars]) for m in p),default=-1)
    def terms(self,p): return [{'powers':list(m),'coefficient':c} for m,c in sorted(p.items())]

class Circuit:
    def __init__(self, inputs):
        self.env = {x:x for x in inputs}
        self.rows=[]
        self.cache={}
    def gate(self, op, a, b):
        if op in ('+','*') and str(a)>str(b):
            a,b=b,a
        key=(op,a,b)
        if key not in self.cache:
            name='v'+str(len(self.rows)+1)
            self.rows.append([name,op,a,b])
            self.cache[key]=name
        return self.cache[key]
    def parse(self, expression):
        def go(t):
            if isinstance(t, ast.Name):
                return self.env[t.id]
            if isinstance(t, ast.Constant) and type(t.value)==int:
                return t.value
            if isinstance(t, ast.BinOp):
                a=go(t.left)
                if isinstance(t.op, ast.Pow):
                    require(isinstance(t.right,ast.Constant) and t.right.value==2,'Only squares allowed')
                    return self.gate('*',a,a)
                return self.gate({ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(t.op)],a,go(t.right))
            raise ValueError(ast.dump(t))
        return go(ast.parse(expression,mode='eval').body)
    def assign(self, name, expression):
        self.env[name]=self.parse(expression)

def main():
    old=json.loads(SOURCE.read_text())
    variables=[{'L':'S','P':'T'}.get(x,x) for x in old['variables']]
    coefficients=old['constants']
    ring=Ring(variables+coefficients,len(variables))
    symbols={x:ring.variable(x) for x in variables+coefficients}
    aliases={'q':'beta*J+1','k':'eta+zeta','H':'4*a+3','C':'q-F-alpha'}
    env=dict(symbols)
    for name, expression in aliases.items():
        env[name]=ring.parse(expression,env)
    pairs=[
        ('S','q*q'),
        ('N','q*S'),
        ('X','w*q'),
        ('a','E+s*N'),
        ('E','X*(a-E)'),
        ('c','k*(a-E)+eta'),
        ('T','E*(c-eta)'),
        ('tau*tau','T*(T+k)+1'),
        ('D','X+a*c+gamma*H'),
        ('Delta','a*a+H'),
        ('C2','c*c'),
        ('D*D','Delta*C2+1'),
        ('k','j*c-V+1+h*E'),
        ('j*c-V','(q-F)*(N-q)-C*(S-1)+(MC+q*MF)*J'),
        ('(K0+w)*C','F+z*(q-1)'),
        ('F2','f*f'),
        ('V','o*f-c'),
        ('g','y*y-V*V'),
        ('I','i*C2'),
        ('Baux','I*I'),
        ('Baux','Delta*(F2-1)'),
        ('y*y-Baux*g','1'),
    ]
    residuals=[ring.add(ring.parse(a,env),ring.parse(b,env),-1) for a,b in pairs]
    require(len(variables)==31 and len(residuals)==22,'Dimension mismatch')
    old_env=dict(symbols)
    old_env['L']=ring.parse('S-1',env)
    old_env['P']=ring.parse('T+k',env)
    old_env['z']=ring.parse('z+1',env)
    for name, expression in old['affine_abbreviations'].items():
        old_env[name]=ring.parse(expression,old_env)
    exact=[]
    for row,new in zip(old['equations'],residuals):
        predecessor=ring.parse(row['residual'],old_env)
        require(predecessor==new,'Transformed predecessor residual mismatch '+str(row['number']))
        from_terms={}
        for term in row['terms']:
            p=ring.constant(term['coefficient'])
            for name,power in zip(old['variables']+coefficients,term['powers']):
                for _ in range(power):
                    p=ring.mul(p,old_env[name])
            from_terms=ring.add(from_terms,p)
        require(from_terms==new,'Transformed predecessor sparse terms mismatch '+str(row['number']))
        exact.append(True)
    degrees=[ring.degree(r) for r in residuals]
    require(degrees==[2]*22,'Not all residuals are quadratic')
    output={}
    for r in residuals: output=ring.add(output,ring.mul(r,r))
    require(ring.degree(output)==4,'Quartic degree fails')
    mon=[0]*len(ring.names)
    mon[variables.index('tau')]=4
    require(output.get(tuple(mon))==1,'tau^4 coefficient fails')
    normalization={}
    for m,c0 in residuals[4].items():
        powers=(0,)*31+m[31:]
        normalization[powers]=normalization.get(powers,0)+c0
    require({m:c0 for m,c0 in normalization.items() if c0}==ring.constant(1),'Nonnegative normalization fails')
    c=Circuit(variables+coefficients)
    c.assign('rep','beta*J')
    for name, expression in aliases.items():
        c.assign(name,expression)
    # Use rep=q-1 directly; forming q-1 would be an avoidable extra gate.
    circuit_pairs=[(a,b.replace('z*(q-1)','z*rep')) for a,b in pairs]
    comparisons=[[c.parse(a),c.parse(b)] for a,b in circuit_pairs]
    source=list(c.rows)
    require(len(source)==62,'Unexpected equality-evaluator count: '+str(len(source)))
    values={x:symbols[x] for x in variables+coefficients}
    def val(x):
        return ring.constant(x) if type(x)==int else values[x]
    for name,op,a,b in source:
        values[name]=ring.mul(val(a),val(b)) if op=='*' else ring.add(val(a),val(b),-1 if op=='-' else 1)
    for (a,b),r in zip(comparisons,residuals):
        require(ring.add(val(a),val(b),-1)==r,'Circuit does not match equation')
    live=set(x for pair in comparisons for x in pair)
    for name,op,a,b in reversed(source):
        if name in live:
            live.update([a,b])
    require(all(row[0] in live for row in source),'Dead circuit gate')
    require(all(x in live for x in variables+coefficients),'Dead input')
    counter=collections.Counter(row[1] for row in source)
    residual_outputs=[c.gate('-',a,b) for a,b in comparisons]
    squares=[c.gate('*',a,a) for a in residual_outputs]
    final=squares[0]
    for sq in squares[1:]:
        final=c.gate('+',final,sq)
    require(len(c.rows)==127,'Unexpected SOS evaluator count')
    terms=ring.terms(output)
    packet={'name':'quartic31_shifted62','repository_pin':PIN,'witness_domain':'strictly positive integers','witnesses':variables,'fixed_numerals':coefficients,'coefficient_binding':{'manifest':'../coefficients/COEFFICIENT_BINDING.json','port_files':{'beta':'../coefficients/beta.bin','K0':'../coefficients/K.bin','MC':'../coefficients/MC.bin','MF':'../coefficients/MF_source.bin'},'encoding':'unsigned little-endian integer','requirement':'Use this complete tuple together; MF is the shifted source mask.'},'affine_abbreviations':aliases,'equations':[{'number':i+1,'left':a,'right':b,'terms':ring.terms(residuals[i]),'degree':degrees[i]} for i,(a,b) in enumerate(pairs)],'source':source,'comparisons':comparisons,'operations':len(source),'multiplications':counter['*'],'additions_subtractions':counter['+']+counter['-'],'exact_maximum_residual_degree':2,'changes':{'L_old':'S-1','P_old':'T+eta+zeta','z_old':'z+1'},'formal_status':'Ordinary mathematics plus exact symbolic audits; no new Lean/Rocq theorem.'}
    (HERE/'quartic31_system62.json').write_text(json.dumps(packet,indent=2)+'\n')
    sos={k:packet[k] for k in ('name','repository_pin','witness_domain','witnesses','fixed_numerals','coefficient_binding','formal_status')}
    sos.update(name='quartic31_shifted_sos127',source=c.rows,output=final,operations=len(c.rows),exact_degree=4,terms=terms,sparse_term_coordinate_order=variables+coefficients)
    (HERE/'quartic31_sos127.json').write_text(json.dumps(sos,indent=2)+'\n')
    audit={'status':'PASS','pin':PIN,'source_file':SOURCE.name,'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'unknowns':31,'equations':22,'degrees':degrees,'system_operations':len(source),'system_multiplications':counter['*'],'system_additions_subtractions':counter['+']+counter['-'],'sos_operations':len(c.rows),'sos_degree':4,'sos_terms_with_ports_symbolic':len(terms),'all_22_transformed_predecessor_residuals_and_sparse_terms_equal_symbolically':all(exact),'all_circuit_outputs_equal_residuals_symbolically':True,'all_gates_and_inputs_live':True,'tau4_coefficient':1,'normalization_residual_5_at_all_ones':1,'positivity_boundary':'S and T shifts are elementary. The z shift imports the established retained59 source lemma that old z >= 2 at every positive source zero.'}
    (HERE/'QUARTIC31_62_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
    print(json.dumps(audit,indent=2))

if __name__=='__main__':
    main()
