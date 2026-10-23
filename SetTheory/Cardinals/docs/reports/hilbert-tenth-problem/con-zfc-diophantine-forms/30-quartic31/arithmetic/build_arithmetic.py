if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
#!/usr/bin/env python3
"""New-owned exact arithmetic audits; never imports or executes upstream code."""
import ast, collections, hashlib, json, random
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PIN='ae3007ca4467011e0e051c84acb4a1dd13971b0e'
def require(c,m):
    if not c: raise ValueError(m)
def save(name,p): (ROOT/name).write_text(json.dumps(p,indent=2)+'\n')
class Ring:
    def __init__(self,names,nvars): self.names=names; self.nvars=nvars; self.zero=(0,)*len(names)
    def const(self,n): return {self.zero:n} if n else {}
    def var(self,n):
        a=list(self.zero);a[self.names.index(n)]=1;return {tuple(a):1}
    def add(self,p,q,sign=1):
        r=dict(p)
        for m,c in q.items():
            r[m]=r.get(m,0)+sign*c
            if not r[m]:del r[m]
        return r
    def mul(self,p,q):
        r={}
        for a,c in p.items():
            for b,d in q.items():
                k=tuple(x+y for x,y in zip(a,b));r[k]=r.get(k,0)+c*d
        return {k:v for k,v in r.items() if v}
    def parse(self,s,env=None):
        env=env or {}
        def walk(t):
            if isinstance(t,ast.Name):return env[t.id] if t.id in env else self.var(t.id)
            if isinstance(t,ast.Constant) and type(t.value)==int:return self.const(t.value)
            if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return {m:-v for m,v in walk(t.operand).items()}
            if isinstance(t,ast.BinOp):
                p=walk(t.left)
                if isinstance(t.op,ast.Pow):
                    require(isinstance(t.right,ast.Constant) and 0<=t.right.value<=8,'bad power')
                    r=self.const(1)
                    for _ in range(t.right.value):r=self.mul(r,p)
                    return r
                q=walk(t.right)
                if isinstance(t.op,ast.Add):return self.add(p,q)
                if isinstance(t.op,ast.Sub):return self.add(p,q,-1)
                if isinstance(t.op,ast.Mult):return self.mul(p,q)
            raise ValueError(ast.dump(t))
        return walk(ast.parse(s.replace('^','**'),mode='eval').body)
    def degree(self,p):return max((sum(m[:self.nvars]) for m in p),default=-1)
    def terms(self,p):return [{'powers':list(k),'coefficient':v} for k,v in sorted(p.items())]
    def evaluate(self,p,vals):
        out=0
        for m,c in p.items():
            for k,x in zip(m,vals):c*=x**k
            out+=c
        return out
source=ROOT/'upstream/quartic32.pinned.json'
old=json.loads(source.read_text()); variables=[x for x in old['variables'] if x!='G']; constants=old['constants']
ring=Ring(variables+constants,len(variables));env={}
for n,s in old['affine_abbreviations'].items():env[n]=ring.parse(s,env)
newres='j*c-V-((q-F)*(N-q)-C*L+(MC+q*MF)*J)'
packing=ring.parse(newres,env)
new=[]
for e in old['equations']:
    if e['number']==14:continue
    e=dict(e)
    if e['number']==15:
        e['equation']='jc-V = (q-F)(N-q)-CL+(MC+q MF)J';e['residual']=newres
        p=packing
    else:
        p=ring.parse(e['residual'])
        for t in e['terms']:
            require(t['powers'][old['variables'].index('G')]==0,'unexpected G dependency')
        reduced={tuple(v for i,v in enumerate(t['powers']) if i!=old['variables'].index('G')):t['coefficient'] for t in e['terms']}
        require(p==reduced,'source residual differs from terms')
    e['old_number']=e['number'];e['number']=len(new)+1;e['terms']=ring.terms(p);e['degree']=ring.degree(p);new.append(e)
require(len(variables)==31 and len(new)==22,'wrong dimension')
require(all(e['degree']==2 for e in new),'not quadratic')
# The packing rewrite difference is a multiple of the retained N equation.
# GL - [(q-F)(N-q)-CL] = (q-F)[q(L+1)-N].
identity=ring.parse('(q*(q-F)-C)*L-((q-F)*(N-q)-C*L)-(q-F)*(q*(L+1)-N)',env)
require(not identity,'packing identity failed')
# Exact SOS expansion, retaining all fixed compiler ports as independent symbols.
sos={}
for e in new:
    p={tuple(t['powers']):t['coefficient'] for t in e['terms']};sos=ring.add(sos,ring.mul(p,p))
require(ring.degree(sos)==4,'not exact quartic')
mon=[0]*len(ring.names);mon[variables.index('tau')]=4
require(sos.get(tuple(mon))==1,'tau4 certificate failed')
require(ring.evaluate({tuple(t['powers']):t['coefficient'] for t in new[4]['terms']},[1]*len(ring.names))==1,'normalization certificate failed')
packet={k:old[k] for k in ['constants','constant_recipe','coefficient_binding','affine_abbreviations','formal_status']}
packet.update(name='quartic31_packing_elimination',source_commit=PIN,domain='strictly positive integers',variables=variables,sparse_term_coordinate_order=variables+constants,equations=new,single_polynomial='sum(r_j^2 for the 22 displayed residuals)',quartic_degree_certificate={'degree':4,'monomial':'tau^4','coefficient':1},normalization_to_nonnegative={'rule':'replace each witness x with n_x+1','degree':4,'nonzero_constant_certificate':'The fifth residual is 1 at all witness inputs 1, independently of fixed ports, so the shifted sum of squares is positive at zero.'},new_reduction='Delete G and its equation; rewrite GL=(q-F)(N-q)-CL using N=q(L+1). All other source equations and old transport coordinate are unchanged.')
save('quartic31.json',packet)
save('quartic31_expanded.json',{'variables':variables,'constants':constants,'degree':4,'terms':ring.terms(sos)})
# Fully charged CSE schedule for a readable factored form of all 22 residuals.
class Circuit:
    def __init__(self,inputs):self.source=[];self.cache={};self.env={x:x for x in inputs}
    def gate(self,op,a,b):
        if op in ['+','*'] and str(a)>str(b):a,b=b,a
        key=(op,a,b)
        if key not in self.cache:
            n='g'+str(len(self.source)+1);self.source.append([n,op,a,b]);self.cache[key]=n
        return self.cache[key]
    def parse(self,s):
        def f(t):
            if isinstance(t,ast.Name):return self.env[t.id]
            if isinstance(t,ast.Constant):return t.value
            if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return self.gate('-',0,f(t.operand))
            if isinstance(t,ast.BinOp):
                a=f(t.left)
                if isinstance(t.op,ast.Pow):
                    require(t.right.value==2,'power must be square');return self.gate('*',a,a)
                b=f(t.right);return self.gate({ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(t.op)],a,b)
            raise ValueError(ast.dump(t))
        return f(ast.parse(s,mode='eval').body)
    def assign(self,n,s):self.env[n]=self.parse(s);return self.env[n]
    def ledger(self,outputs):
        live=set(outputs)
        for n,op,a,b in reversed(self.source):
            if n in live:live.update([a,b])
        require(all(n in live for n,*_ in self.source),'dead arithmetic')
        count=collections.Counter(r[1] for r in self.source)
        return {'operations':len(self.source),'multiplications':count['*'],'additions_subtractions':count['+']+count['-'],'all_gates_live':True,'all_inputs_live':all(x in live for x in variables+constants)}
c=Circuit(variables+constants)
for n,s in old['affine_abbreviations'].items():c.assign(n,s)
exprs=['L-(q*q-1)','N-q*(L+1)','X-w*q','a-E-s*N','E-X*(a-E)','c-k*(a-E)-eta','P-E*(c-eta)-k','tau*tau-P*(P-k)-1','D-X-a*c-gamma*H','Delta-a*a-H','C2-c*c','D*D-Delta*C2-1','k-j*c+V-1-h*E',newres,'(K0+w)*C+(q-F)-z*(q-1)-1','F2-f*f','V-o*f+c','g-y*y+V*V','I-i*C2','Baux-I*I','Baux-Delta*(F2-1)','y*y-Baux*g-1']
outputs=[c.parse(s) for s in exprs]
# Confirm circuit semantics symbolically, not only random evaluation.
envp={x:ring.var(x) for x in ring.names}
for n,op,a,b in c.source:
    x=ring.const(a) if isinstance(a,int) else envp[a];y=ring.const(b) if isinstance(b,int) else envp[b]
    envp[n]=ring.mul(x,y) if op=='*' else ring.add(x,y,-1 if op=='-' else 1)
for out,e in zip(outputs,new):require(envp[out]=={tuple(t['powers']):t['coefficient'] for t in e['terms']},'factored circuit mismatch')
sysledger=c.ledger(outputs)
sys_source=list(c.source)
qs=[c.gate('*',x,x) for x in outputs];out=qs[0]
for q in qs[1:]:out=c.gate('+',out,q)
polyledger=c.ledger([out])
save('quartic31_circuit.json',{'variables':variables,'constants':constants,'source':c.source,'output':out,'exact_degree':4,'ledger':polyledger,'system_source':sys_source,'system_outputs':outputs,'system_output_meaning':'Each output equals zero. Residual calculation is charged; comparisons are free.','system_ledger':sysledger})
# Equality-comparison circuit uses the same source convention as the 59-gate system.
d=Circuit(variables+constants)
d.assign('rep','beta*J')
for n,s in old['affine_abbreviations'].items():d.assign(n,s)
pairs=[('L','q*q-1'),('N','q*(L+1)'),('X','w*q'),('a','E+s*N'),('E','X*(a-E)'),('c','k*(a-E)+eta'),('P','E*(c-eta)+k'),('tau*tau','P*(P-k)+1'),('D','X+a*c+gamma*H'),('Delta','a*a+H'),('C2','c*c'),('D*D','Delta*C2+1'),('k','j*c-V+1+h*E'),('j*c-V','(q-F)*(N-q)-C*L+(MC+q*MF)*J'),('(K0+w)*C+(q-F)-z*rep','1'),('F2','f*f'),('V','o*f-c'),('g','y*y-V*V'),('I','i*C2'),('Baux','I*I'),('Baux','Delta*(F2-1)'),('y*y-Baux*g','1')]
cmp=[[d.parse(a),d.parse(b)] for a,b in pairs]
compareledger=d.ledger([x for p in cmp for x in p])
de={x:ring.var(x) for x in ring.names}
for n,op,a,b in d.source:
    x=ring.const(a) if isinstance(a,int) else de[a];y=ring.const(b) if isinstance(b,int) else de[b]
    de[n]=ring.mul(x,y) if op=='*' else ring.add(x,y,-1 if op=='-' else 1)
for pair,e in zip(cmp,new):
    a,b=pair;x=ring.const(a) if isinstance(a,int) else de[a];y=ring.const(b) if isinstance(b,int) else de[b]
    require(ring.add(x,y,-1)=={tuple(t['powers']):t['coefficient'] for t in e['terms']},'comparison circuit mismatch')
save('quartic31_system.json',{'variables':variables,'constants':constants,'source':d.source,'comparisons':cmp,'exact_maximum_degree':2,'ledger':compareledger,'counting_convention':'Binary additions, subtractions and multiplications including constant arithmetic are charged; comparisons are free; no source operation is executed as code.'})
# Final SOS is built from the smaller comparison schedule, including all 65 finalizer gates.
dbase=list(d.source);rout=[d.gate('-',a,b) for a,b in cmp];squares=[d.gate('*',x,x) for x in rout];polyout=squares[0]
for sq in squares[1:]:polyout=d.gate('+',polyout,sq)
better_polyledger=d.ledger([polyout])
save('quartic31_circuit.json',{'variables':variables,'constants':constants,'source':d.source,'output':polyout,'exact_degree':4,'ledger':better_polyledger,'system_source':dbase,'comparisons':cmp,'system_ledger':compareledger})
# Random signed checks of the exact identity, independent direct arithmetic.
rng=random.Random(310022)
for _ in range(1000):
    q,F,alpha,L=[rng.randrange(-1000,1001) for _ in range(4)];N=q*(L+1);C=q-F-alpha;G=(q-1)*(q-F)+alpha
    require(G*L==(q-F)*(N-q)-C*L,'integer identity failed')
# Retained16 positive auxiliary-gap circuit, copied only as literal data.
rpath=ROOT/'upstream/retained16_system59.pinned.json';ret=json.loads(rpath.read_text())
rs=[]
for row in ret['source']:
    if row[0]=='y2':continue
    if row[0]=='V':
        rs.append(row);rs.append(['yrestored','+','V','e']);rs.append(['y2','*','yrestored','yrestored'])
    else:rs.append(row)
require(len(rs)==60,'gap count wrong')
retvars=['e' if x=='y' else x for x in ret['witnesses']]
rr=Ring(retvars+ret['fixed_numerals'],len(retvars));ep={x:rr.var(x) for x in rr.names}
for n,op,a,b in rs:
    p=rr.const(a) if isinstance(a,int) else ep[a];q=rr.const(b) if isinstance(b,int) else ep[b]
    ep[n]=rr.mul(p,q) if op=='*' else rr.add(p,q,-1 if op=='-' else 1)
deg=[]
for a,b in ret['comparisons']:
    p=rr.const(a) if isinstance(a,int) else ep[a];q=rr.const(b) if isinstance(b,int) else ep[b];deg.append(rr.degree(rr.add(p,q,-1)))
require(deg==[22,18,20,7,2,22,6],'unexpected retained gap degrees')
live=set(x for pair in ret['comparisons'] for x in pair)
for n,op,a,b in reversed(rs):
    if n in live:live.update([a,b])
require(all(n in live for n,*_ in rs),'dead retained gate')
require(all(x in live for x in retvars+ret['fixed_numerals']),'dead retained input')
rc=collections.Counter(r[1] for r in rs)
save('retained16_gap_system60.json',{'name':'retained16_auxiliary_gap_system60','repository_pin':PIN,'witness_domain':'strictly positive integers','witnesses':retvars,'fixed_numerals':ret['fixed_numerals'],'source':rs,'comparisons':ret['comparisons'],'residual_exact_degrees':deg,'exact_maximum_degree':max(deg),'ledger':{'operations':60,'multiplications':rc['*'],'additions_subtractions':rc['+']+rc['-'],'all_gates_live':True,'all_ports_live':True},'coordinate_change':'y_old=of-c+e=V+e; only canonical completeness needs e>0; soundness can take abs(y_old).','coefficient_binding':'Exactly the same coherent compiler tuple as the pinned retained16 source.'})
ledger=[]
for file in [source,rpath,ROOT/'upstream/RETAINED59_PROOF.pinned.md']:
    raw=file.read_bytes();ledger.append({'file':str(file.relative_to(ROOT)),'sha256':hashlib.sha256(raw).hexdigest(),'git_blob_sha1':hashlib.sha1(('blob '+str(len(raw))+'\0').encode()+raw).hexdigest(),'repository_pin':PIN})
save('SOURCE_LEDGER.json',{'repository_pin':PIN,'files':ledger})
save('AUDIT.json',{'checks':'PASS','quartic31_variables':31,'quartic31_equations':22,'quartic31_residual_degrees':[e['degree'] for e in new],'quartic31_exact_degree':4,'quartic31_tau4_coefficient':1,'quartic31_expanded_term_count':len(sos),'quartic31_system_ledger':sysledger,'quartic31_comparison_system_ledger':compareledger,'quartic31_polynomial_ledger':better_polyledger,'symbolic_packing_identity':True,'all_unchanged_source_residuals_match_literal_sparse_terms':True,'symbolic_circuit_residual_agreement':True,'random_signed_packing_checks':1000,'retained16_gap_operations':60,'retained16_gap_degrees':deg,'scope':'Exact algebra and static circuit checks, not a proof-assistant certificate for the inherited compiler or a solvability test.'})
print(json.dumps(json.loads((ROOT/'AUDIT.json').read_text()),indent=2))
