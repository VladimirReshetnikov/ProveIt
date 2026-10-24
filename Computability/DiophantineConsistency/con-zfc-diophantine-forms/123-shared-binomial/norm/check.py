#!/usr/bin/env python3
"""Independent exact polynomial audit; does not import the circuit producer.

This checks transcription and finite algebra. It does not replace the
unbounded ordinary correctness proof or the source-to-refutation calibration.
All checks survive Python -O.
"""
from pathlib import Path
from collections import Counter
import ast, gzip, hashlib, importlib.util, itertools, json
from exact_polynomial import Ring

ROOT=Path(__file__).resolve().parent
VARS=['j','C','z','h','r','v','w','T','c','n','s']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
NAMES=['scalar11_original_direct','scalar11_original_center',
       'scalar11_original_center_reduced','scalar11_q4_center',
       'scalar11_q4_center_reduced']

def need(condition,why):
    if not condition: raise ValueError(why)

def specifications(p):
    f=[('J','6*j+1'),('qm','beta*J'),('q','qm+1'),('q2','q*q'),
       ('q3','q*q*q'),('q4','q**4'),('W','12*w+4'),('X','q*W'),
       ('Y','(2*v+1)*q**3'),('E','X*Y'),('a','(X+1)*Y'),
       ('H','4*a+3'),('Delta','(a+2)**2-1'),('F','(K0+W)*C-z*qm'),
       ('R','(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J'),
       ('k','R+1+h*E' if p['modulus']=='original' else 'R+1+4*h*q**4'),
       ('c2','c*c'),('eta','c-Y*k'),
       ('Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'),
       ('Budget','k*k*(q*q-Derr)-4*q*q*eta*eta'),
       ('ell','X*Y*Y'),('L','ell*k'),('Dt','1+ell*(ell+1)*k*k'),
       ('D','3*Budget-4'),('tguard','2*Dt*s'),
       ('P','Dt*(1+4*D*Dt*s*s)'),('I','2*r*c*c'),('I2','I*I'),
       ('strong','Delta*I*I'),('Df','1+Delta*I*I'),
       ('Q','Delta*Delta*I*I'),('delta','Q-1'),('b','c-R+4*I*T'),
       ('V','Df*b-c'),('Cy','Q*V*V-1'),('Da','(Q-1)*(Q*V*V-1)'),
       ('K','X*(3*c-2*X)+2'),('H2','H*H'),('H3','H**3'),
       ('zc','H*T+K'),('zc2','zc*zc'),
       ('Ac','(zc*zc+3*H*H)*(zc**3-19*H**3)'),
       ('S','s*r*H'),('S2','S*S'),('B','S*n-Ac'),
       ('shift','(2*Q-1)*V' if p['centered'] else '0'),
       ('center_part','S*shift'),('Z','S*(n+shift)-Ac' if p['centered'] else 'S*n-Ac'),
       ('u','S*S*Df'),('bnorm','4*S*S*Da'),('e','16*S*S*P'),
       ('ub','u*bnorm'),('ab','u+bnorm')]
    if p['reduced']:
        f += [('omega','B*B+2*B*center_part+S*S*(V*V+4*Q-4)'),
              ('z2','omega+bnorm'),
              ('inner','(omega-u-e)**2-4*(u*bnorm+u*e+bnorm*e)')]
    else:
        f += [('z2','Z*Z'),('inner','(z2-u-bnorm-e)**2-4*(u*bnorm+u*e+bnorm*e)')]
    f += [('out','inner*inner-64*u*bnorm*e*z2')]
    return f

def ring_binding(p):
    nodes=p['nodes']; names=dict(p['named_registers'])
    names.update({r[1]:i for i,r in enumerate(nodes) if r[0] in ('variable','coefficient')})
    names['out']=p['output']; covered=set(); record=[]
    for name,expression in specifications(p):
        if name not in names: continue
        refs=sorted({n.id for n in ast.walk(ast.parse(expression,mode='eval')) if isinstance(n,ast.Name)})
        need(all(n in names for n in refs),'live formula inputs for '+name)
        ring=Ring(refs); env={n:ring.var(n) for n in refs}
        memo={names[n]:value for n,value in env.items()}
        def evaluate(i):
            covered.add(i)
            if i in memo:return memo[i]
            row=nodes[i]
            if row[0]=='integer':value=ring.scalar(row[1])
            else:
                need(row[0] in ('add','sub','mul'),'unbound symbolic leaf '+name)
                a,b=evaluate(row[1]),evaluate(row[2])
                value=a+b if row[0]=='add' else a-b if row[0]=='sub' else a*b
            memo[i]=value;return value
        expected=eval(expression,{'__builtins__':{}},env)
        if type(expected)==int:expected=ring.scalar(expected)
        need(evaluate(names[name]).terms==expected.terms,'free polynomial identity '+name)
        record.append({'register':name,'formula':expression})
    missing=[i for i,r in enumerate(nodes) if r[0] in ('add','sub','mul') and i not in covered]
    need(not missing,'complete live graph coverage '+str(missing))
    return record

def universal_identities():
    ring=Ring(['z','a','b','e']);z,a,b,e=[ring.var(n) for n in ring.names]
    rad=[a,b,e];acc={0:ring.scalar(1)}
    for signs in itertools.product([-1,1],repeat=3):
        out={};factor={0:z,1:-signs[0]*ring.scalar(1),2:-signs[1]*ring.scalar(1),4:-signs[2]*ring.scalar(1)}
        for i,u in acc.items():
            for j,v in factor.items():
                value=u*v
                for bit,r in enumerate(rad):
                    if (i&j)&(1<<bit):value=value*r
                key=i^j;out[key]=out.get(key,ring.scalar(0))+value
        acc={i:v for i,v in out.items() if v.terms}
    norm=((z*z-a-b-e)**2-4*(a*b+a*e+b*e))**2-64*a*b*e*z*z
    need(set(acc)=={0} and acc[0].terms==norm.terms,'all eight conjugates')
    need(len(norm.terms)==35,'all 35 norm coefficients')
    ring=Ring(['B','S','Q','V']);B,S,Q,V=[ring.var(n) for n in ring.names]
    center=S*(2*Q-1)*V;Z=B+center;b=4*S*S*(Q-1)*(Q*V*V-1)
    omega=B*B+2*B*center+S*S*(V*V+4*Q-4)
    need((Z*Z-b-omega).terms=={},'centered cancellation identity')
    ring=Ring(['X','a','c']);X,a,c=[ring.var(n) for n in ring.names]
    need(((4*a+3)*X*c-2*(X*(X+2*a*c)-1)-(X*(3*c-2*X)+2)).terms=={},'signed projector identity')
    return {'norm_coefficients':35,'sign_product':True,'centering':True,'projector':True}

def topology(p):
    nodes=p['nodes'];degrees=[]
    for i,row in enumerate(nodes):
        op=row[0]
        if op in ('add','sub','mul'):
            need(len(row)==3 and all(type(j)==int and 0<=j<i for j in row[1:]),'backward binary gate')
            degrees.append(degrees[row[1]]+degrees[row[2]] if op=='mul' else max(degrees[row[1]],degrees[row[2]]))
        else:
            need(op in ('variable','integer','coefficient'),'valid leaf')
            degrees.append(int(op=='variable'))
    live=set();todo=[p['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):todo.extend(nodes[i][1:])
    need(live==set(range(len(nodes))),'every gate live')
    need([r[1] for r in nodes if r[0]=='variable']==VARS,'eleven ordered coordinates')
    need([r[1] for r in nodes if r[0]=='coefficient']==PORTS,'six fixed coefficients')
    counts=Counter(r[0] for r in nodes if r[0] in ('add','sub','mul'))
    need(sum(counts.values())==p['operations'] and dict(counts)==p['operation_counts'],'operation census')
    need(degrees[p['output']]==p['syntactic_degree_bound'],'syntactic degree')
    return {'live_nodes':len(nodes),'operations':sum(counts.values()),'counts':dict(counts),'syntactic_degree':degrees[p['output']]}

def leading_certificate(p):
    # Exact leading induction on the reduced graph. The direct graph has one
    # proved cancellation override, licensed by universal_identities above.
    order=['h','z','j','w','v','s','r','c','T','C','n']
    cr=Ring(PORTS);zero=(0,)*len(order);values=[];nm=p['named_registers']
    def key(value):return (sum(value[0]),)+value[0]
    def mul(a,b):return(tuple(x+y for x,y in zip(a[0],b[0])),a[1]*b[1])
    def add(a,b,minus=False):
        if key(a)>key(b):return a
        if key(a)<key(b):return(b[0],-b[1] if minus else b[1])
        out=a[1]-b[1] if minus else a[1]+b[1]
        need(bool(out.terms),'unexpected leading cancellation')
        return(a[0],out)
    override=None
    if p['centered'] and not p['reduced']:
        # Find exactly Z²-(u+bnorm); its actual degree is 96.
        for i,row in enumerate(p['nodes']):
            if row==['sub',nm['z2'],nm['ab']]:override=i
        need(override is not None,'center cut topology')
    for i,row in enumerate(p['nodes']):
        if i==override:
            # omega-u = 2(Sn-Ac)*S*shift + lower degree terms.
            A=values[nm['Ac']];S=values[nm['S']];shift=values[nm['shift']]
            val=mul((zero,cr.scalar(-2)),mul(A,mul(S,shift)))
            need(sum(val[0])==96,'exact centered inner degree')
        elif row[0]=='variable':
            ex=[0]*len(order);ex[order.index(row[1])]=1;val=(tuple(ex),cr.scalar(1))
        elif row[0]=='coefficient':val=(zero,cr.var(row[1]))
        elif row[0]=='integer':val=(zero,cr.scalar(row[1]))
        else:
            a,b=values[row[1]],values[row[2]]
            val=mul(a,b) if row[0]=='mul' else add(a,b,row[0]=='sub')
        need(bool(val[1].terms),'nonzero top at node '+str(i));values.append(val)
    ex,coef=values[p['output']];degree=sum(ex)
    need(degree==p['exact_degree'],'attained degree')
    need(len(coef.terms)==1,'coefficient is a single fixed-port monomial')
    port_exp,num=next(iter(coef.terms.items()));rem=abs(num);powers={}
    for prime in (2,3):
        power=0
        while rem%prime==0:rem//=prime;power+=1
        powers[str(prime)]=power
    need(rem==1 and all(e==0 for e in port_exp[1:]),'only powers of 2,3,beta')
    if p['modulus']=='q4':
        need(dict(zip(order,ex))=={'h':12,'z':4,'j':264,'w':40,'v':52,'s':12,'r':24,'c':32,'T':0,'C':0,'n':0},'specified degree-440 witness')
        need(powers=={'2':476,'3':306} and port_exp[0]==264 and num>0,'specified leading coefficient')
    return {'degree':degree,'monomial':dict(zip(order,ex)),
            'coefficient':{'sign':1 if num>0 else -1,**powers,'beta':port_exp[0]},
            'every_node_checked':len(values),'center_cut_used':override is not None}

def coefficients():
    binding=json.loads((ROOT/'coefficients/BINDING.json').read_text());ports={}
    for name,pin in binding['payloads'].items():
        raw=gzip.decompress((ROOT/'coefficients'/pin['file']).read_bytes())
        need(len(raw)==pin['raw_bytes'] and hashlib.sha256(raw).hexdigest()==pin['raw_sha256'],'actual payload '+name)
        ports[name]=int.from_bytes(raw,'little')
        need(ports[name].bit_length()==pin['bits'],'payload bit length '+name)
    need(ports['beta']==2**1064921-1 and ports['cone_A']==2**1113 and ports['cone_B']==2**666104,'short constant recipes')
    # The inherited coefficient recipe intentionally contains non-optimized
    # proof assertions. Rebuild it in a normal child in the release wrapper.
    if __debug__:
        spec=importlib.util.spec_from_file_location('recipe',ROOT/'coefficients/recipe/source34_builder.py')
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        rebuilt,audit=module.construct()
        for old,new in [('beta','beta'),('K','K0'),('MC','MC'),('MF_source','MF')]:
            need(rebuilt[old]==ports[new],'independent numeral reconstruction '+new)
    return {'all_six_payloads':True,'finite_recipe_rebuilt':bool(__debug__),'beta_bits':ports['beta'].bit_length()}

def main():
    report={'status':'PASS','scope':'finite algebra, constants, topology and exact degree',
            'identities':universal_identities(),'coefficients':coefficients(),'equations':[]}
    for name in NAMES:
        p=json.loads((ROOT/(name+'.json')).read_text())
        report['equations'].append({'name':name,'topology':topology(p),
            'all_registers':ring_binding(p),'degree':leading_certificate(p)})
    outfile=ROOT/('CHECK.json' if __debug__ else 'CHECK_OPTIMIZED.json')
    outfile.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','equations':[{ 'name':r['name'],
        'operations':r['topology']['operations'],'degree':r['degree']['degree']}
        for r in report['equations']]},indent=2))

if __name__=='__main__':main()
