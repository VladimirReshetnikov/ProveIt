#!/usr/bin/env python3
"""Independent read-only audit of the round16 small-variable circuits.

No producer, producer checker, third-party algebra package, or source
numeral program is imported. All checks are explicit exceptions under -O.
"""
import ast
import collections
import copy
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

def need(test, why):
    if not test:
        raise ValueError(why)

class Poly:
    """Sparse exact Z-polynomials in named indeterminates."""
    def __init__(self, terms):
        self.terms = {m: c for m, c in terms.items() if c}
    @staticmethod
    def coerce(x):
        return x if isinstance(x, Poly) else Poly({(): x})
    @staticmethod
    def symbol(s):
        return Poly({((s, 1),): 1})
    def __add__(self, other):
        t = self.terms.copy()
        for m, c in self.coerce(other).terms.items():
            t[m] = t.get(m, 0) + c
        return Poly(t)
    __radd__ = __add__
    def __neg__(self):
        return Poly({m: -c for m,c in self.terms.items()})
    def __sub__(self, other):
        return self + -self.coerce(other)
    def __rsub__(self, other):
        return self.coerce(other) + -self
    def __mul__(self, other):
        t = {}
        for m,c in self.terms.items():
            for n,d in self.coerce(other).terms.items():
                e = dict(m)
                for a,b in n:
                    e[a] = e.get(a,0)+b
                p = tuple(sorted(e.items()))
                t[p] = t.get(p,0)+c*d
        return Poly(t)
    __rmul__ = __mul__
    def __pow__(self, n):
        need(type(n) is int and n >= 0, 'polynomial exponent')
        out = self.coerce(1)
        for _ in range(n):
            out = out*self
        return out
    def serial(self):
        return [{'powers': dict(m), 'coefficient': c} for m,c in sorted(self.terms.items())]

def expression(src, env):
    def visit(node):
        if isinstance(node, ast.Expression): return visit(node.body)
        if isinstance(node, ast.Name): return env[node.id]
        if isinstance(node, ast.Constant):
            need(type(node.value) is int, 'integer literal AST')
            return Poly.coerce(node.value)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub): return -visit(node.operand)
        need(isinstance(node, ast.BinOp), 'supported AST')
        a = visit(node.left)
        if isinstance(node.op, ast.Pow):
            need(isinstance(node.right, ast.Constant), 'literal exponent')
            return a**node.right.value
        b = visit(node.right)
        if isinstance(node.op, ast.Add): return a+b
        if isinstance(node.op, ast.Sub): return a-b
        need(isinstance(node.op, ast.Mult), 'supported binary AST')
        return a*b
    return visit(ast.parse(src, mode='eval'))

def local_identity(rows, names, target, src, coverage):
    refs = {n.id for n in ast.walk(ast.parse(src, mode='eval')) if isinstance(n, ast.Name)}
    symbols = {r: Poly.symbol(r) for r in refs}
    cut = {names[r]: p for r,p in symbols.items()}
    need(len(cut)==len(symbols), 'distinct cut variables '+target)
    memo = dict(cut)
    def walk(i):
        if i in memo: return memo[i]
        row = rows[i]
        if row[0]=='integer': val=Poly.coerce(row[1])
        else:
            need(row[0] in ('add','sub','mul'), 'uncut leaf '+str(row)+' in '+target)
            coverage.add(i)
            a,b=walk(row[1]),walk(row[2])
            val = a+b if row[0]=='add' else a-b if row[0]=='sub' else a*b
        memo[i]=val
        return val
    need(not (walk(names[target])-expression(src, symbols)).terms, 'local identity '+target)

def positive_formulas(direct, lean):
    B='B' if direct else 'Bt'
    f=[('bJ','beta*J'),('q','bJ+1'),('C','q-F-alpha'),('X','q+x' if direct else 'q*w'),
       ('k','eta+zeta'),('c','k*Y+eta'),('mu','q*q+1'),('Am1','mu*Y*(X+1)'),
       ('Hp','4*Am1-1'),('Delta','Am1*(Am1+2)'),('Afull','Am1+1'),
       ('V0','X*mu*mu*Y*Y'),('Dtau','1+V0*(V0+1)*k*k'),
       ('R','(bJ*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J'),('e','k-R-1'),
       (B,'(q*K0+X)*C-q*F' if direct else '(K0+w)*C-F'),
       ('Kc','1+Delta*c*c'),('U','i*c*c*Afull*Kc'),
       ('SE','Delta*Dtau*U'),('Df','1+Delta*Dtau*U*U'),('Q','Delta*Delta*Dtau*U*U'),
       ('delta','Q-1'),('cTR','c*(T+alpha)-R'),('V','Df*cTR-c'),
       ('Dnum','Q*V*V-1'),('Dg','Dtau*Df'),('Radnum','Dg*Dnum'),
       ('P1','q**4*bJ' if direct else 'q**3*bJ'),
       ('Kpos','X*(3*c-2*X)+2'),('Mtot','P1*mu*mu*Hp')]
    if lean: f += [('Lmajor','Delta*Dtau*U*Df*cTR')]
    L='Lmajor' if lean else 'V2'
    if not lean: f += [('V2','V*V')]
    low='q*bJ*Y-q**3*B-bJ*X' if direct else 'bJ*Y-q**3*Bt'
    f += [('inner',low),('Znum',f'P1*mu*mu*(Hp*(n-{L}*{B})+Kpos)+Hp*(mu*mu*inner-P1*e)'),
          ('N','delta*Znum*Znum-Mtot*Mtot*Dg*Dnum')]
    return f

def scalar_formulas(weak):
    f=[('qm','beta*(6*j+1)'),('q','qm+1'),('X','q*(12*w+4)'),('Y','q*v' if weak else '(2*v+1)*q**3'),
       ('a','(X+1)*Y'),('H','4*a+3'),('Delta','(a+2)**2-1'),
       ('F','(K0+12*w+4)*C-z*qm'),('R','(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*(6*j+1)'),
       ('k','R+1+h*X*Y' if weak else 'R+1+4*h*q**4'),('eta','c-Y*k'),
       ('Budget','k*k*(q*q-(cone_A*F-q)**2-(cone_B*C-q)**2)-4*q*q*eta*eta'),
       ('D','Budget-4'),('Dt','1+X*Y*Y*(X*Y*Y+1)*k*k'),('P','Dt*(1+D*Dt*s*s)'),
       ('U','r*c*c'),('Df','1+Delta*U*U*P'),('Q','Delta*Delta*U*U*P'),('delta','Q-1'),
       ('b','c-R+4*U*P*T'),('V','Df*b-c'),('Cy','Q*V*V-1'),('K','X*(3*c-2*X)+2')]
    if weak:
        f += [('M','2*q*q'),('Dc','H*M'),('S','s*r*H*M**5'),
              ('zc','Dc*T+M*K+H*(v-q*q)'),('Ac','(zc*zc+3*Dc*Dc)*(zc**3-19*Dc**3)')]
    else:
        f += [('S','s*r*H'),('zc','H*T+K'),('Ac','(zc*zc+3*H*H)*(zc**3-19*H**3)')]
    return f+[('Z','S*(n+V)-Ac'),('Aux','S*S*Cy'),('Guard','S*S*P*Df'),
              ('Inner','delta*(Z*Z-Guard)-Aux'),('output','Inner*Inner-4*delta*Aux*Guard')]

def normalize(packet, positive):
    if not positive:
        rows=copy.deepcopy(packet['nodes']);names=dict(packet['named_registers']);names['output']=packet['output']
        names.update({r[1]: i for i,r in enumerate(rows) if r[0] in ('variable','coefficient')})
        return rows,names,packet['output']
    rows=[];names={}
    for tag,key in [('variable','witnesses'),('coefficient','fixed_numerals')]:
        for leaf in packet[key]: names[leaf]=len(rows);rows.append([tag,leaf])
    def ref(x):
        if type(x) is str:
            need(x in names, 'undefined register '+x)
            return names[x]
        need(type(x) is int, 'literal type')
        rows.append(['integer',x]);return len(rows)-1
    for name,op,a,b in packet['source']:
        need(name not in names, 'duplicate name')
        need(op in ('+','-','*'), 'positive operation')
        ia,ib=ref(a),ref(b);names[name]=len(rows);rows.append([{'+':'add','-':'sub','*':'mul'}[op],ia,ib])
    return rows,names,names[packet['output']]

def topology(packet,positive,ops):
    rows,names,output=normalize(packet,positive)
    need(type(output) is int and 0 <= output < len(rows), 'output index')
    need(all(type(i) is int and 0 <= i < len(rows) for i in names.values()), 'named register indices')
    for i,r in enumerate(rows):
        if r[0] in ('add','sub','mul'):
            need(len(r)==3 and all(type(x) is int and 0<=x<i for x in r[1:]), 'topological row')
        else:
            need(r[0] in ('integer','variable','coefficient') and len(r)==2, 'leaf shape')
            if r[0]=='integer': need(type(r[1]) is int, 'literal integer')
    live=set();todo=[output]
    while todo:
        i=todo.pop()
        if i in live: continue
        live.add(i)
        if rows[i][0] in ('add','sub','mul'):todo+=rows[i][1:]
    need(live==set(range(len(rows))), 'dead nodes')
    vars_expected=(['J','F','alpha','i','T','x' if packet['name'].startswith('direct') else 'w','Y','n','eta','zeta']
                   if positive else ['j','C','z','h','r','v','w','T','c','n','s'])
    ports=['beta','K0','MC','MF']+([] if positive else ['cone_A','cone_B'])
    need([r[1] for r in rows if r[0]=='variable']==vars_expected,'variable tuple')
    if not positive:
        need(packet['variables']==vars_expected and packet['variable_count']==11,'declared variables')
    need([r[1] for r in rows if r[0]=='coefficient']==ports,'coefficient tuple')
    need(packet['domain']==('strictly positive integers' if positive else 'unrestricted integers'),'domain')
    counts=collections.Counter(r[0] for r in rows if r[0] in ('add','sub','mul'))
    claimed=packet['operation_breakdown'] if positive else packet['operation_counts']
    expected=({'+':counts['add'],'-':counts['sub'],'*':counts['mul']} if positive else dict(counts))
    need(sum(counts.values())==ops==packet['operations'] and claimed==expected,'operation count')
    return rows,names,output,vars_expected

def identities():
    names='d Z S P f C W V a b t A c E D K B q mu h L n e Y X'.split()
    p={x: Poly.symbol(x) for x in names}
    checks={
      'zero_center':'(d*(0-S*S*P*f)-S*S*C)**2-4*d*S**4*C*P*f-S**4*(C-d*P*f)**2',
      'center':'d*((W+S*V)**2-S*S*P*f)-S*S*((d+1)*V*V-1)-(d*W*W+2*d*S*V*W+S*S*(1-V*V-d*P*f))',
      'two_square_recovery':'(t*t+a-b)**2-4*t*t*a-((t*t-a-b)**2-4*a*b)',
      'positive_strong_remainders':'(A*A-1)*(-1)-1+A*A',
      'positive_aux_remainder':'(-(A*A-1))*c*c-1+(1+(A*A-1)*c*c)',
      'budget_parity':'K*K*(q*q-(A-q)**2-(B-q)**2)-4*q*q*E*E+q*q*K*K-(K*K*(2*q*(A+B)-A*A-B*B)-4*q*q*E*E)',
      'weak_homogeneous_quintic':'(Z*Z+3*D*D)*(Z**3-19*D**3)-(Z**5+3*D*D*Z**3-19*D**3*Z*Z-57*D**5)',
      'positive_carrier_scaled':'q**3*h*mu*mu*(h*(n-L*B)+K)+h*(mu*mu*(h*Y-q**3*B)-q**3*h*e)-(q**3*h*mu*mu*h*n+q**3*h*mu*mu*K+h*h*mu*mu*Y-q**3*mu*mu*h*(1+h*L)*B-q**3*h*h*e)'
    }
    for name,src in checks.items():need(not expression(src,p).terms,'universal '+name)
    return list(checks)

def leading(rows,names,output,variables,positive,degree):
    order=(['x' if 'x' in variables else 'w','J','eta','zeta','Y','i','F','alpha','T','n'] if positive
           else ['h','T','j','w','v','s','r','c','C','z','n'])
    zero=(0,)*len(order);vals=[];upper=[];center_report=None
    def key(v):return (sum(v[0]),)+v[0]
    for i,row in enumerate(rows):
        tag=row[0]
        if tag=='variable':
            ex=list(zero);ex[order.index(row[1])]=1;value=(tuple(ex),Poly.coerce(1));bound=1
        elif tag in ('coefficient','integer'):
            value=(zero,Poly.symbol(row[1]) if tag=='coefficient' else Poly.coerce(row[1]));bound=0
        else:
            a,b=vals[row[1]],vals[row[2]]
            bound=upper[row[1]]+upper[row[2]] if tag=='mul' else max(upper[row[1]],upper[row[2]])
            if tag=='mul':value=(tuple(x+y for x,y in zip(a[0],b[0])),a[1]*b[1])
            elif key(a)>key(b):value=a
            elif key(b)>key(a):value=(b[0],-b[1] if tag=='sub' else b[1])
            else:value=(a[0],a[1]-b[1] if tag=='sub' else a[1]+b[1])
        if not positive and i==names['Inner']:
            s,v,delta=vals[names['S']],vals[names['V']],vals[names['delta']]
            sd,vd,dd=map(lambda z:sum(z[0]),(s,v,delta))
            wd=max(sd+1,sum(vals[names['Ac']][0]))
            dominant=2*sd+2*vd
            other=[dd+2*wd,dd+sd+vd+wd,2*sd,dd+sum(vals[names['Guard']][0])]
            need(max(other)<dominant,'center unique dominant degree')
            value=(tuple(2*x+2*y for x,y in zip(s[0],v[0])),-s[1]*s[1]*v[1]*v[1]);bound=dominant
            center_report={'degree':dominant,'competing_upper_bounds':other,'W_degree':wd}
        need(value[1].terms, 'leading cancellation '+str(i))
        need(all(c>0 for c in value[1].terms.values()) or all(c<0 for c in value[1].terms.values()),'coefficient sign certificate')
        vals.append(value);upper.append(bound)
    ex,coef=vals[output]
    need(sum(ex)==degree and upper[output]==degree,'exact global degree')
    if not positive:
        weak=degree==654
        expected={'j':300 if weak else 552,'w':98 if weak else 50,'v':146 if weak else 98,'h':48,'s':20,'r':16,'c':24,'T':2}
        need(dict(zip(order,ex))=={x:expected.get(x,0) for x in order},'explicit attained monomial')
        target=-(2**(546 if weak else 876))*(3**(398 if weak else 602))*Poly.symbol('beta')**(300 if weak else 552)
        need(not (coef-target).terms,'explicit attained coefficient')
    return {'degree':degree,'monomial':{v:e for v,e in zip(order,ex) if e},'coefficient':coef.serial(),'center':center_report}

def audit(packet,positive,ops,degree):
    need(packet['exact_degree']==degree,'claimed degree')
    rows,names,out,variables=topology(packet,positive,ops)
    formulas=positive_formulas(packet['name'].startswith('direct'),packet['name'].endswith('_lean')) if positive else scalar_formulas(degree==654)
    covered=set()
    for name,src in formulas:local_identity(rows,names,name,src,covered)
    need(covered=={i for i,r in enumerate(rows) if r[0] in ('add','sub','mul')}, 'complete arithmetic coverage '+str(set(range(len(rows)))-covered))
    return {'operations':ops,'exact_identities':len(formulas),'covered_arithmetic_gates':len(covered),'leading':leading(rows,names,out,variables,positive,degree)}

PIN_POS={'beta':'0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d','K0':'4364134a56b54cf132beeb9acd8e832be68f9083f4359ace4a588a1ea76a60f7','MC':'6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4','MF':'48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737'}
PIN_SCALAR={'beta':'6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea','K0':'18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af','MC':'3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777','MF':'78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722','cone_A':'66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615','cone_B':'42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401'}

def coefficients(packet,positive):
    if positive:
        binding=packet['coefficient_binding'];base=ROOT/'positive'/binding['path'];payloads=binding['ports'];pins=PIN_POS
    else:
        need(packet['coefficient_binding']=='../coefficients/BINDING.json','binding path')
        base=ROOT/'scalar'/'coefficients';binding=json.loads((base/'BINDING.json').read_text());payloads=binding['payloads'];pins=PIN_SCALAR
    need(set(payloads)==set(pins),'whole tuple')
    values={}
    for name,meta in payloads.items():
        blob=(base/meta['file']).read_bytes();raw=gzip.decompress(blob);h=hashlib.sha256(raw).hexdigest()
        need(h==pins[name]==meta['raw_sha256'],'pinned raw coefficient '+name)
        if positive:need(hashlib.sha256(blob).hexdigest()==meta['gzip_sha256'],'compressed coefficient')
        else:need(len(raw)==meta['raw_bytes'],'raw byte count')
        value=int.from_bytes(raw,'little');values[name]=value
        need(value.bit_length()==meta['bits'] and raw[-1]!=0,'minimal coefficient bytes')
    b=values['beta']
    need(values['K0']>0 and 0<values['MC']<b<values['MF']<2*b,'coefficient box')
    need(b==(1<<(590069 if positive else 1064921))-1,'authentic beta')
    if not positive:need(values['cone_A']==1<<1113 and values['cone_B']==1<<666104,'authentic cones')
    return pins

def main():
    universal=identities();results=[]
    residues={(-q*q*k*k-4*q*q*e*e)%16 for q in range(0,16,2) for k in range(16) for e in range(16)}
    need(residues=={0,12}, 'exhaustive Budget parity')
    need({(v-4)%16 for v in residues}=={8,12}, 'exhaustive D parity')
    need(not ({8,12}&{v*v%16 for v in range(16)}), 'nonsquare residues')
    paths=[('positive/equations/'+n+'.json',True,ops,degree) for n,ops,degree in
           [('single_square',87,436),('single_square_lean',88,380),('direct_single_square',92,384),('direct_single_square_lean',93,334)]]
    paths += [('scalar/two_root/two_root11_degree810.json',False,112,810),('scalar/two_root_weak/two_root_weak11_degree654.json',False,117,654)]
    for path,positive,ops,degree in paths:
        raw=(ROOT/path).read_bytes();packet=json.loads(raw);result=audit(packet,positive,ops,degree)
        result.update(path=path,sha256=hashlib.sha256(raw).hexdigest(),coefficient_sha256=coefficients(packet,positive))
        rejected=[]
        targets=(['U','Kc','Df','Q','cTR','Dg','Znum','Mtot','N'] if positive else ['D','U','P','Df','Q','b','S','Ac','Aux','Guard','Inner','output'])
        for target in targets:
            altered=copy.deepcopy(packet)
            if positive:
                row=next(r for r in altered['source'] if r[0]==target);row[1]='+' if row[1]=='*' else '*'
            else:
                idx=altered['output'] if target=='output' else altered['named_registers'][target]
                row=altered['nodes'][idx];row[0]='add' if row[0]=='mul' else 'mul'
            # Keep the corrupted packet's operation census coherent, so rejection
            # must reach arithmetic rather than merely fail metadata.
            if positive:
                altered['operation_breakdown']=dict(collections.Counter(r[1] for r in altered['source']))
            else:
                altered['operation_counts']=dict(collections.Counter(r[0] for r in altered['nodes'] if r[0] in ('add','sub','mul')))
            try:audit(altered,positive,ops,degree)
            except ValueError as error:
                need(str(error).startswith(('local identity','uncut leaf')), 'mutation rejected before mathematical cut: '+str(error))
                rejected.append(target)
            else:raise ValueError('accepted arithmetic mutation '+target)
        for target in ['domain','operations','exact_degree']:
            altered=copy.deepcopy(packet);altered[target]='wrong' if target=='domain' else packet[target]+1
            try:audit(altered,positive,ops,degree)
            except ValueError:rejected.append(target)
            else:raise ValueError('accepted metadata mutation '+target)
        # Independent coefficient-hash corruption must be rejected, not self-authenticated.
        if positive:
            altered=copy.deepcopy(packet);altered['coefficient_binding']['ports']['K0']['raw_sha256']='0'*64
            try:coefficients(altered,True)
            except ValueError:rejected.append('K0 raw hash')
            else:raise ValueError('accepted coefficient-binding mutation')
        result['rejected_mutations']=rejected;results.append(result)
    report={'status':'PASS','scope':'Independent exact finite algebra, syntax, coefficient binding and degree audit. Unbounded semantic claims are separately reviewed, not machine-proved.','universal_identities':universal,'exhaustive_residue_controls':{'even_q_k_eta_mod16_assignments':2048,'Budget_residues':[0,12],'D_residues':[8,12]},'equations':results}
    text=json.dumps(report,indent=2)+'\n'
    (Path(__file__).resolve().parent/('NORMAL.json' if __debug__ else 'OPTIMIZED.json')).write_text(text)
    print(json.dumps({'status':'PASS','equations':[{'path':r['path'],'operations':r['operations'],'degree':r['leading']['degree'],'identities':r['exact_identities'],'mutations':len(r['rejected_mutations'])} for r in results]},indent=2))

if __name__=='__main__':main()
