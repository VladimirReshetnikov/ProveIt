#!/usr/bin/env python3
"""Independent audit of the ordinary positive-power polynomial artifacts.
No producer modules are imported. Tests supplement, not replace, the proof.
"""
from pathlib import Path
import copy, hashlib, json, math, random
import sympy as sp

def require(condition, message):
    """Optimization-safe equivalent of the original audit assertions."""
    if not condition:
        raise AssertionError(message)

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent.parent/'alternative'


def evaluate(data, env, modulus=None):
    values=[]
    for i,node in enumerate(data['nodes']):
        op=node['op']
        if op=='var': value=env[node['name']]
        elif op=='const':
            require(type(node['value']) is int, 'Independent audit invariant at original line 18')
            value=node['value']
        elif op in ('add','mul'):
            require(all(type(j) is int and 0 <= j < i for j in node['args']), 'Independent audit invariant at original line 21')
            terms=[values[j] for j in node['args']]
            value=sum(terms) if op=='add' else math.prod(terms)
        elif op=='pow_fixed':
            require(type(node['base']) is int and 0 <= node['base'] < i, 'Independent audit invariant at original line 25')
            require(type(node['exponent']) is int and node['exponent'] >= 0, 'Independent audit invariant at original line 26')
            value=values[node['base']]**node['exponent']
        else: raise AssertionError('Nonordinary operation: '+str(op))
        values.append(value % modulus if modulus else value)
    return values


def independent_formula(env, r, retained):
    request=[tuple(env[c+str(i)] for c in ('n','k','m')) for i in range(r)]
    U,v,q,b,z=[env['p_'+c] for c in ('U','v','q','b','z')]
    Y=[request[i][1]+env['p_y'+str(i)] for i in range(r)]
    D=math.prod(Y); V=D**2*(v+1); B=1+4*D*(q+1)
    A=env['p_A'] if retained else B-U*b
    W=2+sum(sum(req) for req in request)
    def N(a,x,y): return x*x-(a*a-1)*y*y-1
    rows={'scale':A*A-W**3*(W+2)*(z+1)**2-1,
          'auxiliary_norm':N(A,U,V)}
    ports={'A':A,'B':B,'D':D,'V':V,'W':W}
    if retained: rows['base_congruence']=B-A-U*b
    for i,((n,k,m),y) in enumerate(zip(request,Y)):
        h,s,t=[env['p_'+c+str(i)] for c in ('h','s','t')]
        T=2*A*n-n*n-1; X=y*(A-n)+m+T*h
        S=X+U*s; R=k+4*y*t
        rows['main_norm_'+str(i)]=N(A,X,y)
        rows['index_norm_'+str(i)]=N(B,S,R)
        ports.update({key+str(i):value for key,value in [('Y',y),('T',T),('X',X),('S',S),('R',R)]})
    return rows,ports


def audit_generic(data):
    r=data['request_count']; retained='p_A' in data['variables']
    expected_inputs={c+str(i) for i in range(r) for c in ('n','k','m')}
    expected_aux={'p_'+c for c in ('z','U','v','q','b')} | {'p_'+c+str(i) for i in range(r) for c in ('y','h','s','t')}
    if retained: expected_aux.add('p_A')
    require(set(data['variables'])==expected_inputs|expected_aux, 'Independent audit invariant at original line 60')
    require(len(data['variables'])==len(set(data['variables'])), 'Independent audit invariant at original line 61')
    require(set(data['inputs'])==expected_inputs, 'Independent audit invariant at original line 62')
    require(data['variable_count']==len(data['variables']), 'Independent audit invariant at original line 63')
    require(data['auxiliary_count']==4*r+5+retained, 'Independent audit invariant at original line 64')
    require(data['residual_count']==2+2*r+retained, 'Independent audit invariant at original line 65')
    env={name:sp.Symbol(name) for name in data['variables']}
    actual=evaluate(data,env)
    expected,ports=independent_formula(env,r,retained)
    require(set(expected)==set(data['residuals']), 'Independent audit invariant at original line 69')
    for name,expr in expected.items():
        require(sp.expand(actual[data['residuals'][name]]-expr)==0, name)
    for name,expr in ports.items():
        require(sp.expand(actual[data['defined_ports'][name]]-expr)==0, name)
    root=data['nodes'][data['output']]
    require(root['op']=='add', 'Independent audit invariant at original line 75')
    require(len(root['args'])==len(expected), 'Independent audit invariant at original line 76')
    squared=[]
    for j in root['args']:
        node=data['nodes'][j]
        require(node['op']=='pow_fixed' and node['exponent']==2, 'Independent audit invariant at original line 80')
        squared.append(node['base'])
    require(sorted(squared)==sorted(data['residuals'].values()), 'Independent audit invariant at original line 82')
    actual_degrees={name:sp.Poly(expr,*env.values()).total_degree() for name,expr in expected.items()}
    exact_degree=2*max(actual_degrees.values()) # SOS leading real homogeneous forms cannot cancel.
    require(data['degree_upper_bound']>=exact_degree, 'Independent audit invariant at original line 85')
    require(exact_degree==(max(8*r+8,4*r+12,12) if retained else 12*r+8), 'Independent audit invariant at original line 86')
    if not retained: require(data['exact_degree']==exact_degree, 'Independent audit invariant at original line 87')
    rng=random.Random(6191+r+retained)
    for _ in range(50):
        numerical={name:rng.randrange(8) for name in env}
        rows,ports=independent_formula(numerical,r,retained)
        for p in (101,1009,65537):
            values=evaluate(data,numerical,p)
            require(values[data['output']]==sum(v*v for v in rows.values())%p, 'Independent audit invariant at original line 94')
    return {'auxiliary_count':len(expected_aux),'input_count':len(expected_inputs),
            'residual_count':len(expected),'exact_residual_degrees':actual_degrees,
            'exact_polynomial_degree':exact_degree,'random_modular_cases':150}


def pell(a,k):
    """Binary integer arithmetic in Z[s]/(s^2-(a^2-1))."""
    d=a*a-1
    def mul(p,q): return p[0]*q[0]+d*p[1]*q[1],p[0]*q[1]+p[1]*q[0]
    ans=(1,0); base=(a,1)
    while k:
        if k&1: ans=mul(ans,base)
        base=mul(base,base); k//=2
    return ans


def witness_k1(data, bases, negative=False):
    r=len(bases); retained='p_A' in data['variables']
    require(not (negative and retained), 'Independent audit invariant at original line 113')
    W=2+sum(2*n+1 for n in bases)
    alpha,frame_y=pell(W+1,W)
    require(frame_y%W==0, 'Independent audit invariant at original line 116')
    A=-alpha if negative else alpha
    U,V=pell(alpha,2 if negative else 4)
    require(U%2==1, 'Independent audit invariant at original line 119')
    b=((1-A)*pow(U,-1,4))%4
    while b<1 or A+U*b<5: b+=4
    B=A+U*b
    env={'p_z':frame_y//W-1,'p_U':U,'p_v':V-1,'p_q':(B-1)//4-1,'p_b':b}
    if retained: env['p_A']=A
    for i,n in enumerate(bases):
        env.update({f'n{i}':n,f'k{i}':1,f'm{i}':n,
                    f'p_y{i}':0,f'p_h{i}':0,f'p_s{i}':b,f'p_t{i}':0})
    require(all(type(x) is int and x>=0 for x in env.values()), 'Independent audit invariant at original line 128')
    values=evaluate(data,env)
    require(values[data['output']]==0, 'Independent audit invariant at original line 130')
    require(values[data['defined_ports']['A']]==A, 'Independent audit invariant at original line 131')
    for name,index in data['residuals'].items(): require(values[index]==0, name)
    bad=env.copy(); bad['m0']+=1
    require(evaluate(data,bad)[data['output']]!=0, 'Independent audit invariant at original line 134')
    return {'bases':bases,'sign':-1 if negative else 1,'maximum_witness_bits':max(x.bit_length() for x in env.values())}


def local_shared_crt(a,ks):
    coords=[pell(a,k) for k in ks]; Y=[y for x,y in coords]; D=math.prod(Y); M=4*D*D
    x,y=1,0
    for order in range(1,1000001):
        x,y=(a*x+(a*a-1)*y)%M,(x+a*y)%M
        if (x,y)==(1,0): break
    else: raise AssertionError('Finite regression period cap exceeded')
    U,V=pell(a,order)
    require(U%M==1 and V%M==0 and V>0, 'Independent audit invariant at original line 146')
    b=((1-a)*pow(U,-1,4*D))%(4*D)
    if b==0: b+=4*D
    B=a+U*b
    require(B>a and (B-1)%(4*D)==0, 'Independent audit invariant at original line 150')
    require(math.gcd(U,4*D)==1, 'Independent audit invariant at original line 151')
    for k,(X,Yi) in zip(ks,coords):
        S,R=pell(B,k)
        require((S-X)%U==0 and S>=X, 'Independent audit invariant at original line 154')
        require((R-k)%(4*Yi)==0 and R>=k, 'Independent audit invariant at original line 155')
        require(V%(Yi*Yi)==0, 'Independent audit invariant at original line 156')
        require(X*X-(a*a-1)*Yi*Yi==1, 'Independent audit invariant at original line 157')
        require(S*S-(B*B-1)*R*R==1, 'Independent audit invariant at original line 158')
    return {'base':a,'indices':ks,'period_mod_4D_squared':order,'maximum_coordinate_bits':max(U.bit_length(),V.bit_length())}


def negative_local_regression():
    checked=accepted=0
    for alpha in range(2,31):
      for n in range(1,min(alpha,7)):
       for k in range(1,5):
        for Y in range(k,k+6):
         for m in range(alpha):
          for h in range(3):
           X=-(alpha+n)*Y+m-(2*alpha*n+n*n+1)*h
           checked+=1
           if X*X-(alpha*alpha-1)*Y*Y==1:
            accepted+=1
            require((Y,k,h,m)==(1,1,0,n), 'Independent audit invariant at original line 174')
    return {'local_tuples_checked':checked,'accepted_tuples':accepted}


def main():
    source_pin=json.loads((HERE/"SOURCE_CHECK.json").read_text())
    for relative, expected in [("prior/PellMatiyasevic_reference.lean",source_pin["pinned_mathlib_source_sha256"]),("prior/PellRepresentation.lean",source_pin["wrapper_sha256"]),("PROOF.md",source_pin["proof_md_sha256_at_review"])]:
        require(hashlib.sha256((SOURCE/relative).read_bytes()).hexdigest()==expected,"Pinned source changed: "+relative)
    files=['POWER_ONE_9AUX.json','POWER_TWO_13AUX.json','POWER_TWO_14AUX.json']
    result={'status':'PASS','scope':'Standalone positive-power graphs; not source calibration or Lean verification.','artifacts':{},'full_k1_witnesses':[]}
    for filename in files:
        raw=(SOURCE/filename).read_bytes(); data=json.loads(raw)
        result['artifacts'][filename]={**audit_generic(data),'sha256':hashlib.sha256(raw).hexdigest()}
        bases_list=[[1],[2],[7]] if data['request_count']==1 else [[1,1],[1,2],[3,5]]
        for bases in bases_list:
            result['full_k1_witnesses'].append({'artifact':filename,**witness_k1(data,bases)})
            if 'p_A' not in data['variables']:
                result['full_k1_witnesses'].append({'artifact':filename,**witness_k1(data,bases,True)})
    result['shared_crt_tests']=[local_shared_crt(a,ks) for a,ks in [(2,[1,2]),(2,[2,3]),(3,[1,2])]]
    result['negative_branch_regression']=negative_local_regression()
    data=json.loads((SOURCE/files[0]).read_text())
    corruptions=[]
    bad=copy.deepcopy(data); bad['auxiliary_count']-=1; corruptions.append(('auxiliary count',bad))
    bad=copy.deepcopy(data); bad['exact_degree']-=1; corruptions.append(('degree claim',bad))
    bad=copy.deepcopy(data); bad['nodes'][bad['output']]['args'].pop(); corruptions.append(('dropped residual',bad))
    bad=copy.deepcopy(data)
    next(node for node in bad['nodes'] if node.get('op')=='const' and node.get('value')==4)['value']=6
    corruptions.append(('changed modulus coefficient',bad))
    result['deliberate_corruptions_rejected']=[]
    for label,bad in corruptions:
        try: audit_generic(bad)
        except (AssertionError,KeyError): result['deliberate_corruptions_rejected'].append(label)
        else: raise AssertionError('Corruption survived: '+label)
    (HERE/'AUDIT_CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
