#!/usr/bin/env python3
"""Independent exact source, gate, norm, fixed-port and degree verification.
No circuit builder is imported. All checks remain active under python -O.
"""
from pathlib import Path
from collections import Counter
import ast,copy,hashlib,json,random
from algebra_audit import Poly,require,norm_audit,borrow_audit,bitcount_audit
from source_audit import audit_source,source_rows
from fixed import leaves
R=Path(__file__).resolve().parent
VARIABLES=['f','g','h','k','l','w','x','y','z','m']

def circuit_audit(body,kerneldata,layout):
    nodes=body['nodes']; named=body['named_nodes']; counts=Counter(n['kind'] for n in nodes)
    require(body['variables']==VARIABLES and body['domain']=='Z','domain')
    require([n['name'] for n in nodes if n['kind']=='variable']==VARIABLES,'ten live variables')
    fixed=set(body['coefficient_recipes'])|{'beta_source','beta_mask'}
    for i,node in enumerate(nodes):
        k=node['kind']; require(k in {'add','sub','mul','literal','fixed','variable'},'gate kind')
        if 'left' in node:require(0<=node['left']<i and 0<=node['right']<i,'topological order')
        elif k=='fixed':require(node['name'] in fixed,'unknown fixed leaf')
        elif k=='literal':require(type(node['value'])==int,'literal type')
    live=set();todo=[body['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i); n=nodes[i]
        if 'left' in n:todo.extend([n['left'],n['right']])
    require(live==set(range(len(nodes))),'dead gates')
    actual_counts={k:counts[k] for k in ('add','sub','mul')}
    require(actual_counts==body['operation_counts'] and sum(actual_counts.values())==body['total_operations'],'gate ledger')
    p=Poly.var; w=layout['weights']; q=layout['targets']; W=max(w); H=layout['convolution_height']; HP=2*W+H+25
    expected={
        'b':1+3*p('f'),'base':p('beta_source')*p('b')**2,
        'ell':sum(p('base')**e for e in w),'packed_positive':p('ell')+p('g'),
        'Gcode':p('D2')*p('packed_positive')**2+p('D1')*p('packed_positive')+p('D0'),
        'top':p('base')**W,'N0':p('base')*p('top'),'N1':p('base')**(H+1),'N':p('N0')*p('N1'),
        'mask':p('N0')-1-(p('b')-1)*p('ell'),'targets':sum(p('base')**e for e in q),
        'Tcode':p('mask')+(p('base')-2)*p('targets')*p('N0'),
        'Jcode':2*p('Gcode')+p('targets'),'Scode':p('g')+p('Jcode')*p('N0'),
        'X':p('N')**2+(p('Scode')+p('Tcode'))*p('N')+p('N')-1-p('Scode'),
        'Y':p('beta_source')**15*p('beta_mask')*p('base')**(HP-16)*p('b'),
        'Ccap':p('b')*p('top'),'L':p('l')*p('Y'),'U':2*p('L')*p('X'),
        'V':4*p('g')*p('w')*p('Y'),'W':p('b')*p('w'),
        'halfA':p('L')*p('X')*(p('V')+1),'A':2*p('halfA'),
        'B1':2*p('X')+1,'C':p('B1')+(p('A')-2)*p('h'),
        'Pn':p('U')**2*p('V'),'K':p('X')+1+p('k')*(p('Pn')-2),
        'S':2*p('A')-5,'T':3*p('W')*p('C')-2*(p('W')**2-1),
        'r1':(p('Pn')**2-4)*p('K')**2+4,'CKL':p('C')-p('K')*p('L'),
        'Delta':8*p('Ccap')**3*p('g')*p('K')**2-p('g')**2*(32*p('CKL')**2*p('Ccap')**3+p('g')**2*p('K')**2),
        'O':p('f')**2*p('l')**2*p('Delta'),'xi':p('z')*p('x'),
        'D':(p('A')**2-4)*p('C')**2+4,'E':p('C')**2*p('D')*p('xi'),
        'Fm1':4*(p('A')**2-4)*p('E')**2,'F':p('Fm1')+1,
        'G':(p('halfA')-1)*p('Fm1')-1,'Omega':16*p('E'),
        'H':p('C')+(p('B1')-p('C'))*p('F')+p('Omega')*p('F')*p('y'),
        'I':(p('G')**2-1)*p('H')**2+1,'Sigma':p('xi')*p('S')**5,
        't':p('T')+p('S')*p('y'),
        'Theta':(p('t')**3-p('t')*p('S')**2-p('S')**3)*(p('t')**2+23*p('S')**2),
        'r0':p('b')*(1+(3*p('O')-4)*p('b')**2*p('z')**2),'r2':p('D')*p('F')*p('I'),
        'separator':p('Pn')**2+p('K')**2+3,'center':p('Sigma')*p('m')-p('Theta'),
        'norm_common':p('Sigma')**2*p('r0')**2,'a0':p('Sigma')**2*p('r0'),
        'a1':p('norm_common')*p('r1'),'a2':p('norm_common')*p('separator')**2*p('r2'),
        'Vnorm':p('center')**2+p('a2')-p('a0')-p('a1'),
        'Wnorm':p('Vnorm')**2+4*p('center')**2*p('a2')-4*p('a0')*p('a1'),
        'F10':p('Wnorm')**2-16*p('Vnorm')**2*p('center')**2*p('a2')}
    recipe_names={json.dumps(rec,sort_keys=True):name for name,rec in body['coefficient_recipes'].items()}
    require(len(recipe_names)==len(body['coefficient_recipes']),'unique coefficient recipes')
    used_recipes=set()
    for degree,layer in enumerate(kerneldata['kernels']):
        expr=Poly(0)
        for row in layer['terms']:
            rec=row['coefficient'];key=json.dumps(rec,sort_keys=True)
            require(key in recipe_names,'fixed recipe present')
            used_recipes.add(key)
            co=rec[0]['coefficient'] if len(rec)==1 and not any(rec[0]['powers']) else p(recipe_names[key])
            expr+=co*p('base')**row['exponent']
        expected['D'+str(degree)]=expr
    require(used_recipes==set(recipe_names),'no extraneous coefficient recipes')
    require(set(expected)==set(named),'all named nodes covered')
    for name,wanted in expected.items():
        stops={named[s]:p(s) for s in wanted.names() if s in named}; memo={}
        def evaluate(i):
            if i in stops:return stops[i]
            if i in memo:return memo[i]
            n=nodes[i]; k=n['kind']
            if k=='literal':value=Poly(n['value'])
            elif k in ('fixed','variable'):value=p(n['name'])
            else:
                a,b=evaluate(n['left']),evaluate(n['right']);value=a+b if k=='add' else a-b if k=='sub' else a*b
            memo[i]=value;return value
        require(evaluate(named[name])==wanted,'local polynomial identity '+name)
    a,e=p('halfA'),p('E')
    require((a-1)*4*((2*a)**2-4)*e**2-1==2*(2*a+2)*(2*a-2)**2*e**2-1,'factored Lucas G identity')
    return {'status':'PASS','local_identities':len(expected),'additional_factorization_identity':1,'operation_counts':actual_counts,'total_operations':sum(actual_counts.values()),'nodes':len(nodes)}

def degree_audit(body):
    W,H=body['W'],body['Hcode']
    dx=4*(W+H+2);dy=2*(2*W+H+9)+1;dc=2*W+1
    expected=456*dx+896*dy+24*dc+1760
    require((dx,dy,dc,expected)==(7964,4229,233,7428120),'independent degree formula')
    require(body['named_degrees']['a2']==1857030 and body['named_degrees']['Vnorm']==1857030 and body['named_degrees']['Wnorm']==3714060,'dominant scaled radicand degrees')
    require(2*body['named_degrees']['Vnorm']+2*body['named_degrees']['center']+body['named_degrees']['a2']==5735370<expected,'strictly lower final subtraction')
    certificates=[]
    for prime in [101,1009,1000003]:
        require(all(prime%d for d in range(2,int(prime**0.5)+1)),'prime check')
        fixed=leaves(body,prime);degrees=[];leaders=[]
        for node in body['nodes']:
            k=node['kind']
            if k=='variable':degree,leader=1,1
            elif k=='literal':degree,leader=0,node['value']%prime
            elif k=='fixed':degree,leader=0,fixed[node['name']]
            else:
                a,b=node['left'],node['right']
                if k=='mul':degree,leader=degrees[a]+degrees[b],leaders[a]*leaders[b]%prime
                else:
                    degree=max(degrees[a],degrees[b])
                    leader=((leaders[a] if degrees[a]==degree else 0)+(1 if k=='add' else -1)*(leaders[b] if degrees[b]==degree else 0))%prime
            degrees.append(degree);leaders.append(leader)
        require(degrees[body['output']]==body['degree_upper_bound']==expected,'degree ledger')
        require(leaders[body['output']]!=0,'exact degree lower bound')
        analytic=pow(2,3727056*body['base_scale_exponent']-17368,prime)*pow(3,7426392,prime)%prime
        require(leaders[body['output']]==analytic,'analytic positive leader agrees with literal circuit')
        require({k:degrees[i] for k,i in body['named_nodes'].items()}==body['named_degrees'],'named degree ledger')
        certificates.append({'prime':prime,'leading_coefficient':leaders[body['output']]})
    return {'exact_degree':expected,'specialization':'all ten variables equal one indeterminate',
            'analytic_leading_coefficient':'2^(3727056*kappa-17368)*3^7426392',
            'kappa':body['base_scale_exponent'],'dominant_final_term':'A2^4',
            'scaled_A2_degree':1857030,'final_subtraction_degree':5735370,'certificates':certificates}

def source_integer_audit(layout,kerneldata):
    # Supplemental exact finite arithmetic tests. The unbounded proof is in PROOF.md.
    pp=[2,3,5,7]
    def co(recipe):
        out=0
        for t in recipe:
            v=t['coefficient']
            for p,e in zip(pp,t['powers']):v*=p**e
            out+=v
        return out
    kernels=[{t['exponent']:co(t['coefficient']) for t in layer['terms']} for layer in kerneldata['kernels']]
    rows=source_rows();w=layout['weights'];W=max(w);H=layout['convolution_height'];targets=layout['targets']
    qmap=dict(zip(layout['order'],targets));rng=random.Random(1873116);cases=0;marked=0
    def coeff(poly):return co([{'powers':list(e),'coefficient':v} for e,v in poly.items()])
    def coefficient_at_target(row,ps):
        out=0
        for mon,poly in row.items():
            v=coeff(poly)*(2 if len(mon)==2 and mon[0]!=mon[1] else 1)
            for i in mon:v*=ps[i]
            out+=v
        return out
    require(coefficient_at_target(rows[4],[1]*31)==2,'all-one vector violates row five')
    for b in [4,16,25,49]:
        B=(1<<20)*b*b;powers=[1]
        for _ in range(H+2):powers.append(powers[-1]*B)
        ds=[sum(v*powers[e] for e,v in k.items()) for k in kernels]
        ell=sum(powers[e] for e in w);cap=b*powers[W]
        n0=powers[W+1];n1=powers[H+1];nn=n0*n1
        target=sum(powers[q] for q in targets);mask=n0-1-(b-1)*ell;tc=mask+(B-2)*target*n0
        assignments=[(None,g) for g in [0,1,cap-1,cap,2*cap-1]]
        for _ in range(6):
            ns=[rng.randrange(b) for _ in w];assignments.append((ns,sum(n*powers[e] for n,e in zip(ns,w))))
        for ns,g in assignments:
            u=ell+g;gc=ds[2]*u*u+ds[1]*u+ds[0];jc=2*gc+target;sc=g+jc*n0
            require(gc>0 and 0<=sc and 0<=tc and sc+tc<nn,'prebinary source bounds')
            xx=nn*nn+(sc+tc)*nn+nn-1-sc
            require(xx%3==0 and xx>3*b,'source congruence and size')
            if b in [4,16]:
                lb=b.bit_length()-1;lB=B.bit_length()-1
                maskpop=(W+23)*lB-31*lb-22
                require(tc.bit_count()==maskpop,'mask population')
                threshold=1+(W+H+2)*lB+maskpop
                require((xx.bit_count()>=threshold)==((sc&tc)==0),'population threshold')
                if ns is not None:
                    require(g&mask==0,'low coordinate digits')
                    ps=[n+1 for n in ns]
                    for row,q in qmap.items():
                        hs=coefficient_at_target(rows[row-1],ps)
                        digit=(jc//powers[q])%B
                        require(((digit&(B-2))==0)==(hs==0),'marked coefficient zero test')
                        marked+=1
            cases+=1
    return {'exact_integer_cases':cases,'marked_target_cases':marked,'nonbinary_square_bases':[25,49]}

def inherited_tail_audit():
    text=(R/'inherited/package59_build.py').read_text();tree=ast.parse(text)
    old=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='tail')
    newtree=ast.parse((R/'tail.py').read_text())
    new=next(n for n in newtree.body if isinstance(n,ast.FunctionDef) and n.name=='tail')
    require(ast.dump(old,include_attributes=False)==ast.dump(new,include_attributes=False),'unchanged inherited finalizer')
    return {'ast_identical_to_package59':True}

def main():
    body=json.loads((R/'generated/sun10.json').read_text())
    layout=json.loads((R/'data/layout.json').read_text())
    kernels=json.loads((R/'data/kernels.json').read_text())
    require(hashlib.sha256((R/'data/source_system65.json').read_bytes()).hexdigest()==body['source_syntax_sha256']=='9aec196c33b314940b5a9db8041741770f6053706ad752ae01f3cb548b765388','source pin')
    require(hashlib.sha256((R/'data/kernels.json').read_bytes()).hexdigest()==body['kernel_sha256'],'kernel pin')
    require(body['base_scale_exponent']==2134940 and body['mask_scale_exponent']==2134919 and body['popcount_power']==2130,'threshold binding')
    source=audit_source(layout,kernels)
    corrupt=copy.deepcopy(kernels);share=source['shared_taps'][0]
    t=next(t for t in corrupt['kernels'][share['degree']]['terms'] if t['exponent']==share['exponent'])
    t['coefficient'][0]['coefficient']+=1
    rejected=False
    try:audit_source(layout,corrupt)
    except ValueError:rejected=True
    require(rejected,'mutated shared tap must fail')
    result={'status':'PASS','scope':'Exact finite certificates and local identities, not an experimental consistency proof',
            'source':source,'changed_tap_negative_control':True,
            'circuit':circuit_audit(body,kernels,layout),'degree':degree_audit(body),
            'tail':inherited_tail_audit(),'norm':norm_audit(),
            'borrow':borrow_audit(),'population':bitcount_audit(),
            'integer_source':source_integer_audit(layout,kernels)}
    (R/'generated/VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
