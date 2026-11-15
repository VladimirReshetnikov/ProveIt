#!/usr/bin/env python3
"""Check the flat exchange certificate using independent canonical term IDs.

No Lean parser, imported proof constructors, K/S rules, arithmetic evaluator,
or source compiler is used. Numeric instantiation of I is 4*Cantor pairing.
"""
from pathlib import Path
import argparse,hashlib,json

def require(p,msg):
    if not p:raise AssertionError(msg)

def check(path):
    data=json.loads(path.read_text())
    require(data['parameters']==['A','B','C'],'Unexpected parameter list')
    pool={};nodes=[]
    def intern(node):
        if node not in pool:
            pool[node]=len(nodes);nodes.append(node)
        return pool[node]
    parameters={p:intern(('parameter',p)) for p in ('A','B','C')}
    def imp(a,b):return intern(('I',a,b))
    terms=[];height=[]
    for i,node in enumerate(data['terms']):
        require(isinstance(node,list),'Term is not a list')
        if node[0]=='parameter':
            require(len(node)==2 and node[1] in parameters,'Unknown parameter')
            terms.append(parameters[node[1]]);height.append(0)
        else:
            require(len(node)==3 and node[0]=='I','Unknown constructor')
            a,b=node[1:]
            require(type(a) is int and type(b) is int and 0<=a<i and 0<=b<i,'Nonpreceding term reference')
            terms.append(imp(terms[a],terms[b]));height.append(1+max(height[a],height[b]))
    def at(i):
        require(type(i) is int and 0<=i<len(terms),'Formula term index')
        return terms[i]
    formulas=[];rho=mp=0;maxpath=0
    for i,line in enumerate(data['lines']):
        f=at(line['formula'])
        if line['rule']=='rho':
            require(len(line['parameters'])==4,'Rho arity')
            a,b,c,u=map(at,line['parameters'])
            target=a
            for direction in line['component_path']:
                require(type(direction) is int and direction in (0,1),'Component direction')
                node=nodes[target]
                require(node[0]=='I','Path crosses a parameter')
                target=node[direction+1]
            require(target==u,'Component path does not prove the displayed bound')
            require(f==imp(imp(imp(c,u),a),imp(imp(a,c),imp(b,c))),'Incorrect rho formula')
            rho+=1;maxpath=max(maxpath,len(line['component_path']))
        else:
            require(line['rule']=='MP','Unpermitted proof rule')
            a,b=line['major'],line['minor']
            require(type(a) is int and type(b) is int and 0<=a<i and 0<=b<i,'Nonpreceding proof reference')
            require(formulas[a]==imp(formulas[b],f),'Modus ponens mismatch')
            mp+=1
        formulas.append(f)
    a,b,c=(parameters[p] for p in ('A','B','C'))
    expected=imp(imp(a,imp(b,c)),imp(b,imp(a,c)))
    last=data['conclusion']
    require(type(last) is int and 0<=last<len(formulas),'Conclusion index')
    require(formulas[last]==expected,'Wrong exchange theorem')
    require(at(data['expected_formula'])==expected,'Declared formula mismatch')
    return {'status':'PASS','certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'term_nodes':len(terms),'max_term_height':max(height),
            'proof_lines':len(formulas),'rho_instances':rho,'MP_steps':mp,
            'maximum_component_path_length':maxpath,'K_or_S_axioms':0,
            'independent_algorithm':'Hash-consed term IDs and flat earlier-premise replay.',
            'arithmetic_argument':'For all natural x,y, each is <=4*Cantor(x,y); path composition gives u<=a, including I(0,0)=0.'}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=check(args.certificate)
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
