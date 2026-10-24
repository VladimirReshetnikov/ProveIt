#!/usr/bin/env python3
"""Exact constructor, exponent, primitive, contraction, and expansion audit.

The numerical controls supplement the ordinary projection proof; they are
not used to infer its universal zero-set equivalence.
"""
from pathlib import Path
import ast,copy,json,sys
from hashlib import sha256
HERE=Path(__file__).resolve().parent
UP=HERE.parent/'provenance/upstream'
sys.path[:0]=[str(HERE),str(UP)]
from build_projected import construct
from verify_synchronized import majorant,frame_audit,product_index_audit,exact_expansion
from affine_contract import independent_verify
from audit_calculus import verify_branch

def need(ok,msg):
    if not ok: raise ValueError(msg)

class Rename(ast.NodeTransformer):
    def __init__(self,mapping):self.mapping=mapping
    def visit_Name(self,node):
        node=copy.deepcopy(node);node.id=self.mapping.get(node.id,node.id);return node

def exact_constructor_identity():
    old=next(x for x in ast.parse((HERE/'direct_source_factored.py').read_text()).body
             if isinstance(x,ast.FunctionDef) and x.name=='source_pair_calculus')
    new=next(x for x in ast.parse((HERE/'projected_source.py').read_text()).body
             if isinstance(x,ast.FunctionDef) and x.name=='constructors')
    olddefs={x.name:x for x in old.body if isinstance(x,ast.FunctionDef)}
    newdefs={x.name:x for x in new.body if isinstance(x,ast.FunctionDef)}
    names=('I','A','M','E','N','X','req','clos','bundle')
    renold=Rename({'self':'BUILDER','b':'PARAM_B'})
    rennew=Rename({'b':'BUILDER','bb':'PARAM_B'})
    dump=lambda n:ast.dump(n,include_attributes=False)
    for name in names:
        need(dump(renold.visit(olddefs[name]))==dump(rennew.visit(newdefs[name])),
             'constructor changed: '+name)
    def assignment(tree,name):
        return next(x.value for x in tree.body if isinstance(x,ast.Assign)
                    and any(isinstance(t,ast.Name) and t.id==name for t in x.targets))
    need(dump(renold.visit(assignment(old,'codes')))==dump(rennew.visit(assignment(new,'codes'))),
         'literal list of nine conclusion codes differs')
    return {'identical_constructor_definitions':list(names),'identical_axiom_conclusions':9,
            'method':'exact Python AST identity after explicit alpha-renaming'}

def label_majorant(cert):
    weights={cert['input']:1}
    def exp(a):
        tag,val=a
        if tag=='c':
            need(val>=0,'negative constant');return max(0,(val-1).bit_length())
        need(tag=='v' and val in weights,'non-topological majorant');return weights[val]
    for g in cert['gates']:
        need(g['output'] not in weights,'duplicate gate')
        x,y=exp(g['left']),exp(g['right'])
        e=max(x,y)+1 if g['operation']=='add' else x+y
        need(g['operation'] in ('add','mul') and e==g['exponent'],'invalid bound')
        weights[g['output']]=e
    e=max(exp(a) for a in cert['outputs']);D=cert['emitted_exponent']
    need(e==cert['exponent'] and D>=e and D>0 and D&(D-1)==0,'wrong label exponent')
    return {'gate_inequalities':len(cert['gates']),'maximum_exponent':e,'emitted_exponent':D}

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--equations',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    source=json.loads((UP/'wire_eliminated_source.json').read_text())
    b,cert,label=construct(source)
    results={'status':'PASS','constructor_identity':exact_constructor_identity(),
             'inherited_calculus_rows':[verify_branch(x) for x in source['horn_branches']],
             'label_majorant':label_majorant(label),'CRT_majorant':majorant(cert),
             'frame_and_binomial':frame_audit(b,cert),'shared_indices':product_index_audit(b)}
    root=args.equations
    base=json.loads((root/'source/equation.json').read_text())
    results['literal_equations']={}
    # Only the retained source and final cap64 equation are deliverables.
    for sub in ('source','cap64'):
        eq=json.loads((root/sub/'equation.json').read_text())
        pol=json.loads((root/sub/'expanded_polynomial.json').read_text())
        receipt=exact_expansion(eq,pol)
        if sub!='source':
            elimin=json.loads((root/sub/'elimination_certificate.json').read_text())
            receipt['contraction']=independent_verify(base,eq,elimin)
        results['literal_equations'][sub]=receipt
    oldguard=0
    for g in range(-30,31):
        if g:
            d_old=abs(g)-1;d_new=g*g-1
            need(g*g==(d_old+1)**2 and g*g==d_new+1 and min(d_old,d_new)>=0,'guard lift')
            need(d_new==d_old*d_old+2*d_old,'exact guard shear')
            oldguard+=1
        else:
            need(all(g*g-d-1!=0 for d in range(20)),'zero guard allowed')
    results['guard_controls']=oldguard
    results['scope']='Exact finite interfaces and data. Universal source projection and Con(ZFC) equivalence use the ordinary proof and inherited calibration.'
    results['optimized_python']=not __debug__
    results['source_digest']=sha256((HERE/'projected_source.py').read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(results,indent=2,sort_keys=True)+'\n')
    print(json.dumps(results,indent=2,sort_keys=True))
if __name__=='__main__':main()
