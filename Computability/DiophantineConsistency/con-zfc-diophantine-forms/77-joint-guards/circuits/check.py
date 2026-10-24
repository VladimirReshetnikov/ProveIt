#!/usr/bin/env python3
"""Independent exact staged checker; never expand the high-degree final SOS.

1. Bind factored source rows by exact AST substitution (expanded sources by
   exact sparse algebra).
2. Validate the X,Y,W cut definitions over the original input ring.
3. Expand each residual only over those three independent cut registers.
4. Check the final sum of squares over independent residual cut registers.
"""
from pathlib import Path
import ast,copy,hashlib,json,sys
from collections import Counter
from exact_ring import Ring, require, equal, evaluate

ROOT=Path(__file__).resolve().parent
sys.setrecursionlimit(20000)
FAMILY=['joint19_degree88','joint20_degree32','joint21_degree20','joint22_degree16','joint23_degree12','joint25_octic']
REGS={
 'q':'beta*(3*J3+1)+1','W':'4*(3*w3+1)','X':'q*W','Y':'(2*v_scale+1)*q**3',
 'C':'q-F-alpha','k':'1-V+j*c+h*E','H':'4*a+3','Delta':'a**2+4*a+3',
 'R':'((q-1)*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*(3*J3+1)',
 'det':'(cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)**2',
 'T':'eta*(k-eta)','pos':'1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)'}
ROWS=['a-E-Y','E-X*(a-E)','c-eta-k*(a-E)',
 'tau**2-E*(c-eta)*(k+E*(c-eta))-1',
 '(X+a*c+gamma*H)**2-Delta*c**2-1','c*j-V-R',
 '(K0+W)*C-F-z*(q-1)','V+c-f*o','I-(2*r+1)*c**2',
 'I**2-Delta*(f**2-1)','I**2*(V**2-y**2)+y**2-1',
 'det*T-(pair_root**2-det-T+1)**2-pos']
MAPS={
 'joint19_degree88':{'V':'f*o-c','I':'(2*r+1)*c**2','E':'X*Y','eta':'c-Y*k','a':'(X+1)*Y'},
 'joint20_degree32':{'V':'f*o-c','I':'(2*r+1)*c**2','E':'X*Y','a':'(X+1)*Y'},
 'joint21_degree20':{'V':'f*o-c','I':'(2*r+1)*c**2','a':'E+Y'},
 'joint22_degree16':{'V':'f*o-c','I':'(2*r+1)*c**2'},
 'joint23_degree12':{'V':'f*o-c'},'joint25_octic':{}}

def inline(e,defs):
    parsed={n:ast.parse(v,mode='eval').body for n,v in defs.items()}
    def go(n,stack=()):
        if isinstance(n,ast.Name) and n.id in parsed:
            require(n.id not in stack,'Cyclic reference')
            return go(copy.deepcopy(parsed[n.id]),stack+(n.id,))
        for key,value in ast.iter_fields(n):
            if isinstance(value,ast.AST):setattr(n,key,go(value,stack))
            elif isinstance(value,list):setattr(n,key,[go(v,stack) if isinstance(v,ast.AST) else v for v in value])
        return n
    return go(ast.parse(e,mode='eval').body)

def parse(node,ring):
    if isinstance(node,str):node=ast.parse(node,mode='eval').body
    if isinstance(node,ast.Name):return ring.var(node.id)
    if isinstance(node,ast.Constant) and type(node.value)==int:return ring.const(node.value)
    if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return -parse(node.operand,ring)
    if isinstance(node,ast.BinOp):
        a=parse(node.left,ring)
        if isinstance(node.op,ast.Pow):
            require(isinstance(node.right,ast.Constant) and type(node.right.value)==int and 0<=node.right.value<=128,'Fixed exponent')
            return a**node.right.value
        b=parse(node.right,ring)
        if isinstance(node.op,ast.Add):return a+b
        if isinstance(node.op,ast.Sub):return a-b
        if isinstance(node.op,ast.Mult):return a*b
    raise ValueError('Unexpected AST '+ast.dump(node))

def reference(name):
    defs=dict(REGS);defs.update(MAPS[name]);rows=list(ROWS)
    deleted=set()
    for variable,row in [('V',7),('I',8),('a',0),('E',1),('eta',2)]:
        if variable in MAPS[name]:deleted.add(row)
    if name=='joint22_degree16':rows[10]='Delta*(f**2-1)*(V**2-y**2)+y**2-1'
    indices=[i for i in range(11) if i not in deleted]
    selected=[rows[i] for i in indices]
    if name=='joint25_octic':
        defs['T']='eta*zeta';selected.append('zeta-k+eta');indices.append('restore_zeta')
    selected.append(rows[11]);indices.append(11)
    return defs,selected,indices

def check_packet(name):
    path=ROOT/(name+'_dag.json');p=json.loads(path.read_text())
    source_path=ROOT/p['source_polynomial'];raw=source_path.read_bytes();src=json.loads(raw)
    require(hashlib.sha256(raw).hexdigest()==p['source_sha256'],'Pinned source '+name)
    require(p['witnesses']==src['variables'] and p['fixed_numerals']==src['fixed_numerals'],'Exact input declarations')
    require(p['exact_degree']==src['exact_degree'],'Inherited exact degree')
    require(p['coefficient_binding']==src['coefficient_binding'],'Whole fixed tuple binding')
    known=set(p['witnesses']+p['fixed_numerals']);live={p['output']};seen=[]
    for n,op,x,y in p['source']:
        require(n not in known and op in ('+','-','*'),'Unique valid gate')
        require(all(not isinstance(v,str) or v in known for v in (x,y)),'Backward-only references')
        known.add(n);seen.append(n)
    for n,op,x,y in reversed(p['source']):
        if n in live:live.update((x,y))
    require(set(seen)<=live and set(p['witnesses']+p['fixed_numerals'])<=live,'All and only live declarations')
    require(len(p['source'])==p['operations'],'Exact live gate count')
    require(dict(Counter(op for n,op,x,y in p['source']))==p['operation_breakdown'],'Exact gate histogram')
    residual_live=set(p['residuals'])
    for n,op,x,y in reversed(p['source']):
        if n in residual_live:residual_live.update((x,y))
    require(sum(n in residual_live for n in seen)==p['system_operations'],'Exact residual gate count')
    defs,selected,indices=reference(name)
    require(indices==p['source_row_indices'] and len(selected)==src['residual_count']==len(p['residuals']),'Exact row order')
    source_binding='AST equality after full inlining'
    expected=[inline(e,defs) for e in selected]
    if 'restoration_abbreviations' in src:
        require(src['restoration_abbreviations']==MAPS[name],'Exact restoration specification')
        actual=[ast.parse(e,mode='eval').body for e in src['residuals']]
        require([ast.dump(x,include_attributes=False) for x in actual]==[ast.dump(x,include_attributes=False) for x in expected],'Literal factored source binding')
    else:
        source_binding='Exact sparse equality for expanded lower-degree source residuals'
        full=Ring(p['witnesses']+p['fixed_numerals'])
        for i,(a,b) in enumerate(zip(expected,src['residuals'])):equal(parse(a,full),parse(b,full),'Expanded source row '+str(i))
    # Independent cut leaves are validated against the actual original inputs.
    full=Ring(p['witnesses']+p['fixed_numerals']);atoms={v:full.var(v) for v in full.names}
    roots=p['named_registers'];cuts=['X','Y','W']
    values=evaluate(p,[roots[n] for n in cuts],atoms)
    for n in cuts:equal(values[roots[n]],parse(inline(REGS[n],REGS),full),'Original cut definition '+n)
    # Expand each residual over the low-degree X,Y,W cut ring, not the SOS.
    ring=Ring(p['witnesses']+p['fixed_numerals']+cuts)
    atoms={v:ring.var(v) for v in p['witnesses']+p['fixed_numerals']}
    atoms.update({roots[n]:ring.var(n) for n in cuts})
    actual=evaluate(p,p['residuals'],atoms)
    partial={n:e for n,e in defs.items() if n not in cuts}
    term_counts=[]
    for i,(root,expr) in enumerate(zip(p['residuals'],selected)):
        ref=parse(inline(expr,partial),ring)
        equal(actual[root],ref,'Staged exact residual '+str(i));term_counts.append(len(ref.d))
    # Universal finalizer check over independent residual variables.
    final=Ring(p['residuals']);rv={r:final.var(r) for r in p['residuals']}
    final_actual=evaluate(p,[p['output']],rv)[p['output']]
    final_expected=sum((x*x for x in rv.values()),final.const(0))
    equal(final_actual,final_expected,'Literal unchanged sum of squares')
    return dict(name=name,variables=len(p['witnesses']),degree=p['exact_degree'],operations=p['operations'],
      system_operations=p['system_operations'],operation_breakdown=p['operation_breakdown'],
      source_binding=source_binding,exact_cut_definitions=cuts,exact_staged_residual_monomial_counts=term_counts,
      final_SOS_identity=True,source_sha256=p['source_sha256'],dag_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),status='PASS')

def displayed_first_norm():
    r=Ring(['X','Y','k']);X,Y,k=(r.var(n) for n in r.names)
    E=X*Y;eta_difference=k*Y
    equal(E*eta_difference*(k+E*eta_difference),X*Y**2*(X*Y**2+1)*k**2,'Displayed first-norm contraction')
    return True

def main():
    checks=[check_packet(name) for name in FAMILY]
    result={'status':'PASS','python_optimization':sys.flags.optimize,'packets':checks,
      'displayed_first_norm_contraction':displayed_first_norm(),
      'verification':'Exact polynomial equality by full-inlining source binding, validated cut substitution, residual sparse identities and universal SOS identity; no numeric sampling or full high-degree SOS expansion.'}
    path=ROOT/('CHECK_OPTIMIZED.json' if sys.flags.optimize else 'CHECK.json')
    path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
