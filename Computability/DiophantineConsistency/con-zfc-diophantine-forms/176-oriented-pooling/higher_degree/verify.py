#!/usr/bin/env python3
"""Independent exact checker for acyclic monic projections.

This checker imports neither the producer nor the search program. It
validates the original monic rows, their dependency order, every imported
source circuit node, the residual and sum-of-squares circuits, top-degree
and nonconstant-variable certificates. No random identity test is used.
"""
from pathlib import Path
import json,hashlib,copy,argparse

ROOT=Path(__file__).resolve().parent

def require(p,msg):
    if not p:raise ValueError(msg)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

class Trees:
    def __init__(self):self.names={};self.nodes=[]
    def intern(self,op,*a):
        item=(op,*a)
        if item not in self.names:self.names[item]=len(self.nodes);self.nodes.append(item)
        return self.names[item]
    def total(self,values):
        values=list(values)
        if not values:return self.intern('const',0)
        z=values[0]
        for t in values[1:]:z=self.intern('+',z,t)
        return z

def validate_nodes(nodes,input_count):
    for i,n in enumerate(nodes):
        require(type(n) is list and n,'invalid node')
        op=n[0]
        if op=='const':require(len(n)==2 and type(n[1]) is int,'invalid constant')
        elif op=='var':require(len(n)==2 and type(n[1]) is int and 0<=n[1]<input_count,'invalid input')
        else:require(op in ('+','-','*') and len(n)==3 and all(type(j) is int and 0<=j<i for j in n[1:]),'invalid topological operation')

def check(program,source216,base):
    require(program['schema']=='oriented-pooled-monic-polynomial-v1','schema')
    rows=source216['residuals'];nodes=program['nodes']
    source_map=[];synthetic=216
    for v in base['variables']:
        s=v.get('source_index')
        if s is None:s=synthetic;synthetic+=1
        source_map.append(s)
    source_row_map={r['parent_row']:i for i,r in enumerate(base['residual_info']) if r['parent_row'] is not None}
    require(len(source_map)==len(set(source_map)),'base variable map')
    require(program['source_removed_variables']==sorted(set(range(216))-set(source_map)),'removed variable metadata')
    require(program['source_removed_rows']==sorted(set(range(len(rows)))-set(source_row_map)),'removed row metadata')
    # Authenticate the pivot equations as actual polynomials in the base
    # DAG. Only quadratic retained rows are expanded; the new pooling
    # residual is retained literally and has its separate arithmetic proof.
    base_polys={}
    def bp(i):
        if i in base_polys:return base_polys[i]
        n=base['nodes'][i];op=n[0]
        if op=='const':out={():n[1]} if n[1] else {}
        elif op=='var':out={(source_map[n[1]],):1}
        elif op in ('add','sub'):
            out=dict(bp(n[1]));sign=1 if op=='add' else -1
            for m,c in bp(n[2]).items():out[m]=out.get(m,0)+sign*c
            out={m:c for m,c in out.items() if c}
        else:
            out={}
            for a,c in bp(n[1]).items():
                for b,d in bp(n[2]).items():
                    m=tuple(sorted(a+b));out[m]=out.get(m,0)+c*d
            out={m:c for m,c in out.items() if c}
        base_polys[i]=out;return out
    for r,i in source_row_map.items():
        literal={tuple(m):c for c,m in rows[r]['terms']}
        require(bp(base['residual_nodes'][i])==literal,'base quadratic row binding')
    pivots={};removed=set()
    for step in program['elimination_steps']:
        r,v=step['row'],step['variable']
        require(type(r) is int and type(v) is int and r in source_row_map and v in source_map,'pivot target')
        require(v not in pivots and r not in removed,'duplicate pivot')
        terms=rows[r]['terms'];cc=[c for c,m in terms if m==[v]]
        require(len(cc)==1 and abs(cc[0])==1,'non-unit pivot')
        require(all(v not in m for c,m in terms if m!=[v]),'pivot reappears nonlinearly')
        pivots[v]=(r,[(-cc[0]*c,m) for c,m in terms if m!=[v]])
        removed.add(r)
    inputs=[v for v in source_map if v not in pivots]
    require(program['retained_source_indices']==inputs,'input list')
    require(len(program['variables'])==len(inputs),'input metadata length')
    validate_nodes(nodes,len(inputs))
    trees=Trees();canonical=[]
    for n in nodes:
        if n[0] in ('var','const'):canonical.append(trees.intern(*n))
        else:canonical.append(trees.intern(n[0],canonical[n[1]],canonical[n[2]]))
    expected={v:trees.intern('var',i) for i,v in enumerate(inputs)}
    visiting=set()
    def define(v):
        if v in expected:return expected[v]
        require(v in pivots,'undefined removed variable')
        require(v not in visiting,'cyclic pivots');visiting.add(v)
        r,terms=pivots[v];summands=[]
        for c,m in terms:
            q=trees.intern('const',c)
            for w in m:q=trees.intern('*',q,define(w))
            summands.append(q)
        expected[v]=trees.total(summands);visiting.remove(v)
        return expected[v]
    for v in pivots:define(v)
    recs=program['definitions'];require({x['variable'] for x in recs}==set(pivots),'definition coverage')
    for d in recs:
        require(d['source_row']==pivots[d['variable']][0],'definition row')
        require(canonical[d['root']]==expected[d['variable']],'definition expression mismatch')
    imported=[]
    for i,n in enumerate(base['nodes']):
        op=n[0]
        if op=='var':z=define(source_map[n[1]])
        elif op=='const':z=trees.intern('const',n[1])
        else:z=trees.intern({'add':'+','sub':'-','mul':'*'}[op],imported[n[1]],imported[n[2]])
        imported.append(z)
    mapping=program['source207_imported_node_map']
    require(len(mapping)==len(imported),'import coverage')
    require(all(canonical[j]==e for j,e in zip(mapping,imported)),'imported source node mismatch')
    kept=[r for r in source_row_map if r not in removed]
    require(program['retained_source_rows']==kept,'retained row map')
    extra=[i for i,x in enumerate(base['residual_info']) if x['parent_row'] is None]
    expected_residuals=[imported[base['residual_nodes'][source_row_map[r]]] for r in kept]+[imported[base['residual_nodes'][i]] for i in extra]
    roots=program['residual_roots']
    require(len(roots)==len(expected_residuals),'residual count')
    require([canonical[i] for i in roots]==expected_residuals,'residual expression mismatch')
    target=trees.total(trees.intern('*',r,r) for r in expected_residuals)
    require(canonical[program['output']]==target,'sum-of-squares mismatch')

    cert=program['degree_certificate'];mod=cert['modulus'];direction=cert['input_direction']
    require(type(mod) is int and mod>1 and len(direction)==len(inputs),'degree witness parameters')
    deg=[];top=[];norm=[]
    for n in nodes:
        op=n[0]
        if op=='var':d=1;t=direction[n[1]]%mod;b=0
        elif op=='const':d=0;t=n[1]%mod;b=(abs(n[1])-1).bit_length() if n[1] else 0
        else:
            u,v=n[1:]
            if op=='*':d=deg[u]+deg[v];t=top[u]*top[v]%mod;b=norm[u]+norm[v]
            else:
                d=max(deg[u],deg[v]);a=top[u] if deg[u]==d else 0;c=top[v] if deg[v]==d else 0
                t=(a+c if op=='+' else a-c)%mod;b=max(norm[u],norm[v])+1
        deg.append(d);top.append(t);norm.append(b)
    rd=[deg[r] for r in roots];maximum=max(rd)
    require(cert['residual_degree_bounds']==rd and cert['degree']==2*maximum,'degree upper bound')
    w=cert['witness_residual'];require(type(w) is int and 0<=w<len(roots),'degree witness row')
    require(rd[w]==maximum and top[roots[w]]!=0 and top[roots[w]]==cert['witness_top_residue'],'nonzero top-degree witness')
    height_bound=max(2*norm[r] for r in roots)+(len(roots)-1).bit_length()
    require(cert['coefficient_height_at_most_power_of_two']==height_bound,'coefficient bound')

    dep=program['dependency_certificate'];p=dep['modulus'];point=dep['point']
    require(type(p) is int and p>1 and len(point)==len(inputs),'dependency witness')
    vals=[]
    for n in nodes:
        if n[0]=='var':a=point[n[1]]
        elif n[0]=='const':a=n[1]
        elif n[0]=='+':a=vals[n[1]]+vals[n[2]]
        elif n[0]=='-':a=vals[n[1]]-vals[n[2]]
        else:a=vals[n[1]]*vals[n[2]]
        vals.append(a%p)
    ad=[0]*len(nodes);ad[program['output']]=1;gradient=[0]*len(inputs)
    for i in reversed(range(len(nodes))):
        n=nodes[i];z=ad[i];op=n[0]
        if op=='var':gradient[n[1]]=(gradient[n[1]]+z)%p
        elif op=='const':continue
        elif op in ('+','-'):
            ad[n[1]]=(ad[n[1]]+z)%p;ad[n[2]]=(ad[n[2]]+(z if op=='+' else -z))%p
        else:
            ad[n[1]]=(ad[n[1]]+z*vals[n[2]])%p;ad[n[2]]=(ad[n[2]]+z*vals[n[1]])%p
    require(gradient==dep['gradient'] and all(gradient),'variable-dependence certificate')
    live=set();stack=[program['output']]
    while stack:
        i=stack.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('+','-','*'):stack.extend(nodes[i][1:])
    metrics={'variables':len(inputs),'residuals':len(roots),'degree':2*maximum,
        'eliminated_variables':len(pivots),'source_variables':len(source_map),
        'live_binary_operations':sum(nodes[i][0] in ('+','-','*') for i in live),
        'stored_nodes':len(nodes),'maximum_literal_absolute_value':max(abs(n[1]) for n in nodes if n[0]=='const'),
        'coefficient_height_bound_exponent':height_bound}
    require(program['metrics']==metrics,'metrics')
    return metrics

def controls(program,s,b):
    cases=[]
    p=copy.deepcopy(program);p['nodes'][p['output']][0]='-';cases.append(p)
    p=copy.deepcopy(program);p['elimination_steps'][0]['row']=149;cases.append(p)
    p=copy.deepcopy(program);p['degree_certificate']['witness_top_residue']=0;cases.append(p)
    p=copy.deepcopy(program);p['dependency_certificate']['gradient'][0]=0;cases.append(p)
    p=copy.deepcopy(program);p['source207_imported_node_map'][-1]=0;cases.append(p)
    for i,p in enumerate(cases):
        try:check(p,s,b)
        except (ValueError,KeyError,IndexError):continue
        raise ValueError('Accepted mutation '+str(i))
    return len(cases)

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--receipt',type=Path);args=parser.parse_args()
    s=json.loads((ROOT/'source216.json').read_text());results=[]
    for path in sorted(ROOT.glob('equations*/integer*.json')):
        p=json.loads(path.read_text())
        base_path=ROOT/p['base_file'];b=json.loads(base_path.read_text())
        require(p['source216_sha256']==digest(ROOT/'source216.json'),'source216 hash')
        require(p['source207_sha256']==digest(base_path),'source207 hash')
        result={'file':path.name,'sha256':digest(path),'metrics':check(p,s,b),'rejected_mutations':controls(p,s,b)}
        results.append(result)
    receipt={'status':'PASS','method':'exact structural substitution, integer monic pivots, homogeneous coefficients, reverse derivatives',
             'programs':results,'unbounded_consistency_proof':'not supplied by finite verifier; inherited arithmetic theorem required'}
    if args.receipt:args.receipt.write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps(receipt,sort_keys=True))
if __name__=='__main__':main()
