#!/usr/bin/env python3
"""Emit explicit polynomial DAGs after certified monic elimination.

The arithmetic circuit contains only integer literals, variables, addition,
subtraction, and multiplication. All powers are fixed repetitions. The
acyclic elimination method is inherited from ProveIt report 152.
"""
from pathlib import Path
import hashlib,json,sys,random,argparse
import search as spec

ROOT=Path(__file__).resolve().parent
BASE_PATH=ROOT/'source207.json'
BASE=json.loads(BASE_PATH.read_text())

class Circuit:
    def __init__(self):self.nodes=[];self.table={}
    def node(self,op,*args):
        k=(op,*args)
        if k not in self.table:
            self.table[k]=len(self.nodes);self.nodes.append(list(k))
        return self.table[k]
    def constant(self,n):return self.node('const',n)
    def sum(self,ns):
        ns=list(ns)
        if not ns:return self.constant(0)
        a=ns[0]
        for b in ns[1:]:a=self.node('+',a,b)
        return a

def direction_certificate(nodes,roots,input_source):
    mod=1000000007
    ds=[];lc=[];nb=[]
    # nb bounds log2 of the coefficient l1 norm from above.
    for node in nodes:
        op=node[0]
        if op=='var':
            ds.append(1);lc.append((input_source[node[1]]+3)%mod);nb.append(0)
        elif op=='const':
            ds.append(0);lc.append(node[1]%mod);nb.append((abs(node[1])-1).bit_length() if node[1] else 0)
        else:
            a,b=node[1:]
            if op=='*':ds.append(ds[a]+ds[b]);lc.append(lc[a]*lc[b]%mod);nb.append(nb[a]+nb[b])
            else:
                d=max(ds[a],ds[b]);ds.append(d)
                va=lc[a] if ds[a]==d else 0;vb=lc[b] if ds[b]==d else 0
                lc.append((va+vb if op=='+' else va-vb)%mod);nb.append(max(nb[a],nb[b])+1)
    md=max(ds[r] for r in roots)
    candidates=[i for i,r in enumerate(roots) if ds[r]==md and lc[r]!=0]
    if not candidates:raise ValueError('No exact top-degree witness')
    w=candidates[0]
    return {'degree':2*md,'modulus':mod,'input_direction':[v+3 for v in input_source],
            'residual_degree_bounds':[ds[r] for r in roots],
            'witness_residual':w,'witness_top_residue':lc[roots[w]],
            'coefficient_height_at_most_power_of_two':max(2*nb[r] for r in roots)+(len(roots)-1).bit_length()}

def dependency_certificate(nodes,output,count):
    mod=1000000007;rng=random.Random(2718281828)
    for trial in range(8):
        values=[rng.randrange(1,mod) for _ in range(count)]
        ev=[]
        for node in nodes:
            op=node[0]
            if op=='var':v=values[node[1]]
            elif op=='const':v=node[1]
            elif op=='+':v=ev[node[1]]+ev[node[2]]
            elif op=='-':v=ev[node[1]]-ev[node[2]]
            else:v=ev[node[1]]*ev[node[2]]
            ev.append(v%mod)
        adj=[0]*len(nodes);adj[output]=1
        grad=[0]*count
        for i in range(len(nodes)-1,-1,-1):
            node=nodes[i];op=node[0];a=adj[i]
            if op=='var':grad[node[1]]=(grad[node[1]]+a)%mod
            elif op=='const':pass
            elif op in ('+','-'):
                adj[node[1]]=(adj[node[1]]+a)%mod
                adj[node[2]]=(adj[node[2]]+(a if op=='+' else -a))%mod
            else:
                adj[node[1]]=(adj[node[1]]+a*ev[node[2]])%mod
                adj[node[2]]=(adj[node[2]]+a*ev[node[1]])%mod
        if all(grad):return {'modulus':mod,'point':values,'gradient':grad}
    raise ValueError('Could not prove all input dependencies')

def build(profile,base_path=BASE_PATH):
    base_path=Path(base_path);base=json.loads(base_path.read_text())
    spec.configure(base_path)
    definitions={};removed_rows=set()
    for step in profile['steps']:
        r,v=step['row'],step['variable']
        if r in removed_rows or v in definitions or r not in spec.KEEP_ROWS or v not in spec.ACTIVE:raise ValueError('Invalid pivot')
        terms=spec.ROWS[r]['terms']
        cs=[c for c,m in terms if m==[v]]
        if len(cs)!=1 or abs(cs[0])!=1 or any(v in m for c,m in terms if m!=[v]):raise ValueError('Nonmonic pivot')
        definitions[v]=(r,[(-cs[0]*c,m) for c,m in terms if m!=[v]])
        removed_rows.add(r)
    inputs=[v for v in spec.ACTIVE if v not in definitions]
    circuit=Circuit();values={v:circuit.node('var',i) for i,v in enumerate(inputs)}
    visiting=set();definition_records=[]
    def sparse(terms):
        terms_out=[]
        for c,mon in terms:
            a=circuit.constant(c)
            for v in mon:a=circuit.node('*',a,define(v))
            terms_out.append(a)
        return circuit.sum(terms_out)
    def define(v):
        if v in values:return values[v]
        if v in visiting:raise ValueError('Cyclic definitions')
        visiting.add(v);r,terms=definitions[v]
        out=sparse(terms);values[v]=out
        visiting.remove(v);definition_records.append({'variable':v,'source_row':r,'root':out})
        return out
    for v in sorted(definitions):define(v)
    def expr(e):
        op=e[0]
        if op=='v':return define(e[1])
        if op=='c':return circuit.constant(e[1])
        return circuit.node(op,expr(e[1]),expr(e[2]))
    # Import the authenticated P207 DAG node for node, substituting each
    # source variable by its explicit acyclic definition. No expansion or
    # probabilistic equality test is needed for this exact transformation.
    imported=[]
    source_map=[];synthetic=216
    for v in base['variables']:
        old=v.get('source_index')
        if old is None:old=synthetic;synthetic+=1
        source_map.append(old)
    for n in base['nodes']:
        op=n[0]
        if op=='var':
            imported.append(define(source_map[n[1]]))
        elif op=='const':imported.append(circuit.constant(n[1]))
        else:imported.append(circuit.node({'add':'+','sub':'-','mul':'*'}[op],imported[n[1]],imported[n[2]]))
    retained_rows=[r for r in spec.KEEP_ROWS if r not in removed_rows]
    row_to_source_node={meta['parent_row']:node for meta,node in zip(base['residual_info'],base['residual_nodes']) if meta['parent_row'] is not None}
    residuals=[imported[row_to_source_node[r]] for r in retained_rows]
    residuals.extend(imported[node] for meta,node in zip(base['residual_info'],base['residual_nodes']) if meta['parent_row'] is None)
    out=circuit.sum(circuit.node('*',r,r) for r in residuals)
    dc=direction_certificate(circuit.nodes,residuals,inputs)
    dep=dependency_certificate(circuit.nodes,out,len(inputs))
    live=set()
    def walk(i):
        if i in live:return
        live.add(i);node=circuit.nodes[i]
        if node[0] in ('+','-','*'):
            walk(node[1]);walk(node[2])
    walk(out)
    meta={'variables':len(inputs),'residuals':len(residuals),'degree':dc['degree'],
          'eliminated_variables':len(definitions),'source_variables':len(source_map),
          'live_binary_operations':sum(circuit.nodes[i][0] in ('+','-','*') for i in live),
          'stored_nodes':len(circuit.nodes),'maximum_literal_absolute_value':max(abs(n[1]) for n in circuit.nodes if n[0]=='const'),
          'coefficient_height_bound_exponent':dc['coefficient_height_at_most_power_of_two']}
    return {'schema':'oriented-pooled-monic-polynomial-v1','domain':'unrestricted integers',
        'source216_sha256':hashlib.sha256(spec.SOURCE.read_bytes()).hexdigest(),
        'source207_sha256':hashlib.sha256(base_path.read_bytes()).hexdigest(),'base_file':base_path.name,
        'retained_source_indices':inputs,
        'variables':[{'source_index':v,'name':spec.S['variables'][v]['name'] if v<216 else 'pool_quotient_'+str(v-216)} for v in inputs],
        'source_removed_variables':sorted(spec.REMOVED_V),'source_removed_rows':sorted(spec.REMOVED_R),
        'elimination_steps':profile['steps'],'definitions':definition_records,'retained_source_rows':retained_rows,
        'source207_imported_node_map':imported,
        'nodes':circuit.nodes,'residual_roots':residuals,'output':out,
        'degree_certificate':dc,'dependency_certificate':dep,'metrics':meta}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--base',type=Path,default=BASE_PATH)
    parser.add_argument('--profiles',type=Path,default=ROOT/'profiles')
    parser.add_argument('--output',type=Path,default=ROOT/'equations')
    args=parser.parse_args();output=args.output;output.mkdir(parents=True,exist_ok=True)
    reports=[]
    for path in sorted(args.profiles.glob('cap*.json')):
        profile=json.loads(path.read_text());program=build(profile,args.base)
        name='integer{variables}_degree{degree}'.format(**program['metrics'])
        (output/(name+'.json')).write_text(json.dumps(program,sort_keys=True,separators=(',',':'))+'\n')
        reports.append({'name':name,**program['metrics']})
        print(json.dumps(reports[-1]),flush=True)
    (output/'RESULTS.json').write_text(json.dumps(reports,sort_keys=True,indent=2)+'\n')
if __name__=='__main__':main()
