#!/usr/bin/env python3
"""One exact complete-packet scheduling change for the pinned numeric signal compiler.
No giant gate file is emitted. Actual all-branch rows are censused and bound to
an independently reviewed projection receipt; bounded complete sources are
expanded exactly. The original and projected packets remain separate cases.
"""
import argparse
from collections import Counter
from contextlib import contextmanager
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys

PINS = {
    'numeric/compile_packet.py': '2df8a5b96630a9b343266ded0b26b6489be601acdee6f50d2a06dad4563e5f57',
    'numeric/MORITA_18_SIGNAL_MACHINE.json': '3f45f8aa2fbf5756cd1e4cf22fa3e55582abc9ba8275fe246652ceb94eb08e05',
}
CHECKER_SHA = '93aa415f401fa34e90c2b76c071d3ba52c3c9ace05f37302b97ba3bfea01ae9e'
RECEIPT_SHA = '116610066be57984e46f1f43e8f7e2a966adba6b6d091ebb72fbfddc7340d5b9'


def need(ok, message):
    if not ok: raise ValueError(message)


def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exact(a, b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if type(a) in (tuple, list): return len(a) == len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a == b


@contextmanager
def numeric(root):
    path = root/'numeric/compile_packet.py'
    data = path.read_bytes()
    need(hashlib.sha256(data).hexdigest() == PINS['numeric/compile_packet.py'], 'numeric source mismatch')
    name = '_signal_complementarity_pinned_numeric'
    before, present = sys.modules.get(name), name in sys.modules
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    try:
        exec(compile(data, str(path), 'exec'), mod.__dict__)
        yield mod
    finally:
        sys.modules.pop(name, None)
        if present: sys.modules[name] = before


def deleted(name, speeds):
    return name == 'span' or name.startswith('germ:') or name.startswith('first:') and speeds[int(name.split(':')[1])] < 0


def local_cost(row):
    need(len(row) > 0 and any(c > 0 for i,c in row), 'affine schedule needs a positive first term')
    need(all(type(c) is int and c and type(i) is int and i >= 0 for i,c in row), 'exact sparse row')
    return Counter(nonunit=sum(abs(c)>1 for i,c in row), nnz=len(row), rows=1)


class _SLP:
    """Literal binary schedule, with no cross-row CSE or free signed scaling."""
    def __init__(self): self.gates=[]; self.phase='affine'
    def op(self, op, a, b):
        out = 'g'+str(len(self.gates))
        self.gates.append([out, op, a, b, self.phase])
        return out
    def add(self,a,b): return self.op('add',a,b)
    def sub(self,a,b): return self.op('sub',a,b)
    def mul(self,a,b): return self.op('mul',a,b)
    def sum(self, terms):
        it=iter(terms)
        try: out=next(it)
        except StopIteration: return 0
        for term in it: out=self.add(out,term)
        return out
    def row(self, terms, constant=0):
        pos=next(i for i,(v,c) in enumerate(terms) if c>0)
        terms=[terms[pos]]+terms[:pos]+terms[pos+1:]
        def scaled(v,c): return v if abs(c)==1 else self.mul(abs(c),v)
        out=scaled(*terms[0])
        for v,c in terms[1:]: out=(self.add if c>0 else self.sub)(out,scaled(v,c))
        if constant: out=(self.add if constant>0 else self.sub)(out,abs(constant))
        return out


def _emit(branches, factored):
    """Private bounded literal model for complete actual-branch packet subsets."""
    d=len(branches[0]['matrix']); B=len(branches)
    e=[f'e{r}' for r in range(B)]
    copies=[[f'z{r}_{i}' for i in range(d)] for r in range(B)]
    x=[f'x{i}' for i in range(d)]; y=[f'y{i}' for i in range(d)]
    variables=x+y+e+[v for row in copies for v in row]
    dag=_SLP()
    E=dag.sum(e)
    rows=[dag.sub(E,1)]
    columns=[]
    for i in range(d):
        if factored:
            c=dag.sum(row[i] for row in copies); columns.append(c)
            rows.append(dag.sub(x[i],c))
        else:
            rows.append(dag.row([(x[i],1)]+[(row[i],-1) for row in copies]))
    for i in range(d):
        rows.append(dag.row([(y[i],1)]+[(copies[r][k],-c) for r,p in enumerate(branches) for k,c in p['matrix'][i]]))
    literal_rows=[[('',-1)]+[(v,1) for v in e]]
    literal_rows += [[(x[i],1)]+[(row[i],-1) for row in copies] for i in range(d)]
    literal_rows += [[(y[i],1)]+[(copies[r][k],-c) for r,p in enumerate(branches) for k,c in p['matrix'][i]] for i in range(d)]
    for r,p in enumerate(branches):
        for name, row in p['eq']:
            terms=[(copies[r][i],c) for i,c in row]
            rows.append(dag.row(terms)); literal_rows.append(terms)
        for name,row in p['strict']:
            slack=f's{r}_{name}';variables.append(slack)
            terms=[(copies[r][i],c) for i,c in row]+[(e[r],-1),(slack,-1)]
            rows.append(dag.row(terms));literal_rows.append(terms)
    dag.phase='squares'
    squares=[dag.mul(row,row) for row in rows]
    dag.phase='complementarity'
    row_sums=[dag.sum(row) for row in copies]
    if factored:
        total=dag.sum(columns)
        diagonal=dag.sum(dag.mul(e[r],row_sums[r]) for r in range(B))
        cross=dag.sub(dag.mul(E,total),diagonal)
        summands=squares+[cross]
    else:
        summands=squares+[dag.mul(dag.sub(E,e[r]),row_sums[r]) for r in range(B)]
    dag.phase='finalizer'
    output=dag.sum(summands)
    c=Counter(op for _,op,_,_,_ in dag.gates)
    return {'variables':variables,'gates':dag.gates,'output':output,'rows':rows,'literal_rows':literal_rows,'E':E,'columns':columns,'row_sums':row_sums,'factored':factored,
            'counts':{'M':c['mul'],'A':c['add']+c['sub'],'operations':len(dag.gates),'rows':len(rows),'finalizer_terms':len(summands),'finalizer_additions':sum(phase=='finalizer' for *_,phase in dag.gates)}}


def padd(a,b,sign=1):
    out=dict(a)
    for mon,c in b.items():out[mon]=out.get(mon,0)+sign*c
    return {m:c for m,c in out.items() if c}


def pmul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            mon=tuple(sorted(m+n));out[mon]=out.get(mon,0)+c*d
    return {m:c for m,c in out.items() if c}


def _expand(packet):
    env={v:{(v,):1} for v in packet['variables']}
    def val(x):return ({():x} if x else {}) if type(x) is int else env[x]
    for out,op,a,b,phase in packet['gates']:
        env[out]=pmul(val(a),val(b)) if op=='mul' else padd(val(a),val(b),1 if op=='add' else -1)
    return val(packet['output']), [val(row) for row in packet['rows']]


def _evaluate(packet, assignment):
    env=dict(assignment)
    def val(x):return x if type(x) is int else env[x]
    for out,op,a,b,phase in packet['gates']:
        a,b=val(a),val(b);env[out]=a*b if op=='mul' else a+b if op=='add' else a-b
    return val(packet['output'])


def verify(root, projection_checker, projection_receipt):
    need(__debug__, 'run without -O')
    root=Path(root).resolve()
    for rel,h in PINS.items():need(sha(root/rel)==h,'source pin mismatch: '+rel)
    need(sha(projection_checker)==CHECKER_SHA,'projection checker pin mismatch')
    need(sha(projection_receipt)==RECEIPT_SHA,'projection receipt pin mismatch')
    reviewed=json.loads(Path(projection_receipt).read_text())
    checks=Counter()
    def ck(label, ok):
        if not ok:raise AssertionError(label)
        checks[label]+=1
    schema=hashlib.sha256();samples={};census={'old':Counter(),'new':Counter()};mat=Counter()
    with numeric(root) as mod:
        C=mod.Compiler().close();B=C.B;d=18
        ck('actual_closure_dimensions',(len(C.modes),B)==(49700,80501))
        ids={0,1,7,101,1234,30213,70000,80500}
        for r,(s,t,J) in enumerate(C.branches):
            eq,st=C.guards(s,t,J);matrix=C.matrix(s,t,J);speed=C.cs[s]
            gone=[name for name,row in st if deleted(name,speed)]
            schema.update(json.dumps([r,eq,st,matrix,gone],separators=(',',':')).encode())
            for kind,strict in [('old',st),('new',[(name,row) for name,row in st if name not in gone])]:
                for name,row in eq:census[kind]+=local_cost(row)
                for name,row in strict:census[kind]+=local_cost(row+[(18,-1),(19,-1)])
                census[kind]['strict_slacks']+=len(strict)
            mat['nnz']+=sum(len(row) for row in matrix)
            mat['nonunit']+=sum(abs(c)>1 for row in matrix for i,c in row)
            if r in ids:samples[r]={'eq':eq,'strict':st,'matrix':matrix,'speed':speed}
        ck('all_actual_row_schema_digest',schema.hexdigest()==reviewed['branch_schema_sha256'])
    schedules={}
    for kind,c in census.items():
        c.update(rows=37,nnz=B+18*(B+1)+18+mat['nnz'],nonunit=mat['nonunit'])
        R,N,U=c['rows'],c['nnz'],c['nonunit']
        before={'M':U+R+B,'A':N+19*B,'operations':U+R+B+N+19*B}
        old=reviewed['complete_schedule'][kind]
        ck('full_parent_schedule_census',all(before[k]==old[k] for k in before) and N==old['nnz'] and R==old['rows'] and c['strict_slacks']==old['strict_slacks'])
        after={'M':U+R+B+1,'A':N+18*B+18,'operations':U+R+B+1+N+18*B+18}
        phases={'affine':{'M':U,'A':N-R+1},'squares':{'M':R,'A':0},'complementarity':{'M':B+1,'A':17*B+17+(B-1)+1},'finalizer':{'M':0,'A':R}}
        ck('complete_factored_phase_ledger',sum(v['M'] for v in phases.values())==after['M'] and sum(v['A'] for v in phases.values())==after['A'])
        ck('exact_full_saving',before['M']-after['M']==-1 and before['A']-after['A']==B-18 and before['operations']-after['operations']==80482)
        schedules[kind]={'before':before,'after':after,'saved_operations':before['operations']-after['operations'],'after_phases':phases,'affine_incidences':N,'nonunit_affine_coefficients':U,'affine_rows':R,'finalizer_terms_before':R+B,'finalizer_terms_after':R+1,'witnesses':old['witnesses'],'strict_slacks':old['strict_slacks'],'degree':2}
    rng=random.Random(80482);fixtures=[]
    groups=[[0],[0,1],[7,101,1234],[0,1,30213,70000,80500]]
    for ids in groups:
        for kind in ('old','new'):
            branches=[]
            for i in ids:
                p=samples[i]
                branches.append(dict(p,strict=[(n,row) for n,row in p['strict'] if kind=='old' or not deleted(n,p['speed'])]))
            old,new=_emit(branches,False),_emit(branches,True)
            op,orr=_expand(old);np,nrr=_expand(new)
            ck('complete_actual_subset_polynomial_identity',op==np)
            ck('every_actual_subset_affine_row',orr==nrr)
            ck('literal_rows_unchanged',old['literal_rows']==new['literal_rows'])
            for row,poly in zip(old['literal_rows'],orr):
                expected={}
                for v,c in row:expected=padd(expected,{(v,) if v else ():c})
                ck('literal_source_row_expansion',poly==expected)
            for signed in (False,True):
                for _ in range(4):
                    assignment={v:rng.randrange(-5 if signed else 0,8) for v in old['variables']}
                    ck('complete_subset_tuple_identity',_evaluate(old,assignment)==_evaluate(new,assignment))
            b=len(ids)
            ck('actual_subset_schedule_delta',new['counts']['M']==old['counts']['M']+1 and old['counts']['A']-new['counts']['A']==b-18)
            ck('actual_subset_finalizer',old['counts']['finalizer_terms']==len(old['rows'])+b and new['counts']['finalizer_terms']==len(new['rows'])+1 and new['counts']['finalizer_additions']==len(new['rows']))
            fixtures.append({'branch_ids':ids,'packet':kind,'before':old['counts'],'after':new['counts'],'expanded_terms':len(op),'polynomial_sha256':hashlib.sha256(json.dumps([[list(m),c] for m,c in sorted(op.items())],separators=(',',':')).encode()).hexdigest()})
    # Tiny complete packets independently cover all B,d in a modest rectangle.
    for b in range(1,7):
        for d in range(1,6):
            branches=[{'matrix':[[(i,1)] for i in range(d)],'eq':[],'strict':[]} for _ in range(b)]
            old,new=_emit(branches,False),_emit(branches,True)
            ck('tiny_complete_polynomial_identity',_expand(old)[0]==_expand(new)[0])
            ck('tiny_complete_schedule_delta',new['counts']['M']==old['counts']['M']+1 and old['counts']['A']-new['counts']['A']==b-d)
            ck('tiny_finalizer_terms',new['counts']['finalizer_terms']==2*d+2 and new['counts']['finalizer_additions']==2*d+1)
    return {'status':'PASS_SIGNAL_COMPLEMENTARITY_FACTORING','source_pins':PINS,'projection_checker_sha256':CHECKER_SHA,'projection_receipt_sha256':RECEIPT_SHA,'helper_sha256':sha(__file__),'branch_schema_sha256':schema.hexdigest(),'branches':B,'dimension':18,'counts':dict(sorted(checks.items())),'total_checks':sum(checks.values()),'complete_schedules':schedules,'bounded_full_packet_fixtures':fixtures,'scope':'Same complete polynomial on every integer tuple separately for each original or already projected packet; no witness or guard changes in this stage. Natural zero semantics and external horizon unchanged. Full schedule paid by actual row census and explicit loop recipe, not a materialized giant gate file.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',required=True,type=Path)
    parser.add_argument('--projection-checker',required=True,type=Path)
    parser.add_argument('--projection-receipt',required=True,type=Path)
    parser.add_argument('--output',required=True,type=Path)
    parser.add_argument('--expect',type=Path)
    args=parser.parse_args()
    result=verify(args.root,args.projection_checker,args.projection_receipt)
    if args.expect:need(exact(result,json.loads(args.expect.read_text())),'receipt mismatch')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':result['status'],'checks':result['total_checks'],'branches':result['branches'],'saving':result['complete_schedules']['new']['saved_operations']},sort_keys=True))

if __name__=='__main__':main()
