"""Data-only liveness and operation-count audit; not a polynomial proof."""
import collections, json, pathlib
base=pathlib.Path(__file__).resolve().parent
results=[]
for f in ['scalar-carrier12/rational.json','scalar-carrier12/integral.json']:
    j=json.loads((base/'sources'/f).read_text())
    nodes=j['nodes']; live=set()
    def visit(i):
        if i in live: return
        if type(i) is not int or not 0<=i<len(nodes): raise ValueError('invalid reference')
        live.add(i); row=nodes[i]
        if row[0] in {'add','sub','mul'}:
            if any(k>=i for k in row[1:]): raise ValueError('nontopological')
            for k in row[1:]: visit(k)
        elif row[0] not in {'integer','variable','coefficient'}: raise ValueError('unknown row')
    visit(j['output'])
    counts=dict(collections.Counter(nodes[i][0] for i in live if nodes[i][0] in {'add','sub','mul'}))
    if counts!=j['operation_counts'] or sum(counts.values())!=j['operations']: raise ValueError('count mismatch')
    deg=[]
    for row in nodes:
        if row[0]=='variable': d=1
        elif row[0] in {'integer','coefficient'}: d=0
        elif row[0]=='mul': d=deg[row[1]]+deg[row[2]]
        else: d=max(deg[row[1]],deg[row[2]])
        deg.append(d)
    results.append(dict(file=f,live_nodes=len(live),total_nodes=len(nodes),live_operations=sum(counts.values()),
                        breakdown=counts,syntactic_degree_upper_bound=deg[j['output']],
                        supplied_variables=sum(nodes[i][0]=='variable' for i in live),status='PASS'))
j=json.loads((base/'sources'/'ten-positive-direct-zero-offset'/'equation.json').read_text())
rows={r[0]:r for r in j['source']};live=set()
def visit_name(k):
    if k not in rows or k in live:return
    live.add(k)
    for v in rows[k][2:]:visit_name(v)
visit_name(j['output'])
counts=dict(collections.Counter(rows[k][1] for k in live))
if counts!=j['operation_breakdown'] or len(live)!=j['operations']: raise ValueError('ten-positive count mismatch')
results.append(dict(file='ten-positive-direct-zero-offset/equation.json',total_operations=len(rows),live_operations=len(live),breakdown=counts,status='PASS'))
receipt={'scope':'Independent live binary operation counts for three pinned literal DAGs. Syntactic degree is only an upper bound; published exact-degree proofs and complete coefficient calibration have not been rederived by this audit.','results':results}
(base/'CIRCUIT_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
