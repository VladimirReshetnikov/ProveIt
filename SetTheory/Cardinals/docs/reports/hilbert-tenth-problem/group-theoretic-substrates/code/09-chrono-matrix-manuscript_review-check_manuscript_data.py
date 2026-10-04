"""Fresh manuscript cross-check. Read frozen JSON as data; execute no packet code."""
import collections
import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path('/workspace/shared/chronological-matrix-report55-release-20261004')
OUT = Path(__file__).resolve().parent
SCI = Path('/workspace/shared/matrix-chronological-certificate-20261004')
AUD = Path('/workspace/shared/matrix-chronological-independent-audit-20261004')
def need(test, message):
    if not test:
        raise ValueError(message)
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path):
    return json.loads(path.read_text())

expected_article = {
    'Report55.tex':'1846c0d191ff167602fb252ff3375a3809782ada03f786ae9bdea20f34b803d9',
    'Report55.pdf':'b5b78e9b1d485ea1fc5d09d028805e4c6d2c0abbfedfa25c367bc0449fc6d417'}
for filename, digest in expected_article.items():
    need(sha(ROOT/'article'/filename)==digest, 'Reviewed article pin: '+filename)
preserved = {}
for origin, target in [(SCI, ROOT/'science'), (AUD, ROOT/'independent_audit')]:
    for p in sorted(origin.rglob('*')):
        if p.is_file():
            rel = p.relative_to(origin)
            need((target/rel).is_file(), f'Missing preserved file: {rel}')
            need(p.read_bytes() == (target/rel).read_bytes(), f'Changed preserved file: {rel}')
            preserved[str(target.relative_to(ROOT)/rel)] = sha(p)

manifest = read(SCI/'evidence/frozen-manifest.json')
for entry in manifest['files']:
    p=SCI/entry['path']
    need(sha(p)==entry['sha256'], f'Science hash mismatch: {p}')
    need(p.stat().st_size==entry['bytes'], f'Science size mismatch: {p}')
need(len(manifest['files'])==18, 'Frozen manifest count')

d = read(SCI/'evidence/polynomial-dag.json')
need(sha(SCI/'evidence/polynomial-dag.json') == '95e2563fcfcaecfdc5918ffd6dd7421896350df8969a38f08cbb5f5060d80034', 'DAG pin')
ws=set(d['witnesses']); need(len(ws)==len(d['witnesses'])==41309,'Witness count')
need(d['input']=='x', 'Input x')
gates=d['gates']; body=d['body_gate_count']; degrees=[]
# Exact two-variable restriction setting all other independent variables to zero.
# This preserves the pure coefficient w^8 g^4 in the original polynomial.
polys=[]
def ref(r, before):
    k,v=r.split(':',1)
    if k=='gate':
        n=int(v); need(0<=n<before, 'Topological gate reference'); return degrees[n],polys[n]
    if k=='constant':
        n=int(v); return 0,({(0,0):n} if n else {})
    if k=='input':
        need(v=='x','Unexpected input'); return 1,{}
    need(k=='witness' and v in ws, 'Unknown witness')
    return 1,({(1,0):1} if v=='bounds.offset.w' else {(0,1):1} if v=='bounds.offset.g' else {})
def polyop(op,p,q):
    out=collections.defaultdict(int)
    if op=='*':
        for (i,j),a in p.items():
            for (k,l),b in q.items(): out[i+k,j+l]+=a*b
    else:
        for t,a in p.items(): out[t]+=a
        for t,b in q.items(): out[t]+=b if op=='+' else -b
    return {t:a for t,a in out.items() if a}
for n,g in enumerate(gates):
    need(len(g)==3 and g[0] in {'+','-','*'}, 'Gate vocabulary')
    op,l,r=g; dl,pl=ref(l,n); dr,pr=ref(r,n)
    degrees.append(dl+dr if op=='*' else max(dl,dr))
    polys.append(polyop(op,pl,pr))
need(d['output']==f'gate:{len(gates)-1}', 'Output last gate')
need(degrees[-1]==12, 'Degree upper bound')
need(polys[-1].get((8,4),0)==1, 'Degree twelve attaining coefficient')
counts=dict(collections.Counter(g[0] for g in gates))
bodycounts=dict(collections.Counter(g[0] for g in gates[:body]))
need(counts=={'*':72093,'+':64111,'-':47812},'Full ledger')
need(bodycounts=={'*':48475,'+':40494,'-':24194},'Body ledger')
need(len(gates)==184016 and body==113163,'Gate counts')
need(len(d['equalities'])==23618 and len(d['ports'])==506,'Residual and port counts')
need(collections.Counter(m['kind'] for m in d['macros'])=={'power':1475,'subset':491},'Macro counts')
# Verify the complete literal finalizer rather than trust ledger metadata.
squares=[]; cursor=body
for lhs,rhs,name in d['equalities']:
    need(gates[cursor]==['-',lhs,rhs], f'Residual finalizer: {name}')
    need(gates[cursor+1]==['*',f'gate:{cursor}',f'gate:{cursor}'], f'Square: {name}')
    squares.append(f'gate:{cursor+1}');cursor+=2
acc=squares[0]
for sq in squares[1:]:
    need(gates[cursor]==['+',acc,sq], 'Unweighted sum finalizer')
    acc=f'gate:{cursor}';cursor+=1
need(cursor==len(gates) and acc==d['output'], 'Finalizer exhaustiveness')
# All source leaves/gates must contribute to the literal output.
seen=set();todo=[d['output']]
while todo:
    r=todo.pop()
    if r in seen: continue
    seen.add(r)
    if r.startswith('gate:'): todo.extend(gates[int(r[5:])][1:])
need(sum(r.startswith('gate:') for r in seen)==len(gates),'Dead gates')
need({r[8:] for r in seen if r.startswith('witness:')}==ws,'Dead witnesses')
need('input:x' in seen,'Dead input')

countdown=read(SCI/'sources/matrix193_countdown_rows.json')
tr=countdown['transitions'];need(tr['count']==97 and len(tr['tiles'])==96,'Actual branches')
need(countdown['initial_state']['X']==[35426321,-19628667] and countdown['initial_state']['Y']==[1,0] and countdown['initial_state']['n']=='ordinary_x','Initial state')
need(tr['loader']['Y_matrix']==[52891,-29036,94920,-52109] and tr['loader']['counter_change']==-1,'Loader')
need(tr['tile_counter_guard']=='n=next_n=0','Both tile guards')
ids=[t['tile_id'] for t in tr['tiles']]
need(ids==[1,2,18,19]+list(range(21,108))+[109,110,111,112,114], 'Tile identifiers')
def transpose_block(flat):
    return [[flat[0],flat[2]],[flat[1],flat[3]]]
def blockdiag(a,b):
    n=len(a);m=len(b)
    return [row+[0]*m for row in a]+[[0]*n+row for row in b]
maps=[blockdiag([[1,0],[0,1]],transpose_block(tr['loader']['Y_matrix']))]
maps += [blockdiag(transpose_block(t['K']),transpose_block(t['G'])) for t in tr['tiles']]
threshold=max([128]+[2+sum(map(abs,row))+abs(1-sum(row)) for a in maps for row in a])
need(threshold==18510406623962009412894903228521 and threshold < 2**104,'Radix threshold')

ctx=read(SCI/'sources/matrix193_context_absorption.json')['packet']
lift=read(SCI/'sources/matrix195_counted_suffix.json')['packet']
need(ctx['U']=='[110' and ctx['V']=='A0]' and lift['contexts']=={'U':'[110','V':'A0]'},'Fixed contexts')
need(len(ctx['generators'])==193 and len(lift['generators'])==195,'Generator counts')
O=[[1,0,0],[0,0,0],[0,0,0]];F=[[0,1,0],[0,0,0],[0,0,0]];Dc=[[0,0,0],[0,1,1],[0,0,1]]
I2=[[1,0],[0,1]];B=[[-52109,29036],[-94920,52891]]
for old,new in zip(ctx['generators'],lift['generators']):
    need(blockdiag(old['matrix'],O)==new['matrix'], 'Actual old lift')
need(lift['generators'][-2]['matrix']==blockdiag(blockdiag(I2,I2),F),'END matrix')
need(lift['generators'][-1]['matrix']==blockdiag(blockdiag(B,I2),Dc),'COUNT matrix')
expected=blockdiag(blockdiag(I2,[[1,2],[0,1]]),[[0,1,'x'],[0,0,0],[0,0,0]])
need(lift['target_template']==expected,'Literal direct-input target')
def rank(m):
    a=[list(map(Fraction,row)) for row in m];n=len(a);r=0
    for c in range(len(a[0])):
        piv=next((p for p in range(r,n) if a[p][c]),None)
        if piv is None: continue
        a[r],a[piv]=a[piv],a[r];d=a[r][c];a[r]=[v/d for v in a[r]]
        for p in range(n):
            if p!=r:
                d=a[p][c];a[p]=[v-d*w for v,w in zip(a[p],a[r])]
        r+=1
    return r
ranks=[rank(g['matrix']) for g in lift['generators']]
need(ranks==[5]*194+[6],'All actual matrix ranks')
need(sum(len(row) for g in lift['generators'] for row in g['matrix'])==9555,'Actual entry count')

pins={
'science/sources/matrix193_countdown_rows.json':'f365eb9b62242b395b33766d00a246f0ebcd1a28d867cbcf1173037552b916e0',
'science/sources/matrix193_context_absorption.json':'73f8cae212c6c1917e73cc76c7bf3c43b8c587748bbf4327eddf4c82e726a436',
'science/sources/matrix195_counted_suffix.json':'3c803a9a219eebf299a40dcece8958e905b3c59f8ba8b5cb1e60d9c52812c5bd',
'dependencies/pell-source.lean':'993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a'}
pins.update({
 'dependencies/matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742',
 'dependencies/matrix193_kernel_row_projection.md':'400aab15caa9462808cc2dc2ef68f013797a9bc656c97acecdd610de81a13c6e',
 'dependencies/group_directed_semigroup193.md':'75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
 'dependencies/u15_unary_block_interface.md':'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452'})
for p,h in pins.items():need(sha(ROOT/p)==h,'Article pin '+p)
receipt={
 'status':'PASS','scope':'Fresh manuscript claim cross-check; does not replace the full semantic source audit',
 'article_sha256':{p:sha(ROOT/'article'/p) for p in ['Report55.tex','Report55.pdf']},
 'preserved_file_count':len(preserved),'frozen_science_manifest_entries':18,
 'positive_witness_count':len(ws),'full_gate_count':len(gates),'body_gate_count':body,
 'counts':counts,'body_counts':bodycounts,'residual_count':len(d['equalities']),
 'port_count':len(d['ports']),'macro_counts':dict(collections.Counter(m['kind'] for m in d['macros'])),
 'finalizer_verified_gate_by_gate':True,'all_source_gates_and_variables_live':True,
 'degree_upper_bound':degrees[-1],'pure_monomial':'bounds.offset.w^8 bounds.offset.g^4',
 'pure_monomial_coefficient':polys[-1].get((8,4),0),'exact_total_degree':12,
 'actual_maps':len(maps),'actual_radix_threshold':threshold,'radix_factor':2**104,
 'tile_guards':'n=next_n=0','ordinary_input_unshifted':True,
 'all_195_matrices_verified_against_lift_recipe':True,'all_9555_entries_verified':True,
 'matrix_rank_counts':dict(collections.Counter(ranks)),'fixed_contexts':lift['contexts'],
 'principal_pins':pins,'preserved_files':preserved,
 'author_upstream_saved_schedule_or_lean_code_executed':False,
 'checker_sha256':sha(Path(__file__))}
(OUT/'data-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='preserved_files'},indent=2,sort_keys=True))
