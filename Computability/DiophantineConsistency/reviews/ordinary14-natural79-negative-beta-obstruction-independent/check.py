#!/usr/bin/env python3
"""Independent full-source AST and split-natural exact evaluation; no Lean."""
from pathlib import Path
import ast,hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-natural79-negative-beta-obstruction'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b
pin(P/'check.py','30e08353a1490b96da67d036b90d847eec5153f17feaf93a2da091d4e5d03da8')
obs=json.loads(pin(P/'result.json','759e35c0f4c246eeb6e2e38a2fd26e2e2c0f5fa711b52ba5e8e9eb48ddd3a05e'))
split=pin(D/'Lean/DiophantineConsistency/NaturalExpression.lean','0e0923fcc8dde83a1e8099a55e5ec8c804ff2b1648d8376b6c81ac343eac4e4f').decode()
for fragment in ('(.constant a.toNat, .constant (-a).toNat)', '(a.1 + b.1, a.2 + b.2)', '(a.1 + b.2, a.2 + b.1)', '(a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1)'): assert fragment in split
g=json.loads(pin(D/'research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'))
s=pin(D/'research/ordinary14-natural79-corrected-reflection-overlay/source/P79NaturalForcedW.lean.src','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36').decode()
# Parse the literal Lean let block as Python's arithmetic AST. Only variables,
# nonnegative integer literals and binary +,-,* are allowed. This is separate
# from the author's line-regex evaluator and follows the actual source bytes.
block=s.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('-- END LITERAL GRAPH',1)[0]
program=ast.parse('\n'.join(line.strip()[4:].replace(':=','=') for line in block.splitlines() if line.strip()))
assert len(program.body)==79==len(g['source'])
witnesses=['n_J','n_F','n_alpha','n_f','n_i','n_T','n_w','n_s','n_r','n_eta','n_zeta','n_y','n_gamma','n_h'];ports=['beta','K0','MC','MF']
assert g['witnesses']==witnesses and g['fixed_numerals']==ports
for i,n in enumerate(witnesses):assert f'let {n} : Expr (Fin 14) := .var {i}' in s
for i,n in enumerate(ports):assert f'let {n} : Expr (Fin 14) := .constant (p {i})' in s
assert '⟨F0, F1, Fa, Fs, guard, out, qF, C, G, R⟩' in s and g['output']=='out'
v=[1,0,0,2,2,0,0,0,1,0,0,1,0,1];p=[-1,0,3,0]
assert all(x>=0 for x in v) and v[6]==0 and p[0]<0
values=dict(zip(witnesses,v));values.update(zip(ports,p));pairs={n:(x,0) for n,x in zip(witnesses,v)};pairs.update({n:(max(x,0),max(-x,0)) for n,x in zip(ports,p)})
ops={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}
def val(node):
 if isinstance(node,ast.Name):return values[node.id],pairs[node.id],node.id
 if isinstance(node,ast.Constant) and type(node.value)==int and node.value>=0:return node.value,(node.value,0),node.value
 raise AssertionError(ast.dump(node))
for statement,jsonrow in zip(program.body,g['source']):
 assert isinstance(statement,ast.Assign) and len(statement.targets)==1 and isinstance(statement.targets[0],ast.Name)
 name=statement.targets[0].id;node=statement.value;assert isinstance(node,ast.BinOp) and type(node.op) in ops and name not in values
 a,(ap,an),aname=val(node.left);b,(bp,bn),bname=val(node.right);op=ops[type(node.op)];assert [name,op,aname,bname]==jsonrow
 if op=='+':integer=a+b;pair=(ap+bp,an+bn)
 elif op=='-':integer=a-b;pair=(ap+bn,an+bp)
 else:integer=a*b;pair=(ap*bp+an*bn,ap*bn+an*bp)
 assert pair[0]-pair[1]==integer
 values[name]=integer;pairs[name]=pair
assert values['q']==0 and [values[n] for n in ('F0','F1','Fa','Fs','guard')]==[1]*5 and values['out']==0
assert pairs['out'][0]==pairs['out'][1]
selected=obs['selected_graph_values'];assert all(values[n]==value for n,value in selected.items())
assert values['V']==-1 and values['R']==1 and values['Dstar']==0
assert obs['ports_by_name']==dict(zip(ports,p)) and obs['natural_witness_by_name']==dict(zip(witnesses,v))
print(json.dumps({'scope':'separately parsed 79 source rows and exact integer/split-pair computation; not Lean elaboration or fixed-compact-port evidence','all_source_rows_match_json':True,'source_rows':len(program.body),'beta':p[0],'w':v[6],'q':values['q'],'factors':[values[n] for n in ('F0','F1','Fa','Fs','guard')],'output':values['out'],'split_natural_output_sides_equal':True,'split_side_bit_length':pairs['out'][0].bit_length(),'positive_or_fixed_beta_case_checked':False},indent=2,sort_keys=True))
