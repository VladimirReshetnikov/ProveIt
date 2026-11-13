from pathlib import Path
import hashlib,itertools,json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-eta-zeta-natural-unit-norm-structural-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-eta-zeta-natural-unit-norm-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text()); src=(P/'EtaZetaNaturalUnitGraph.lean.src').read_text();bridge=(P/'EtaZetaNaturalUnitBridge.lean.src').read_text()
assert len(g['source'])==85
for idx,x in enumerate(g['witnesses']):assert f'  let {x} : Expr (Fin 13) := .var {idx}\n' in src
for idx,x in enumerate(g['fixed_numerals']):assert f'  let {x} : Expr (Fin 13) := .constant (p {idx})\n' in src
for n,op,a,b in g['source']:assert f'  let {n} := {a} {op} {b}\n' in src,(n,op,a,b)
assert '⟨A0, A1, Fa, Fs, out, g72, qm, Z, X, s, kbase, U, a, c, Dstar, n_y, V, n_f, I, ell, Delta⟩' in src
# Hash-consed exact expression syntax, not algebraic equality: this checks
# proposed rfl shapes including grouping and repeated subexpressions.
tab={}
def node(*xs):
 if xs not in tab:tab[xs]=len(tab)
 return tab[xs]
def nat(n):return node('nat',n)
def add(x,y):return node('+',x,y)
def sub(x,y):return node('-',x,y)
def mul(x,y):return node('*',x,y)
ops={'+':add,'-':sub,'*':mul};d={}
for i,n in enumerate(g['witnesses']):d[n]=node('var',i)
for i,n in enumerate(g['fixed_numerals']):d[n]=node('port',i)
for n,op,a,b in g['source']:d[n]=ops[op](d[a] if isinstance(a,str) else nat(a),d[b] if isinstance(b,str) else nat(b))
one=nat(1);three=nat(3);four=nat(4);b,z,x,s,k,U,a,c,root,y,vv,f,I,ell,delta=(d[j] for j in ['qm','Z','X','s','kbase','U','a','c','Dstar','n_y','V','n_f','I','ell','Delta'])
q=add(one,b);Y=mul(mul(q,mul(q,q)),s);E=mul(mul(x,Y),mul(Y,k))
first=add(one,sub(mul(z,z),mul(mul(b,b),add(one,mul(E,add(E,k))))))
main=add(one,sub(mul(root,root),mul(mul(U,U),add(one,mul(add(add(three,mul(four,a)),mul(a,a)),mul(c,c))))))
Q=mul(add(add(three,mul(four,a)),mul(a,a)),sub(mul(f,f),one))
aux=sub(mul(y,y),mul(Q,sub(mul(y,y),mul(vv,vv))))
strong=add(one,sub(mul(I,I),Q))
assert d['F0']==first and d['F1']==main and d['Fa']==aux and d['Fs']==strong
assert d['ell']==E and d['r0']==sub(sub(k,d['R']),one)
assert d['out']==sub(mul(mul(mul(first,main),aux),strong),one)
assert d['A0']==sub(mul(z,z),mul(mul(b,b),add(one,mul(ell,add(ell,k)))))
assert d['A1']==sub(mul(root,root),mul(mul(U,U),add(one,mul(delta,mul(c,c)))))
assert d['g72']==sub(mul(I,I),mul(delta,sub(mul(f,f),one)))
for b0,z0,x0,s0,k0 in itertools.product(range(4),repeat=5):
 q0=1+b0;y0=q0**3*s0;e0=x0*y0*y0*k0
 assert (1+z0*z0-b0*b0*(1+e0*(e0+k0)))%4!=3
for snippet in ['1+zv^2-bv^2*(1+ev*(ev+kv))','exact first_bad bv zv xv sv kv hn','theorem first_pattern','theorem main_pattern','theorem aux_pattern','theorem strong_pattern','theorem signed_norms']:
 assert snippet in bridge,snippet
print(json.dumps({'all_85_graph_rows_and_export_order_checked':True,'first_main_aux_strong_exact_expression_shapes_checked':True,'k_and_r0_exact_structures_checked':True,'mod4_first_factor_cases':1024,'arbitrary_signed_ports_permitted':True,'lean_executed':False},sort_keys=True,indent=2))
