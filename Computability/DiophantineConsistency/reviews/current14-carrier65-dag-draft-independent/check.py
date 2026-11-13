#!/usr/bin/env python3
import hashlib,json,re,sys
from collections import Counter
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-dag-draft';graph=root/'research/carrier65-independent/INCOMING_CARRIER65.json';data=json.loads(graph.read_text());lean=(p/'Current14Carrier65DAG.lean').read_text();sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(graph)=='bf58ed6600eee34d86a802a992e3fd9b999e1835b57a5a83734a40073e1658a7' and sha(graph) in lean
inputs=['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma'];ports=['beta','K0','MC','MF'];assert data['witnesses']==inputs and data['fixed_numerals']==ports
body=lean.split('def nodes :',1)[1].split('def output',1)[0];lines=re.findall(r'^\s*\.(input|constant|literal|add|sub|mul)\s+(.+?)\s*,?\s*--\s*(\d+):\s*(\w+)\s*$',body,re.M);assert len(lines)==86
rows=[]
for i,(op,args,ix,name) in enumerate(lines):
 assert int(ix)==i
 if op in ('input','constant'):
  m=re.fullmatch(r'⟨(\d+), by decide⟩',args.rstrip(',').strip());assert m;args=[int(m[1])]
 else: args=[int(x) for x in args.rstrip(',').split()]
 rows.append((op,args,name))
assert rows[:14]==[('input',[i],n) for i,n in enumerate(inputs)] and rows[14:18]==[('constant',[i],n) for i,n in enumerate(ports)] and rows[18:21]==[('literal',[i],str(i)) for i in (1,3,4)]
idx={n:i for i,(_,_,n) in enumerate(rows)};idx.update({'1':18,'3':19,'4':20});ops={'+':'add','-':'sub','*':'mul'}
for i,(name,op,a,b) in enumerate(data['source'],21):
 assert rows[i]==(ops[op],[idx[str(a)],idx[str(b)]],name) and all(j<i for j in rows[i][1])
assert idx[data['output']]==85 and Counter(x[0] for x in rows[21:])=={'add':16,'sub':12,'mul':37}
c=re.search(r'def consumers : List ℕ :=\s*\[([^]]+)\]',lean).group(1);cons=[int(x.strip()) for x in c.split(',')];assert len(cons)==85
for i,j in enumerate(cons):assert i<j<=85 and i in rows[j][1] and j==min(k for k in range(i+1,86) if i in rows[k][1] and rows[k][0] in ('add','sub','mul'))
# Independently transcribe Carrier65.core/value to a structural expression with multiplication associativity normalized.
def atom(n):return ('atom',n)
def add(a,b):return ('add',a,b)
def sub(a,b):return ('sub',a,b)
def mul(*xs):
 out=[]
 for x in xs: out.extend(x[1:] if x[0]=='mul' else [x])
 return ('mul',*out)
def sq(x):return mul(x,x)
expr={}
for i,(op,args,name) in enumerate(rows):
 if op in ('input','constant'):x=atom(name)
 elif op=='literal':x=atom(str(args[0]))
 else:x={'add':add,'sub':sub,'mul':mul}[op](*(expr[rows[j][2]] for j in args))
 expr[name]=x
v={n:atom(n) for n in inputs+ports};one,three,four=map(atom,('1','3','4'));b=mul(v['beta'],v['J']);q=add(b,one);C=sub(sub(q,v['F']),v['alpha']);X=mul(v['w'],q);Y=mul(v['s'],q,q,q);E=mul(X,Y);k=add(v['eta'],v['zeta']);ell=mul(E,k,Y);c=add(mul(k,Y),v['eta']);a=add(E,Y);H=add(mul(four,a),three);delta=add(sq(a),H);D=add(add(X,mul(a,c)),mul(v['gamma'],H));rank=add(mul(add(mul(b,sub(q,v['F'])),v['alpha']),sub(sq(q),one)),mul(add(v['MC'],mul(q,v['MF'])),v['J']));tau=sub(add(mul(E,v['n']),k),rank);V=sub(mul(sq(v['f']),sub(mul(c,v['T']),rank)),c);S=mul(v['i'],delta,c,c);P=sub(sq(tau),mul(ell,add(ell,k)));Q=sub(sq(D),mul(delta,c,c));U=add(mul(sq(S),sub(sq(V),sq(v['y']))),sq(v['y']));W=sub(add(mul(add(v['K0'],v['w']),C),sub(q,v['F'])),mul(v['z'],b));Z=sub(mul(delta,sq(v['f'])),sq(S));value=sub(mul(P,Q,U,W,Z),delta)
for name,x in [('q',q),('C',C),('X',X),('Y',Y),('E',E),('k',k),('ell',ell),('c',c),('a',a),('H',H),('Delta',delta),('main_root',D),('R',rank),('tau',tau),('V',V),('normalized_S',S),('N0',P),('N1',Q),('Na',U),('Nt',W),('scaled_Ns',Z),('polynomial',value)]:assert expr[name]==x,name
assert 'value nodes output p v = Carrier65.value p v' in lean and 'theorem live_operation_count' in lean
print(json.dumps({'status':'PASS_SOURCE_REVIEW','nodes':86,'gates':65,'consumer_entries':85,'counts':{'add':16,'sub':12,'mul':37},'graph_sha256':sha(graph),'source_sha256':sha(p/'Current14Carrier65DAG.lean'),'generator_sha256':sha(p/'generate.py'),'scope':'external structural review with associativity normalization; Lean semantic proof unverified'},indent=2))
