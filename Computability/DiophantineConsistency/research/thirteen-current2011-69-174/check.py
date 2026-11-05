#!/usr/bin/env python3
"""Retarget two audited gate lists and compare with Lean source; no Lean run."""
import ast, collections, gzip, hashlib, json, re, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B')
D = Path(__file__).resolve().parents[2]
def need(value, message):
    if not value: raise RuntimeError(message)
def digest(data): return hashlib.sha256(data).hexdigest()
def read(path, expected):
    data=(D/path).read_bytes(); need(digest(data)==expected, 'source drift '+str(path)); return data

carrier=read('research/thirteen-current2011-carrier-split-draft/src/DiophantineConsistency/ModelThirteenCarrierCore.lean','394d7b25748bb93ac285f6bac763d948364ce12277a6ccf999dc6915f3864dc9').decode()
base=json.loads(read('research/thirteen-unit-sphere96/polynomial.json','48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1'))
old={69:json.loads(read('research/thirteen-variable-independent/polynomial69.json','3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f'))}
ports=base['coefficient_binding']['ports']; need(list(sorted(ports))==['K0','MC','MF','beta'],'port names')
rawports={}
for name,meta in ports.items():
    gz=(D/'research/thirteen-unit-sphere96/coefficients'/meta['file']).read_bytes(); raw=gzip.decompress(gz)
    need(digest(gz)==meta['gzip_sha256'] and digest(raw)==meta['raw_sha256'] and len(raw)==meta['raw_bytes'],'port '+name)
    rawports[name]=int.from_bytes(raw,'big')

class Canon:
    def __init__(self): self.nodes=[]; self.ids={}
    def node(self,k):
        if k not in self.ids: self.ids[k]=len(self.nodes); self.nodes.append(k)
        return self.ids[k]
    def num(self,n): return self.node(('n',n))
    def add(self,a,b,sign=1):
        terms=collections.Counter(); const=0
        for x,m in ((a,1),(b,sign)):
            node=self.nodes[x]
            if node[0]=='n': const+=m*node[1]
            elif node[0]=='sum':
                const+=m*node[2]
                for k,v in node[1]: terms[k]+=m*v
            else: terms[x]+=m
        v=tuple(sorted((k,v) for k,v in terms.items() if v))
        if not v: return self.num(const)
        if len(v)==1 and v[0][1]==1 and const==0: return v[0][0]
        return self.node(('sum',v,const))
    def mul(self,a,b):
        out=[]
        for x in (a,b):
            n=self.nodes[x]; out.extend(n[1] if n[0]=='mul' else (x,))
        return self.node(('mul',tuple(sorted(out))))
    def op(self,op,a,b): return self.mul(a,b) if op=='*' else self.add(a,b,1 if op=='+' else -1)
    def parse(self,text,env):
        text=re.sub(r'Expr\.constant\s*\(p\s+(\d+)\)',lambda m:'port'+m.group(1),text)
        def go(x):
            if isinstance(x,ast.Name): need(x.id in env,'unknown '+x.id); return env[x.id]
            if isinstance(x,ast.Constant) and type(x.value)==int: return self.num(x.value)
            if isinstance(x,ast.BinOp):
                if isinstance(x.op,ast.Pow):
                    need(isinstance(x.right,ast.Constant) and x.right.value in (2,3),'power')
                    z=go(x.left); out=z
                    for _ in range(1,x.right.value):out=self.mul(out,z)
                    return out
                op={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}.get(type(x.op)); need(op is not None,'op');return self.op(op,go(x.left),go(x.right))
            raise RuntimeError('AST '+ast.dump(x))
        return go(ast.parse(text.replace('^','**'),mode='eval').body)

prime=1000000007
def polyop(a,b,op):
    out=[0]*(len(a)+len(b)-1 if op=='*' else max(len(a),len(b)))
    if op=='*':
        for i,x in enumerate(a):
            for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%prime
    else:
        for i,x in enumerate(a):out[i]=(out[i]+x)%prime
        for i,y in enumerate(b):out[i]=(out[i]+(1 if op=='+' else -1)*y)%prime
    while len(out)>1 and out[-1]==0:out.pop()
    return out

block=carrier.split('def front13 (p : Fin 4 → ℤ)',1)[1].split('/-- The 13/69/174',1)[0]
lets=re.findall(r'\n  let (\w+)(?:\s*:\s*Expr\s*\(Fin\s+13\))?\s*:=\s*(.*?)(?=\n  let |\n  final )',block,re.S)
final=' '.join(block.split('\n  final ',1)[1].split())
need(final=='(tau ^ 2 - ell * (ell + k)) (D ^ 2 - delta * c ^ 2) (delta * (b * i * c ^ 2)) f delta (V ^ 2 - y ^ 2) y (b * i * c ^ 2)','front final')
results={}
for profile,original in old.items():
    graphpath=Path(__file__).resolve().parent/f'polynomial{profile}.json'
    need(digest(graphpath.read_bytes())=='8667df5fe2f33c14a4280972336611218ebfb68883347bbfbb9215e5ab72a517','graph pin')
    g=json.loads(graphpath.read_text())
    oldpaths={69:('research/thirteen-variable-independent/polynomial69.json','3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f')}
    need(g['source']==original['source'] and g['witnesses']==original['witnesses'] and
         g['fixed_numerals']==original['fixed_numerals'] and g['output']==original['output'] and
         g['operation_counts']==original['operation_counts'] and g['operations']==profile and
         g['schema']=='literal_integer_arithmetic_dag_v1' and g['witness_domain']=='strictly positive integers' and
         g['exact_degree']==174 and (g['source_graph'],g['source_graph_sha256'])==oldpaths[profile] and
         g['coefficient_binding']['raw_bytes']==base['coefficient_binding']['raw_bytes'] and
         g['coefficient_binding']['ports']==ports and g['coefficient_binding']['path']=='../thirteen-unit-sphere96/coefficients/',
         'retargeted graph structure/ports')
    witnesses=g['witnesses']; fixed=g['fixed_numerals']; need(witnesses==['J','F','alpha','f','i','T','s','w','n','eta','zeta','m','gamma'] and fixed==['beta','K0','MC','MF'],'inputs')
    c=Canon(); env={f'port{i}':c.node(('v',v)) for i,v in enumerate(fixed)}
    for name,expr in lets:
        expr=' '.join(expr.split()); m=re.fullmatch(r'\.var (\d+)',expr)
        if m: need(witnesses[int(m.group(1))]==name,'witness index');env[name]=c.node(('v',name))
        else: env[name]=c.parse(expr,env)
    for name,expr in {'P':'tau^2-ell*(ell+k)','Q':'D^2-delta*c^2','S':'delta*(b*i*c^2)', 'gap':'V^2-y^2','t':'b*i*c^2'}.items():env[name]=c.parse(expr,env)
    wrapper=re.search(r'def expressionAt69 \(p : Fin 4 → ℤ\) : Expr \(Fin 13\) :=\s*front13 p fun P Q S f delta gap y _ =>\s*([^\n]+)',carrier)
    need(wrapper is not None,'wrapper missing');expr=wrapper.group(1)
    need(expr=='P * Q * (S ^ 2 * gap + y ^ 2) * (delta * f ^ 2 - S ^ 2) - delta','complete 69 wrapper')
    sourceout=c.parse(expr,env)
    values={x:c.node(('v',x)) for x in witnesses+fixed}; deg={x:1 for x in witnesses};deg.update({x:0 for x in fixed});polys={x:[0,1] for x in witnesses};polys.update({x:[rawports[x]%prime] for x in fixed});edges={};counts=collections.Counter()
    rows={row[0]:row for row in g['source']}
    expected_rows={'a':['a','+','E','Y'],'four_a':['four_a','*',4,'a'],'H':['H','+','four_a',3],
      'a2':['a2','*','a','a'],'Delta':['Delta','+','a2','H'],'ac':['ac','*','a','c'],
      'main_base':['main_base','+','X','ac'],'gammaH':['gammaH','*','gamma','H'],
      'main_root':['main_root','+','main_base','gammaH'],'main_square':['main_square','*','main_root','main_root'],
      'c2':['c2','*','c','c'],'Dc2':['Dc2','*','Delta','c2'],'N1':['N1','-','main_square','Dc2']}
    need(all(rows.get(k)==v for k,v in expected_rows.items()),'main norm cancellation shape')
    for name,op,a,b in g['source']:
        need(name not in values and op in ('+','-','*') and all(type(x)==int or x in values for x in (a,b)),'topology')
        def v(x):return c.num(x) if type(x)==int else values[x]
        values[name]=c.op(op,v(a),v(b));counts[op]+=1;edges[name]=(a,b)
        da=deg[a] if type(a)==str else 0;db=deg[b] if type(b)==str else 0;deg[name]=da+db if op=='*' else max(da,db)
        if name=='N1':
            need((deg['X'],deg['a'],deg['c'],deg['H'],deg['gamma'])==(2,6,5,6,1),'degree cancellation assumptions')
            need([name,op,a,b]==['N1','-','main_square','Dc2'],'N1 cut');deg[name]=18
        polys[name]=polyop(polys[a] if type(a)==str else [a%prime],polys[b] if type(b)==str else [b%prime],op)
    used=set(); leaves=set(); stack=[g['output']]
    while stack:
        name=stack.pop()
        if name in edges:
            if name not in used:used.add(name);stack.extend(edges[name])
        elif type(name)==str:leaves.add(name)
    need(len(used)==len(g['source'])==profile and leaves==set(witnesses+fixed) and dict(counts)==g['operation_counts'],'liveness/count')
    need(sourceout==values[g['output']],'Lean syntax does not match retargeted graph '+str(profile))
    upper=deg[g['output']];ray=polys[g['output']];need(len(ray)-1==upper and ray[-1]!=0,'degree '+str(profile))
    results[str(profile)]={'graph_sha256':digest(graphpath.read_bytes()),'rows':len(used),'counts':dict(counts),'source_equal_mod_associativity_commutativity':True,'degree_upper':upper,'ray_degree':len(ray)-1,'ray_leading_coefficient_mod_1000000007':ray[-1]}
print(json.dumps({'status':'PASS','scope':'External source/graph comparison and exact degree for recorded current2011 bytes; Lean does not parse graph JSON and byte-to-Lean-port linkage is separate.','prime':prime,'results':results},indent=2,sort_keys=True))
