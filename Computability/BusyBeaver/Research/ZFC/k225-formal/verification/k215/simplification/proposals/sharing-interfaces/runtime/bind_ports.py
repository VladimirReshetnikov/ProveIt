"""Owned literal parser and source-path audit for maintained formal role graph."""
if not __debug__:raise RuntimeError('Assertions must be enabled')
from pathlib import Path
import re,json,hashlib
import analyze_symbolic as A
D=Path(__file__).parent
s=(D/'reference/K215Decoder.lean').read_text()
def section(name):return s.split('def '+name+' :')[1].split('#[',1)[1].split(']',1)[0]
nodes=[(k,int(a),int(b))for k,a,b in re.findall(r'\.(leaf|fork) (\d+) (\d+)',section('sourceNodes'))]
# Role arrays contain suffix brackets; delimit by following declaration, not first ].
body=s.split('def roles : Array Role := #[',1)[1].split('\n\n',1)[0]
roles=[]
for line in body.splitlines():
 if not line.strip() or line.strip()==']':continue
 m=re.match(r'\s*⟨(\d+), (\d+), \[([^]]*)\], (.*)⟩[,\]]*',line)
 assert m,('unparsed role',line)
 node,q,ctx,es=m.groups();edges=[]
 for e in re.finditer(r'\(\.internal (\d+) (\d+)\)|\(\.primitive (\d+) ⟨(true|false), (\(?-?1\)?), (\d+)⟩\)',es):
  a,b,n,w,d,z=e.groups()
  edges.append(('internal',int(a),int(b))if a is not None else('primitive',int(n),(int(w=='true'),int(d.strip('()')),int(z))))
 assert len(edges)==2
 roles.append((int(node),int(q),tuple(int(x.strip()=='true')for x in ctx.split(',')if x.strip()),edges))
assert(len(nodes),len(roles))==(202,234)
def native(q):return {230:254,102:301,120:302}.get(q,q)
T=A.table(D/'inputs/K215_Formal.tm')
OP={0:'CI',1:'CD',2:'CB',3:'CC',4:'CH'}
def routed(pc,op,arg):
 rid=0;node=201;hist=(1,)
 for b in map(int,pc[:-1]):
  n,q,ctx,es=roles[rid];assert n==node and ctx==hist[-2:]
  assert nodes[n][0]=='fork'
  e=es[b];assert e[0]=='internal';rid=e[1];node=nodes[n][1+b];hist=hist+(b,)
 n,q,ctx,es=roles[rid];assert n==node and ctx==hist[-2:]
 bit=int(pc[-1]);e=es[bit];assert e[0]=='primitive'
 assert nodes[n][0]=='fork' and nodes[n][1+bit]==e[1]
 kind,code,r=nodes[e[1]];assert(kind,OP[code],r)==('leaf',op,0 if op=='CH' else arg), (pc,kind,code,r,op,arg)
 w,d,z=e[2];assert T[native(q),bit]==(w,d,native(z))
 return native(q),rid
sites=json.loads((D/'inputs/K215_Formal.sites.json').read_text());PORTS={pc:routed(pc,op,arg)[0]for pc,op,arg in sites}
assert len(PORTS)==4751
if __name__=='__main__':
 out=dict(status='FORMAL_ROLE_ROUTES_BOUND',sites=len(PORTS),nodes=len(nodes),roles=len(roles),formal_sha256=hashlib.sha256(s.encode()).hexdigest(),ports=PORTS,scope='Literal arrays and RoutedEntry fields audited independently; formal proof not recompiled.')
 r=json.loads((D/'RESIDUAL_RESULT.json').read_text())
 assert len(r['records'])==6176
 assert all(x['port_q']==PORTS[sites[x['site']][0]]for x in r['records'])
 assert len({x['site']for x in r['records']})==4751
 out['finite_prefix_ports_matched']=4751;out['residual_guards_at_bound_port']=6176
 out['orientation']='onl=false; head at final PC bit; left=reverse(pre)++[true]; right=bit::gap::true::plain-box; moved=false'
 (D/'PORT_BINDING.json').write_text(json.dumps(out,separators=(',',':')));print(out['status'],out['sites'])
