#!/usr/bin/env python3
"""Independent candidate graph, exact byte ports and degree audit, no Lean."""
import collections,gzip,hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2]; P=D/'research/current2011-ordinary71-60-candidate'; Q=D/'research/current2011-ordinary67-94-candidate'; prime=1000000007
def sha(b):return hashlib.sha256(b).hexdigest()
def need(v,s):
    if not v:raise RuntimeError(s)
gb=(P/'polynomial.json').read_bytes();g=json.loads(gb)
need(sha(gb)=='3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27' and sha((P/'check.py').read_bytes())=='177975d7326466e7b02abcda8831d359a2a50552212d7835f062272705418ae5' and sha((P/'result.json').read_bytes())=='06ff1bfcf9af75972b0e9e47796ade7bbdd9fc70f614705754526073888d6d7f','frozen author inputs')
oldb=(P/'history/initial/polynomial.json').read_bytes();need(sha(oldb)=='d4d586406f56d1a179a8de199bf71fbcc86972d8817c8360322937a7bd60c358','initial graph');old=json.loads(oldb)
old['coefficient_binding']['path']='../fourteen-nonzero-spheres/coefficients/'
need(g==old,'unexpected graph change beyond corrected port path')
pb=(Q/'polynomial.json').read_bytes();need(sha(pb)=='d76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb','parent hash');p=json.loads(pb)
need(g['witness_domain']=='strictly positive integers' and g['witnesses']==['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma'] and g['fixed_numerals']==['beta','K0','MC','MF'],'input interface')
need(g['source'][:61]==p['source'][:61] and g['parent_graph_sha256']==sha(pb) and g['coefficient_binding']['ports']==p['coefficient_binding']['ports'],'prefix/parent ports')
tail=[['P2','*','N0','N0'],['Na2','*','Na','Na'],['QW','*','N1','Nt'],['rQW','-','QW',1],['rQW2','*','rQW','rQW'],['strong2','*','strong_residual','strong_residual'],['sum1','+','P2','Na2'],['sum2','+','sum1','rQW2'],['sum3','+','sum2','strong2'],['polynomial','-','sum3',2]]
need(g['source'][61:]==tail and g['output']=='polynomial','complete candidate tail')
rows={x[0]:x for x in g['source']}
required={'a':['a','+','E','Y'],'four_a':['four_a','*',4,'a'],'H':['H','+','four_a',3],
 'a2':['a2','*','a','a'],'Delta':['Delta','+','a2','H'],'ac':['ac','*','a','c'],
 'main_base':['main_base','+','X','ac'],'gammaH':['gammaH','*','gamma','H'],
 'main_root':['main_root','+','main_base','gammaH'],'main_square':['main_square','*','main_root','main_root'],
 'c2':['c2','*','c','c'],'Dc2':['Dc2','*','Delta','c2'],'N1':['N1','-','main_square','Dc2'],
 'I':['I','*','i','c2'],'I2':['I2','*','I','I'],'f2m1':['f2m1','-','f2',1],
 'Aaux':['Aaux','*','Delta','f2m1'],'V2':['V2','*','V','V'],'y2':['y2','*','y','y'],
 'aux_gap':['aux_gap','-','V2','y2'],'aux_term':['aux_term','*','Aaux','aux_gap'],
 'Na':['Na','+','aux_term','y2'],'strong_residual':['strong_residual','-','I2','Aaux']}
need(all(rows.get(k)==v for k,v in required.items()),'factor/cancellation rows')
ports=g['coefficient_binding']['ports'];need(g['coefficient_binding']['path']=='../fourteen-nonzero-spheres/coefficients/','coefficient relative path')
need(set(ports)==set(g['fixed_numerals']),'port metadata keys'); values={};total=0
for name,meta in ports.items():
    path=(P/g['coefficient_binding']['path']/meta['file']).resolve();rawgz=path.read_bytes();data=gzip.decompress(rawgz)
    need(sha(rawgz)==meta['gzip_sha256'] and sha(data)==meta['raw_sha256'] and len(data)==meta['raw_bytes'] and int.from_bytes(data,'big').bit_length()==meta['bits'],'port '+name)
    total+=len(data);values[name]=int.from_bytes(data,'big')%prime
need(total==g['coefficient_binding']['raw_bytes']==47313,'port bytes')
def op_poly(a,b,op):
    n=len(a)+len(b)-1 if op=='*' else max(len(a),len(b));v=[0]*n
    if op=='*':
        for i,x in enumerate(a):
            for j,y in enumerate(b):v[i+j]=(v[i+j]+x*y)%prime
    else:
        for i,x in enumerate(a):v[i]=(v[i]+x)%prime
        for i,y in enumerate(b):v[i]=(v[i]+(y if op=='+' else -y))%prime
    while len(v)>1 and v[-1]==0:v.pop()
    return v
deg={v:1 for v in g['witnesses']};deg.update({v:0 for v in g['fixed_numerals']});polys={v:[0,1] for v in g['witnesses']};polys.update({k:[v] for k,v in values.items()}); edges={};counts=collections.Counter()
for name,op,a,b in g['source']:
    need(name not in deg and op in ('+','-','*') and all(type(x)==int or x in deg for x in (a,b)),'row topology')
    x=0 if type(a)==int else deg[a];y=0 if type(b)==int else deg[b];deg[name]=x+y if op=='*' else max(x,y)
    if name=='N1':
        need((deg['X'],deg['a'],deg['c'],deg['H'],deg['gamma'])==(2,6,5,6,1),'N1 degree assumptions')
        deg[name]=max(2*deg['X'],deg['X']+deg['a']+deg['c'],deg['gamma']+deg['H']+max(deg['X'],deg['a']+deg['c']),2*deg['gamma']+2*deg['H'],deg['H']+2*deg['c'])
    polys[name]=op_poly([a%prime] if type(a)==int else polys[a],[b%prime] if type(b)==int else polys[b],op);edges[name]=(a,b);counts[op]+=1
todo=[g['output']];used=set();leaves=set()
while todo:
    n=todo.pop()
    if n in edges:
        if n not in used:used.add(n);todo.extend(edges[n])
    elif type(n)==str:leaves.add(n)
need(len(used)==len(g['source'])==g['operations']==71 and leaves==set(g['witnesses']+g['fixed_numerals']) and dict(counts)=={'*':38,'+':19,'-':14},'liveness/count')
ray=polys[g['output']];need(deg['polynomial']==len(ray)-1==60 and ray[-1]==176981100,'exact degree')
out=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True)
need(out.returncode==0 and out.stdout==(P/'result.json').read_bytes(),'author check rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_GRAPH_AUDIT','graph_sha256':sha(gb),'rows':len(used),'operation_counts':dict(counts),'live_inputs':len(leaves),'port_raw_bytes':total,'degree_upper':deg['polynomial'],'ray_degree':len(ray)-1,'ray_leading_coefficient_mod_1000000007':ray[-1],'scope':'Exact current-byte graph and degree only; candidate zero equivalence, Lean model theorem and serialized-port binding remain separate.'},indent=2,sort_keys=True))
