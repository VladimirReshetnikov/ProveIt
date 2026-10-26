#!/usr/bin/env python3
"""Independent finite audit; imports no producer or search program.

Checks literal source mutation, all inherited unit/affine pivots, acyclic
projection identities, binary arithmetic graphs, exact degrees, actual input
occurrence, and coefficient-height bounds. Arithmetic semantic proofs are
retained separately and are not certified by testing finitely many inputs.
"""
import argparse,copy,hashlib,json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
def demand(x,s):
    if not x:raise ValueError(s)
def load(p):return json.loads(p.read_text())
def poly(t):
    p={}
    for c,m in t:
        m=tuple(sorted(m));p[m]=p.get(m,0)+c
    return {m:c for m,c in p.items() if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def plus(a,b):
    p=dict(a)
    for m,c in b.items():p[m]=p.get(m,0)+c
    return {m:c for m,c in p.items() if c}
def times(a,b):
    p={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(sorted(m+n));p[key]=p.get(key,0)+c*d
    return {m:c for m,c in p.items() if c}
def replace(p,v,r):
    out={}
    for m,c in p.items():
        t={():c}
        for x in m:t=times(t,r if x==v else {(x,):1})
        out=plus(out,t)
    return out
def eliminate(rows,ri,v,rest):
    c=rows[ri].get((v,),0)
    demand(abs(c)==1,'nonunit pivot')
    demand(all(v not in m for m in rows[ri] if m!=(v,)),'nonlinear pivot')
    want={m:-a*c for m,a in rows[ri].items() if m!=(v,)}
    demand(want==rest,'restoration differs from actual pivot')
    new=[replace(r,v,rest) for r in rows]
    demand(not new[ri],'pivot survived')
    return new
def cut(data,rows,rr,vv):
    rename={v:i for i,v in enumerate(vv)}
    demand(all(v in rename for j in rr for m in rows[j] for v in m),'discarded coordinate occurs')
    return {'variables':[data['variables'][v] for v in vv],
            'residuals':[{'label':data['residuals'][j]['label'],'terms':terms({tuple(rename[v] for v in m):c for m,c in rows[j].items()})} for j in rr]}
def mathdata(d):return {k:d[k] for k in ('variables','residuals')}

def replay_stage(d,parent):
    cert=load(parent/'projection_certificate.json');rows=[poly(r['terms']) for r in d['residuals']]
    for s in cert['steps']:rows=eliminate(rows,s['row_id'],s['variable'],poly(s['restoration']))
    kept=cert['retained_original_rows']
    demand(all(not rows[j] for j in set(range(len(rows)))-set(kept)),'nonzero omitted row')
    out=cut(d,rows,kept,cert['retained_original_variables']);rows=[poly(r['terms']) for r in out['residuals']]
    for v,s in load(parent/'translation_certificate.json')['shifts']:
        rows=[replace(r,v,{(v,):1,():s}) for r in rows]
    out['residuals']=[{'label':r['label'],'terms':terms(p)} for r,p in zip(out['residuals'],rows)]
    return out

def replay_affine(d,parent):
    cert=load(parent/'affine_compact_certificate.json');rows=[poly(r['terms']) for r in d['residuals']]
    for op in cert['operations']:
        typ=op['type']
        if typ=='row_add':rows[op['target']]=plus(rows[op['target']],{m:op['multiple']*c for m,c in rows[op['source']].items()})
        elif typ=='translation':
            v=op['variable'];rows=[replace(r,v,{(v,):1,():op['delta']}) for r in rows]
        elif typ=='shear':rows=[replace(r,op['variable'],poly(op['restoration'])) for r in rows]
        elif typ=='projection':rows=eliminate(rows,op['row'],op['variable'],poly(op['restoration']))
        else:raise ValueError('unsupported inherited operation')
    kept=cert['retained_rows']
    demand(all(not rows[j] for j in set(range(len(rows)))-set(kept)),'nonzero omitted affine row')
    return cut(d,rows,kept,cert['retained_variables'])

def check_source():
    parent=ROOT/'parent166';original=load(parent/'factored_source.json')
    # First validate the independent replay against the retained old endpoint.
    stage=replay_stage(original,parent)
    demand(stage==mathdata(load(parent/'parent_stage.json')),'original stage replay differs')
    demand(replay_affine(stage,parent)==mathdata(load(parent/'parent_compact229.json')),'original affine replay differs')
    d=copy.deepcopy(original);names={v['name']:i for i,v in enumerate(d['variables'])}
    W,A,q,z,L,u,v=[names[n] for n in ['shared.W','shared.A','pow2.output','shared.Zminus1','frame.L','free_A.u','free_A.v']]
    labels=[r['label'] for r in d['residuals']];fi=labels.index('shared.frame_definition');ci=labels.index('free_A.cofinal_constructor')
    f=poly(d['residuals'][fi]['terms']);demand(f.get((W,))==1,'frame coefficient')
    oldW0={m:-c for m,c in f.items() if m!=(W,)};demand(all(W not in m for m in oldW0),'recursive frame')
    demand(poly(d['residuals'][ci]['terms'])=={(A,):1,(L,L):-1,(u,u):-1,(v,v):-1},'old center row changed')
    d['residuals'][fi]['terms']=terms(plus({(W,):1},times({(q,):-1},oldW0)))
    d['residuals'][ci]['terms']=terms({(A,):1,(L,L):-1,(z,z):-8,(z,):-8,():-2})
    out=replay_affine(replay_stage(d,parent),parent)
    dead={i for i,vv in enumerate(out['variables']) if vv['name'] in ('free_A.u','free_A.v')};demand(len(dead)==2,'private center count')
    rows=[poly(r['terms']) for r in out['residuals']]
    out=cut(out,rows,list(range(len(rows))),[i for i in range(len(out['variables'])) if i not in dead])
    demand(out==mathdata(load(ROOT/'source227.json')),'new source differs')
    return {'old_variables':229,'new_variables':227,'inherited_unit_pivots':208,'source_replay':'PASS'}

def check_projection(source,p):
    defs={};used=set()
    for pivot in p['pivots']:
        ri,v=pivot['row'],pivot['variable'];rest=poly(pivot['restoration'])
        demand(ri not in used and v not in defs,'duplicate pivot')
        row=poly(source['residuals'][ri]['terms']);co=row.get((v,),0)
        demand(abs(co)==1 and all(v not in m for m in row if m!=(v,)),'literal pivot is not monic')
        demand({m:-co*c for m,c in row.items() if m!=(v,)}==rest,'literal unit restoration changed')
        defs[v]=rest;used.add(ri)
    free=[v for v in range(len(source['variables'])) if v not in defs]
    kept=[r for r in range(len(source['residuals'])) if r not in used]
    demand(free==p['free'] and kept==p['retained_rows'],'source partition differs')
    visited=set();active=set()
    def visit(v):
        if v in visited:return
        demand(v not in active,'cyclic definition')
        active.add(v)
        if v in defs:
            for m in defs[v]:
                for w in m:visit(w)
        active.remove(v);visited.add(v)
    for v in range(len(source['variables'])):visit(v)
    return defs

def audit_graph(source,p,g,c,metrics):
    defs=check_projection(source,p);nodes=g['nodes'];nvars=len(p['free']);registry={}
    demand(g['domain']=='unrestricted integers','wrong domain')
    demand(g['variables']==[source['variables'][v]['name'] for v in p['free']],'free names differ')
    for i,n in enumerate(nodes):
        demand(n[0] in ('const','input','add','mul'),'unknown graph operation')
        if n[0] in ('add','mul'):demand(len(n)==3 and 0<=n[1]<i and 0<=n[2]<i,'non-topological graph')
        elif n[0]=='input':demand(len(n)==2 and 0<=n[1]<nvars,'invalid input')
        else:demand(len(n)==2 and type(n[1]) is int,'invalid literal')
        demand(tuple(n) not in registry,'duplicate hash-consed node');registry[tuple(n)]=i
    def lookup(t):
        demand(t in registry,'missing required arithmetic node');return registry[t]
    def constant(k):return lookup(('const',k))
    def combine(op,a,b):
        ca=nodes[a][1] if nodes[a][0]=='const' else None;cb=nodes[b][1] if nodes[b][0]=='const' else None
        if ca is not None and cb is not None:return constant(ca+cb if op=='add' else ca*cb)
        if op=='add':
            if ca==0:return b
            if cb==0:return a
        else:
            if ca==0 or cb==0:return constant(0)
            if ca==1:return b
            if cb==1:return a
        return lookup((op,*sorted((a,b))))
    roots=g['source_coordinate_roots'];demand(len(roots)==len(source['variables']),'restoration list length')
    for i,v in enumerate(p['free']):demand(roots[v]==lookup(('input',i)),'input restoration differs')
    def expression(pol):
        s=constant(0)
        for m,co in sorted(pol.items()):
            t=constant(co)
            for v in m:t=combine('mul',t,roots[v])
            s=combine('add',s,t)
        return s
    for v,pol in defs.items():demand(roots[v]==expression(pol),'unit definition graph differs')
    want_res=[expression(poly(source['residuals'][i]['terms'])) for i in p['retained_rows']]
    demand(want_res==g['residual_roots'],'residual graph differs')
    output=constant(0)
    for r in want_res:output=combine('add',output,combine('mul',r,r))
    demand(output==g['output'],'sum of squares output differs')
    degree=[];bits=[]
    for n in nodes:
        op=n[0]
        if op=='input':degree.append(1);bits.append(0)
        elif op=='const':degree.append(-1 if n[1]==0 else 0);bits.append((abs(n[1])-1).bit_length() if n[1] else 0)
        else:
            a,b=n[1:]
            degree.append(max(degree[a],degree[b]) if op=='add' else (degree[a]+degree[b] if min(degree[a],degree[b])>=0 else -1))
            bits.append(max(bits[a],bits[b])+1 if op=='add' else bits[a]+bits[b])
    dc=c['degree'];mod=dc['modulus'];ray=dc['ray'];demand(len(ray)==nvars,'ray dimension')
    leading=[]
    for i,n in enumerate(nodes):
        if n[0]=='input':v=ray[n[1]]
        elif n[0]=='const':v=n[1]
        elif n[0]=='mul':v=leading[n[1]]*leading[n[2]]
        else:v=sum(leading[j] for j in n[1:] if degree[j]==degree[i])
        leading.append(v%mod)
    node=want_res[dc['residual_number']];top=max(degree[r] for r in want_res)
    demand(node==dc['residual_node'] and degree[node]==dc['degree']==top,'degree witness location')
    demand(leading[node]==dc['leading_coefficient'] and leading[node]!=0,'vanishing top coefficient')
    oc=c['occurrence'];mod=oc['modulus'];point=oc['point'];demand(len(point)==nvars,'gradient point dimension')
    values=[]
    for n in nodes:
        if n[0]=='input':v=point[n[1]]
        elif n[0]=='const':v=n[1]
        elif n[0]=='add':v=values[n[1]]+values[n[2]]
        else:v=values[n[1]]*values[n[2]]
        values.append(v%mod)
    adj=[0]*len(nodes);adj[output]=1
    for i in reversed(range(len(nodes))):
        n=nodes[i]
        if n[0]=='add':
            for j in n[1:]:adj[j]=(adj[j]+adj[i])%mod
        elif n[0]=='mul':
            a,b=n[1:];adj[a]=(adj[a]+adj[i]*values[b])%mod;adj[b]=(adj[b]+adj[i]*values[a])%mod
    gradient=[0]*nvars
    for i,n in enumerate(nodes):
        if n[0]=='input':gradient[n[1]]=(gradient[n[1]]+adj[i])%mod
    demand(gradient==oc['gradient'] and all(gradient),'a declared input is not certified to occur')
    demand(c['height_exponent']==bits[output]+1,'height bound differs')
    live=set();stack=[output]
    while stack:
        i=stack.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('add','mul'):stack.extend(nodes[i][1:])
    got={'variables':nvars,'residuals':len(want_res),'exact_degree':2*top,'live_binary_gates':sum(nodes[i][0] in ('add','mul') for i in live),
         'live_nodes':len(live),'total_nodes_with_restorations':len(nodes),'largest_absolute_literal':max(abs(nodes[i][1]) for i in live if nodes[i][0]=='const'),
         'expanded_height_strictly_less_than_power_of_two':bits[output]+1}
    demand(got==metrics,'reported metrics differ')
    if nvars==83:
        tight=load(ROOT/'P83/TIGHT_HEIGHT.json');norm=[]
        for n in nodes:
            if n[0]=='input':norm.append(1)
            elif n[0]=='const':norm.append(abs(n[1]))
            elif n[0]=='add':norm.append(norm[n[1]]+norm[n[2]])
            else:norm.append(norm[n[1]]*norm[n[2]])
        bound=norm[output]
        demand(str(bound)==tight['bound_integer'],'tight norm upper bound differs')
        demand(bound.bit_length()==tight['strict_power_of_two_exponent'],'tight height exponent differs')
        got['tight_expanded_height_strictly_less_than_power_of_two']=bound.bit_length()
    return got

def corruption_controls(source,p,g,c,m):
    caught=0
    bad=copy.deepcopy(p);bad['pivots'][0]['restoration'][0][0]+=1
    try:check_projection(source,bad)
    except ValueError:caught+=1
    bad=copy.deepcopy(p);bad['retained_rows']=bad['retained_rows'][1:]
    try:check_projection(source,bad)
    except ValueError:caught+=1
    bad=copy.deepcopy(c);bad['degree']['leading_coefficient']=0
    try:audit_graph(source,p,g,bad,m)
    except ValueError:caught+=1
    bad=copy.deepcopy(c);bad['occurrence']['gradient'][0]=0
    try:audit_graph(source,p,g,bad,m)
    except ValueError:caught+=1
    demand(caught==4,'a deliberate corruption escaped');return caught

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--profile',type=int,action='append');ap.add_argument('--skip-source',action='store_true');ap.add_argument('--receipt',type=Path);a=ap.parse_args()
    result={'source':{'skipped':True} if a.skip_source else check_source()};source=load(ROOT/'source227.json')
    profiles=a.profile or sorted(int(p.name[1:]) for p in ROOT.glob('P[0-9]*') if p.is_dir())
    results=[];fixtures=None
    for n in profiles:
        folder=ROOT/f'P{n}';p=load(folder/'projection.json');g=load(folder/'circuit.json');c=load(folder/'certificates.json');m=load(folder/'METRICS.json')
        results.append(audit_graph(source,p,g,c,m))
        if n==83:fixtures=(p,g,c,m)
    if fixtures:result['corruptions_rejected']=corruption_controls(source,*fixtures)
    result['profiles']=results;result['status']='PASS';result['scope']='finite exact algebra, graph and certificate audit; unbounded mathematical proofs are separate'
    rendered=json.dumps(result,indent=2)+'\n'
    if a.receipt:a.receipt.write_text(rendered)
    print(rendered,end='')

if __name__=='__main__':main()
