#!/usr/bin/env python3
"""Independent finite audit; no imports from construction code, no assertions."""
from pathlib import Path
from collections import Counter,defaultdict
import json,math,itertools,gzip,hashlib,random
ROOT=Path(__file__).resolve().parent
def need(ok,msg):
    if not ok:raise ValueError(msg)
def plus(a,b,sign=1):
    c=dict(a)
    for m,v in b.items():c[m]=c.get(m,0)+sign*v
    return {m:v for m,v in c.items() if v}
def times(a,b):
    c={}
    for m,u in a.items():
        for n,v in b.items():
            e=tuple(x+y for x,y in zip(m,n));c[e]=c.get(e,0)+u*v
    return {m:v for m,v in c.items() if v}
def parent():
    d=json.loads((ROOT/'data/parent_system.json').read_text());names=d['variables']+d['constants'];n=len(d['variables']);zero=(0,)*len(names);env={}
    for i,x in enumerate(names):e=list(zero);e[i]=1;env[x]={tuple(e):1}
    def val(x):return {zero:x} if isinstance(x,int) and x else {} if isinstance(x,int) else env[x]
    for out,op,a,b in d['source']:env[out]=times(val(a),val(b)) if op=='*' else plus(val(a),val(b),-1 if op=='-' else 1)
    rows=[]
    for a,b in d['comparisons']:
        result={}
        for e,v in plus(val(a),val(b),-1).items():
            for alpha in itertools.product(*(range(k+1) for k in e[:n])):
                c=v*math.prod(math.comb(x,y) for x,y in zip(e[:n],alpha));m=alpha+e[n:];result[m]=result.get(m,0)+c
        rows.append({m:v for m,v in result.items() if v})
    order=list(range(4))+list(range(5,22))+[4]
    return d,[rows[j] for j in order]
def weighted_terms(rows,n=31):
    ans=[]
    for row in rows:
        byalpha=defaultdict(dict)
        for e,v in row.items():
            alpha,p=e[:n],e[n:];mult=math.factorial(2-sum(alpha))*math.prod(math.factorial(k) for k in alpha)
            byalpha[alpha][p]=v*mult
        ans.append(dict(byalpha))
    return ans
def recipe_value(rec,ports,mod=None):
    total=0
    for p,v in rec.items():
        term=v
        for a,e in zip(ports,p):term*=pow(a,e,mod) if mod else a**e
        total+=term
    return total%mod if mod else total
def load_ports():
    data=[];receipts=[]
    for p in ['beta','K','MC','MF_source']:
        raw=gzip.decompress((ROOT/f'data/ports/{p}.bin.gz').read_bytes());data.append(int.from_bytes(raw,'little'));receipts.append({'port':p,'bits':data[-1].bit_length(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
    return data,receipts
def support_check(weighted,w):
    pairs=list(itertools.combinations_with_replacement(range(32),2));sums=defaultdict(list)
    for p in pairs:sums[w[p[0]]+w[p[1]]].append(p)
    selected=set()
    for row in weighted:
        for alpha in row:
            p=[0]*(2-sum(alpha))
            for i,e in enumerate(alpha,1):p.extend([i]*e)
            selected.add(tuple(p))
    need(len(w)==32 and w[0]==0 and len(set(w))==32 and min(w[1:])>0,'weight domain or uniqueness')
    for p in selected:need(sums[w[p[0]]+w[p[1]]]==[p],f'protected pair collision {p}')
    return {'selected_pairs':len(selected),'all_pairs':len(pairs),'distinct_sums':len(sums),'maximum_weight':max(w),'unprotected_collision_maximum':max(map(len,sums.values()))},pairs
def layouts(W):
    ans={'uniform':{'targets':[2*W+j*(2*W+1) for j in range(22)],'row_indices_in_common_order':list(range(22)),'row_signs':[1]*22}}
    if (ROOT/'data/overlap_layout.json').exists():ans['overlap']=json.loads((ROOT/'data/overlap_layout.json').read_text())
    return ans
def source_identity(rows,weighted,w,pairs,layout):
    H=layout['targets'];order=layout['row_indices_in_common_order'];signs=layout['row_signs'];need(sorted(order)==list(range(22)),'row permutation');need(min(H)>=2*max(w),'negative coding exponent')
    need(all(b>a for a,b in zip(H,H[1:])),'targets increasing');target_index={h:i for i,h in enumerate(H)};D={};owner={};actual=[{} for h in H]
    for j,(r,sgn) in enumerate(zip(order,signs)):
        need(sgn in (-1,1),'invalid row sign')
        for alpha,q in weighted[r].items():
            e=H[j]-sum(x*y for x,y in zip(alpha,w[1:]));need(e not in owner,'D coefficient collision');owner[e]=(j,alpha);D[e]={p:v*sgn for p,v in q.items()}
            for a,b in pairs:
                exp=e+w[a]+w[b]
                if exp not in target_index:continue
                i=target_index[exp];beta=[0]*31
                if a:beta[a-1]+=1
                if b:beta[b-1]+=1
                beta=tuple(beta);need(i==j and beta==alpha,'cross-output or monomial contamination')
                mult=1 if a==b else 2
                for p,v in q.items():
                    mon=beta+p;actual[i][mon]=actual[i].get(mon,0)+mult*sgn*v
    for i,(r,sgn) in enumerate(zip(order,signs)):
        need({m:v for m,v in actual[i].items() if v}=={m:2*sgn*v for m,v in rows[r].items()},'exact coefficient recovery')
    zero=(0,)*4;need(max(D)==H[-1] and list(D[H[-1]])==[zero] and D[H[-1]][zero]>0,'positive leading coefficient')
    return D,{'targets':H,'maximum_target':H[-1],'source_span':H[-1]+2*max(w),'D_terms':len(D),'leading_coefficient':D[H[-1]][zero],'exact_output_identities':len(H)}
def fixed_values(rec,ports,prime):
    vals={'base_floor':pow(2,rec['beta_source_exponent'],prime)}
    for name,terms in rec['recipes'].items():vals[name]=recipe_value({tuple(t['powers']):t['coefficient'] for t in terms},ports,prime)
    return vals
def dag_check(d,fixed,assignment,prime):
    nodes=d['nodes'];values=[];degrees=[];leads=[];ops=Counter();varset=set()
    for i,node in enumerate(nodes):
        kind=node['kind']
        if kind=='variable':value=assignment[node['name']]%prime;deg=1;lead=1;varset.add(node['name'])
        elif kind=='literal':need(isinstance(node['value'],int),'noninteger literal');value=node['value']%prime;deg=0;lead=value
        elif kind=='fixed':need(node['name'] in fixed,'unbound fixed leaf');value=fixed[node['name']];deg=0;lead=value
        else:
            need(kind in ('add','sub','mul'),'invalid gate');a,b=node['left'],node['right'];need(0<=a<i and 0<=b<i,'acyclic earlier gate references');ops[kind]+=1
            if kind=='mul':value=values[a]*values[b]%prime;deg=degrees[a]+degrees[b];lead=leads[a]*leads[b]%prime
            else:
                value=(values[a]+values[b] if kind=='add' else values[a]-values[b])%prime;deg=max(degrees[a],degrees[b]);aa=leads[a] if degrees[a]==deg else 0;bb=leads[b] if degrees[b]==deg else 0;lead=(aa+bb if kind=='add' else aa-bb)%prime
        values.append(value);degrees.append(deg);leads.append(lead)
    used=set();todo=[d['output']]
    while todo:
        i=todo.pop()
        if i in used:continue
        used.add(i)
        if 'left'in nodes[i]:todo.extend([nodes[i]['left'],nodes[i]['right']])
    need(len(used)==len(nodes),'dead paid gates or leaves');need(varset==set(d['variables']),'variable set mismatch');need(dict(ops)==d['operation_counts'] and sum(ops.values())==d['total_operations'],'operation ledger')
    return values,degrees,leads
def geometric(B,n,p):
    total=0;term=1
    for i in range(n):total=(total+term)%p;term=term*B%p
    return total
def source_modular_check(d,values,D,ports,assignment,p):
    W=d['W'];w=d['weights'];H=d['targets'];floor=pow(2,d['base_floor_exponent'],p);v=dict(assignment)
    if d['domain']=='integers':b=1+3*v['f'];B=floor*b*b
    else:
        if d['domain']=='positive integers':
            for n in ['epsilon','phi','n']:v[n]-=1
        else:
            for n in ['g','h','s','w','i','j']:v[n]+=1
        b=floor+v['epsilon'];B=b**3
    b%=p;B%=p;top=pow(B,W,p);dc=sum(recipe_value(q,ports,p)*pow(B,e,p) for e,q in D.items())%p;ell=sum(pow(B,x,p) for x in w[1:])%p
    K=H[-1]+2*W;N0=pow(B,W+1,p);N1=4*pow(B,K+1,p)%p;N=N0*N1%p
    tsum=sum(pow(B,h,p) for h in H)%p;target=(B-2)*tsum%p;mask=(N0-1-(b-1)*ell)%p;T=(mask+target*N0)%p;J=(2*(1+v['g'])**2*dc+B*geometric(B,K+1,p))%p;Sc=(v['g']+J*N0)%p;R=((Sc+T+1)*N+T+1)%p;X=(N-1)*R%p
    direct={'b':b,'B':B,'top':top,'Dcode':dc,'ell':ell,'N0':N0,'N1':N1,'N':N,'targetsum':tsum,'target':target,'mask':mask,'Tcode':T,'Jcode':J,'Scode':Sc,'Rcode':R,'X':X,'Y':N*N%p,'Ccap':b*top%p,'Gcap':32*b*top%p}
    if d['domain']!='integers':direct.pop('Y') # finalizer reuses name Y for N^2*s
    for n,x in direct.items():
        if n in d['named_nodes']:need(values[d['named_nodes'][n]]==x,f'source circuit transcription: {n}')
def telescoping_identity():
    z=(0,)*5
    def c(n):return {z:n} if n else {}
    vs=[]
    for i in range(5):e=list(z);e[i]=1;vs.append({tuple(e):1})
    A,C,E,G,H=vs
    def sq(x):return times(x,x)
    Am1=plus(sq(A),c(1),-1);D=plus(times(Am1,sq(C)),c(1));F=plus(times(Am1,sq(E)),c(1));I=plus(times(plus(sq(G),c(1),-1),sq(H)),c(1))
    V=times(times(times(A,C),times(A,E)),times(G,H));a1=times(times(D,F),I)
    rhs=plus(plus(times(plus(sq(C),c(1),-1),times(sq(times(A,E)),sq(times(G,H)))),times(D,times(plus(sq(E),c(1),-1),sq(times(G,H))))),times(times(D,F),plus(sq(H),c(1),-1)))
    need(plus(plus(sq(V),a1,-1),rhs,-1)=={},'nine tail telescoping identity')
def main():
    src,rows=parent();weighted=weighted_terms(rows);w=json.loads((ROOT/'data/weights.json').read_text())['weights_in_parent_coordinate_order'];support,pairs=support_check(weighted,w);ports,port_receipts=load_ports();rec=json.loads((ROOT/'data/coefficient_recipes.json').read_text())
    need(src['variables']==rec['variables'] and src['constants']==rec['ports'],'parent coordinate/port binding')
    # Independently compare every published fixed recipe coefficient to the parent.
    for i,row in enumerate(rec['rows']):
        reconstructed={}
        for t in row:
            q={(0,)*4:t['leaf']} if isinstance(t['leaf'],int) else {tuple(r['powers']):r['coefficient'] for r in rec['recipes'][t['leaf']]}
            reconstructed[tuple(t['alpha'])]={p:t['sign']*v for p,v in q.items()}
        need(reconstructed==weighted[i],'coefficient recipe transcription')
    M=max(abs(recipe_value(q,ports)) for row in weighted for q in row.values());need((1<<rec['beta_source_exponent'])>4*33**2*M,'strict source digit bound');telescoping_identity()
    all_layouts=layouts(max(w));layout_receipts={};Dby={}
    for name,layout in all_layouts.items():Dby[name],layout_receipts[name]=source_identity(rows,weighted,w,pairs,layout)
    results=[];rng=random.Random(7119)
    for path in sorted((ROOT/'generated').glob('*.json')):
        d=json.loads(path.read_text());layout=d['layout'];need(layout in all_layouts,'unknown layout');need(d['weights']==w,'circuit weight binding');need(d['targets']==all_layouts[layout]['targets'],'circuit target binding')
        certfile=path.name.endswith('_degree_certificate.json');degrees_at=[]
        for prime in [1000000007,1000000009,998244353]:
            fixed=fixed_values(rec,ports,prime)
            for trial in range(2):
                assignment={n:rng.randrange(1,50) for n in d['variables']};values,degrees,leads=dag_check(d,fixed,assignment,prime);source_modular_check(d,values,Dby[layout],ports,assignment,prime)
                if trial==0:degrees_at.append({'prime':prime,'degree_bound':degrees[d['output']],'coefficient_at_bound':leads[d['output']]})
        if certfile or d['domain']=='integers':need(all(x['coefficient_at_bound'] for x in degrees_at),'exact-degree certificate vanishes')
        if not certfile and d['domain']!='integers':
            cert=json.loads(path.with_name(path.stem+'_degree_certificate.json').read_text());prime=1000000007;fixed=fixed_values(rec,ports,prime)
            for k in range(8):
                ass={n:rng.randrange(1,100) for n in d['variables']};v,_,_=dag_check(d,fixed,ass,prime);vv,_,_=dag_check(cert,fixed,ass,prime);need(v[d['output']]==vv[cert['output']],'primary/certificate circuit discrepancy')
        results.append({'file':path.name,'operations':d['total_operations'],'domain':d['domain'],'degree_receipts':degrees_at,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    receipt={'status':'PASS','scope':'Finite identities, bindings and arithmetic circuits; not an unbounded unsolvability test or full formal proof.','support':support,'layouts':layout_receipts,'ports':port_receipts,'coefficient_bound_bit_length':M.bit_length(),'base_floor_exponent':rec['beta_source_exponent'],'circuits':results,'optimized_python_safe':True}
    (ROOT/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'status':'PASS','support':support,'circuits':len(results),'layouts':{k:v['maximum_target'] for k,v in layout_receipts.items()}},indent=2))
if __name__=='__main__':main()
