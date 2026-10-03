#!/usr/bin/env python3
"""Exact CA-clock checks. Never instantiate or step the compiled CA.

Reads frozen literal sources. Writes only this package's receipt. Assertions
use explicit exceptions, so `python -O` retains all verification.
"""
from pathlib import Path
from collections import defaultdict, Counter
import argparse, hashlib, json

import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from verify_pins import verify_inputs
HERE = Path(__file__).resolve().parent
DEFAULT = ROOT
PRIMES = (2, 3, 5, 7, 11)

def require(ok, detail):
    if not ok: raise AssertionError(detail)

def grouped(rows, key='source'):
    out = defaultdict(list)
    for row in rows: out[row[key]].append(row)
    return out

def read(root, name): return json.loads((root/name).read_text())
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def ca_clock(symbol, p, N, lam):
    require(N > 0 and lam > 0, 'positive encoded N and lambda required')
    if symbol == '0': return 1
    if symbol == '+': return (p*p+3)*N*N+lam*(p+3)*N+4*N+3
    if symbol == '-':
        require(N % p == 0, ('disabled decrement', p, N))
        Q=N//p
        return 3*N*N+Q*Q+lam*(3*N+Q)+2*N+2*Q+3
    require(symbol in ('Z','P'), symbol)
    require((N%p != 0) == (symbol=='Z'), ('disabled test', symbol,p,N))
    Q=N//p
    return 2*(N*N+Q*Q)+2*(lam+1)*(N+Q)+3

def test_clock(p,N,lam):
    return ca_clock('P' if N%p==0 else 'Z',p,N,lam)

def literal_clock(N,delta,lam):
    require(delta in (-1,0,1) and N+delta>=0, (N,delta))
    return 1 if delta==0 else lam+abs((N+delta)**2-N*N)

def enabled(row, values):
    g=row['guard']; op=g['op']
    return op=='true' or (values[g['counter']]==g['value'] if op=='eq' else values[g['counter']]>g['value'])

def traverse(groups,start,values,targets,lam,budget=200000):
    q=start;v=list(values); rows=[]; moves=zeros=0;tv=[0,0];cost=0
    while q not in targets or not rows:
        options=[r for r in groups[q] if enabled(r,v)]
        require(len(options)==1,('row enabledness',q,v,options))
        r=options[0];i=0 if r['side']==-1 else 1;d=r['delta']
        old=v.copy(); c=literal_clock(v[i],d,lam)
        # Independently evaluate the compiler's original travel-time expression.
        require(c==(1 if d==0 else lam+2*v[i]+d), ('travel/potential disagreement',r,v))
        cost+=c
        if d: moves+=1;tv[i]+=abs((v[i]+d)**2-v[i]**2)
        else: zeros+=1
        rows.append(dict(control=q,counters=old,branch=r['name'],predicted_CA_microedges=c))
        v[i]+=d;q=r['target']
        require(min(v)>=0 and len(rows)<=budget,('negative value or budget',q,v))
    require(cost==lam*moves+sum(tv)+zeros,'path potential identity')
    return dict(control=q,counters=v,rows=rows,steps=len(rows),moves=moves,zero_updates=zeros,TV=tv,CA_microedges=cost)

def count_ledger(R):
    """Derive total primitive counts from every source AND destination restorer."""
    source_hist=Counter();restore_hist=Counter();m=len(R['controls']);rows=moves=0
    for q,es in grouped(R['rows']).items():
        x=es[0]['symbol'];p=PRIMES[es[0]['counter']]
        if x=='0':
            require(len(es)==1,'identity branching');rows+=1;source_hist[('0',p,1)]+=1
        elif x in '+-':
            require(len(es)==1,'moving branching');m+=p+7;rows+=p+10;moves+=p+3
            source_hist[(x,p,1)]+=1
        else:
            symbols={e['symbol'] for e in es}
            require(symbols<=set('ZP') and len(symbols)==len(es),'test source')
            require(len({e['counter'] for e in es})==1,'test counter')
            m+=2*p+2;rows+=2*p+3+(p-1)*('Z' in symbols)+('P' in symbols);moves+=p+1
            source_hist[(''.join(sorted(symbols)),p,len(es))]+=1
    for q,es in grouped(R['rows'],'target').items():
        if es[0]['symbol'] in 'ZP':
            p=PRIMES[es[0]['counter']]
            require(all(e['symbol'] in 'ZP' and PRIMES[e['counter']]==p for e in es),'mixed restorer')
            restore_hist[p]+=1;m+=2*p+2;rows+=2*p+3;moves+=p+1
    D=2*(m+2*moves);S=2*D+2;Z=40*D+60;lam=3+2*Z-4*S
    return dict(m=m,moving=moves,zero_update=rows-moves,rows=rows,J=0,D=D,S=S,Z=Z,lambda_=lam),source_hist,restore_hist

def suffix_clock(K,h,b,lam):
    """Exact geometric sum, excluding the normalized source data operation."""
    require(K>0 and K%7 and K%11 and h>=0 and b in (0,1),'recorder promise')
    u=(11**h-7**h)//4; u2=(121**h-49**h)//72
    v=(49**h-11**h)//38; v2=(2401**h-121**h)//2280
    return (test_clock(11,K*7**h,lam)+616*K*K*u2+(76*lam+60)*K*u+12*h
            +test_clock(7,K*11**h,lam)
            +b*(152*K*K*121**h+(26*lam+20)*K*11**h+6)
            +8208*K*K*49**b*v2+(266*lam+208)*K*7**b*v+18*h
            +test_clock(11,K*7**(2*h+b),lam))

def suffix_direct(K,h,b,lam):
    H,W=h,0;total=0
    def step(i,symbol):
        nonlocal H,W,total
        p=7 if i==0 else 11;N=K*7**H*11**W
        total+=ca_clock(symbol,p,N,lam)
        d={'+':1,'-':-1}.get(symbol,0)
        if i==0:H+=d
        else:W+=d
    step(1,'Z')
    for _ in range(h):
        for op in ((0,'P'),(0,'-'),(1,'+'),(1,'P')):step(*op)
    step(0,'Z')
    if b:
        step(0,'+');step(0,'P')
    for _ in range(h):
        for op in ((1,'P'),(1,'-'),(0,'+'),(0,'P'),(0,'+'),(0,'P')):step(*op)
    step(1,'Z')
    require((H,W)==(2*h+b,0),'recorder final state')
    return total

def run(root,out):
    verify_inputs()
    require(root.resolve() == ROOT, 'Only bundled pinned source is permitted')
    S=read(root,'source.json');R=read(root,'reversible5.json');C=read(root,'certificates.json');N3=read(root,'normalized3.json')
    SG=grouped(S['branches']);RG=grouped(R['rows']);ledger,sh,rh=count_ledger(R);lam=ledger['lambda_']
    require(ledger==dict(m=122622,moving=66066,zero_update=75495,rows=141561,J=0,D=509508,S=1019018,Z=20380380,lambda_=36684691),ledger)
    require(len(S['controls'])==ledger['m'] and len(S['branches'])==ledger['rows'] and sum(bool(e['delta']) for e in S['branches'])==ledger['moving'],'serialized ledger')
    # Representative actual serialized graph for every prime/op/available test topology.
    representatives={}
    for c in C['prime']:
        key=(c['kind'],c.get('prime',0),''.join(sorted(c.get('targets',{}))))
        representatives.setdefault(key,c)
    checks=literal_steps=0;by_kind=Counter()
    for key,c in sorted(representatives.items()):
        kind,p,_=key
        for n in range(1,41):
            if kind=='-':n*=p
            sym=kind
            if kind=='test':
                sym='P' if n%p==0 else 'Z'
                if sym not in c['targets']:continue
            target=c['targets'][sym] if kind=='test' else c['target']
            z=traverse(SG,c['source'],[n,0],{target},lam)
            expected=ca_clock(sym,p,n,lam)
            require(z['CA_microedges']==expected,('macro clock',key,n,z,expected))
            require(z['counters']==[p*n if sym=='+' else n//p if sym=='-' else n,0],('macro output',key,n))
            Q=n//p if p else 0
            M=0 if sym=='0' else (p+3)*n if sym=='+' else 3*n+Q if sym=='-' else 2*(n+Q)
            TV=0 if sym=='0' else (p*p+3)*n*n if sym=='+' else 3*n*n+Q*Q if sym=='-' else 2*(n*n+Q*Q)
            Z=1 if sym=='0' else 4*n+3 if sym=='+' else 2*n+2*Q+3 if sym=='-' else 2*(n+Q)+3
            require((z['moves'],sum(z['TV']),z['zero_updates'])==(M,TV,Z),('phase counts',key,n))
            checks+=1;literal_steps+=z['steps'];by_kind[sym]+=1
    # Replay all actual saved rows continuously, not just saved numeric totals.
    replay=[]
    for name,start,initial,target,steps,theta in (
        ('empty-prologue-literal-trace.json','START',[1,0],'tm_A0_pop0',138,1394018396),
        ('empty-first-tm-literal-trace.json','tm_A0_pop0',[1,0],'tm_B0_pop0',210,2788036936),
        ('empty-through-first-tm-literal-trace.json','START',[1,0],'tm_B0_pop0',348,4182055332)):
        actual=traverse(SG,start,initial,{target},lam);saved=read(root,name)
        require(actual['steps']==steps and actual['CA_microedges']==theta,('trace clock',name))
        require(len(saved['trace'])==steps,'saved trace length')
        for a,b in zip(actual['rows'],saved['trace']):
            require(all(a[k]==b[k] for k in a),('saved row mismatch',name,a,b))
        replay.append(dict(file=name,sha256=sha(root/name),**{k:v for k,v in actual.items() if k!='rows'}))
    five_sums=[]
    for name,theta in (('empty-prologue-five-trace.json',1394018396),('empty-first-tm-five-trace.json',2788036936)):
        trace=read(root,name)['trace'];cost=0
        for r in trace:
            n=1
            for p,e in zip(PRIMES,r['counters']):n*=p**e
            cost+=ca_clock(r['symbol'],PRIMES[r['counter']],n,lam)
        require(cost==theta,('five/micro trace sum',name))
        five_sums.append(dict(file=name,steps=len(trace),CA_microedges=cost))
    # Every generator of the 2^233 orientation cube is checked without allocating CA gates.
    index={r['name']:i for i,r in enumerate(R['rows'])};flip_checks=0
    for c in C['history']:
        i=index[c['prefix']+'b0r0'];j=index[c['prefix']+'b1r0']
        rows=list(R['rows']);a=dict(rows[i]);b=dict(rows[j])
        for k in ('source','counter','symbol'):a[k],b[k]=b[k],a[k]
        rows[i]=a;rows[j]=b
        lg,ss,rr=count_ledger(dict(controls=R['controls'],rows=rows))
        require((lg,ss,rr)==(ledger,sh,rh),('orientation count change',c['target']))
        flip_checks+=1
    require(flip_checks==233,'pair count')
    # General positive lambda corroboration; no floating point is used.
    monotone=0
    for l in (1,2,17,lam):
        for p in PRIMES:
            for sym in ('+','-','Z','P'):
                domain=[n for n in range(1,101) if sym=='+' or (n%p==0 if sym in ('-','P') else n%p!=0)]
                costs=[ca_clock(sym,p,n,l) for n in domain]
                require(all(a<b for a,b in zip(costs,costs[1:])),('monotonicity',l,p,sym))
                monotone+=len(costs)-1
    suffix_checks=dominance=0
    for l in (1,lam):
        for K in (1,13,30):
            for h in range(13):
                for b in (0,1):
                    require(suffix_clock(K,h,b,l)==suffix_direct(K,h,b,l),('suffix formula',l,K,h,b));suffix_checks+=1
                require(suffix_clock(K,h,1,l)>suffix_clock(K,h,0,l),'equal-history strictness');dominance+=1
                for d in range(1,7):
                    for a in (0,1):
                        for b in (0,1):
                            require(suffix_clock(K,h+d,a,l)>suffix_clock(K,h,b,l),('positive-gap strictness',l,K,h,d,a,b));dominance+=1
    # All six-pair startup assignments on 64 parameter choices, at every boundary.
    hist_by_edge={e:(j,b) for j,c in enumerate(C['history']) for b,e in enumerate(c['incoming'])}
    startup_zero=('entry','v0000z','n0001e0','n0001e1','n0001e2','n0001e3')
    ids=[hist_by_edge[e][0] for e in startup_zero];require(len(set(ids))==6,'six startup pairs')
    E={e['name']:e for e in N3['rows']};orientations=boundaries=0
    for L in (0,1):
      for Rv in (0,1):
       for T in range(4):
        for cofactor in (1,13):
         for h0 in (0,1):
          path=['entry']+['v0000p','v0000d']*T+['v0000z','n0001e0','n0001e1','n0001e2','n0001e3']
          for mask in range(64):
            data=[L,Rv,T];h=h0;ha=h0;t=ta=0;seen_difference=False
            for edge in path:
                e=E[edge];p=PRIMES[e['counter']];sym=e['symbol'];K=cofactor*2**data[0]*3**data[1]*5**data[2]
                t+=ca_clock(sym,p,K*7**h,lam);ta+=ca_clock(sym,p,K*7**ha,lam)
                data[e['counter']]+={'+':1,'-':-1}.get(sym,0)
                K=cofactor*2**data[0]*3**data[1]*5**data[2]
                if edge in hist_by_edge:
                    j,b=hist_by_edge[edge];a=b^((mask>>ids.index(j))&1)
                    seen_difference|=(a!=b)
                    t+=suffix_clock(K,h,b,lam);ta+=suffix_clock(K,ha,a,lam)
                    h=2*h+b;ha=2*ha+a
                require((h<ha and t<ta) if seen_difference else (h==ha and t==ta),('startup orientation prefix',L,Rv,T,cofactor,h0,mask,edge))
                boundaries+=1
            orientations+=1
    startup_formula=lambda A:38*A*A+2*(A//5)**2+12*(A//7)**2+24*(A//11)**2+2*(lam+1)*(19*A+A//5+6*(A//7)+12*(A//11))+62
    clean_formula_checks=0
    for A in range(1,201):
        if A%7==0 or A%11==0 or A%5==0:continue
        direct=5+test_clock(5,A,lam)+6*test_clock(7,A,lam)+12*test_clock(11,A,lam)
        require(startup_formula(A)==direct,'T=0 clean CA formula');clean_formula_checks+=1
    receipt=dict(status='PASS',scope='Theorem-derived CA microedge clocks; actual literal-row replay; no CA execution or gate allocation',source_sha256=sha(root/'source.json'),lambda_=lam,ledger=ledger,actual_macro_representatives=len(representatives),actual_macro_tests=checks,actual_macro_tests_by_symbol=dict(by_kind),literal_rows_traversed_in_macro_tests=literal_steps,saved_trace_replays=replay,five_macro_sums=five_sums,individual_orientation_flips_checked=flip_checks,monotonicity_pairs_checked=monotone,closed_suffix_equalities_checked=suffix_checks,recorder_strict_inequalities_checked=dominance,startup_orientation_input_comparisons=orientations,startup_boundary_checks=boundaries,clean_T0_formula_checks=clean_formula_checks,clean_T0_empty_clock=startup_formula(1),source_group_histogram={str(k):v for k,v in sorted(sh.items())},restorer_prime_histogram=dict(sorted(rh.items())))
    out.write_text(json.dumps(receipt,indent=2)+'\n');return receipt

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source',type=Path,default=DEFAULT);ap.add_argument('--output',type=Path,default=HERE/'clock-receipt.json');args=ap.parse_args()
    result=run(args.source,args.output)
    print(json.dumps({k:v for k,v in result.items() if k not in ('saved_trace_replays','source_group_histogram','restorer_prime_histogram')},indent=2))
