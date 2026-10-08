#!/usr/bin/env python3
"""Paired component timings and native positive-stage checks, not production claims."""
import sys,json,random,time,statistics,platform
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'src'),str(ROOT/'tests')]
from whitehead_exposure.algebra import *
from whitehead_exposure.selector import *
from whitehead_exposure.slp import *
from whitehead_exposure.engine import *
from whitehead_exposure.braid import *
from whitehead_exposure.pd_fixture import presentation_from_pd
from helpers import all_moves,random_word,barrier

def brute_graph_selector(graphs,alive):
    V=[x for g in alive for x in (-g,g)];total=add_graphs(graphs);d=degrees(total,V);L=sum(total.values())
    local=[(g,degrees(g,V),sum(g.values())) for g in graphs];best=None
    for a,S in all_moves(alive):
        c=cut_capacity(total,S);delta=c-d[a]
        for graph,dj,ell in local:
            if cut_capacity(graph,S)==1:
                U=L-d[a]+(ell-dj[a])*(c-2);score=(U,delta)
                if best is None or score<best:best=score
    return best

def clock(fn):
    t=time.perf_counter();v=fn();return time.perf_counter()-t,v

def main():
    rng=random.Random(831079)
    report={'python':sys.version,'platform':platform.platform(),'seed':831079,'timing':'perf_counter, alternating component order, no subprocess isolation; raw samples retained','component':[],'compressed':[],'braids':[]}
    for r in range(2,8):
        words=barrier(3)+[random_word(rng,r,8*r)*4];graphs=[word_graph(w) for w in words];alive=tuple(range(1,r+1))
        a_times=[];b_times=[];stats={}
        for rep in range(3):
            fa=lambda:exposure_from_graphs(graphs,alive,stats=stats);fb=lambda:brute_graph_selector(graphs,alive)
            if rep%2:tb,b=clock(fb);ta,a=clock(fa)
            else:ta,a=clock(fa);tb,b=clock(fb)
            assert (a['allocation_bound'],a['length_change'])==b
            a_times.append(ta);b_times.append(tb)
        report['component'].append({'rank':r,'explicit_length':sum(map(len,words)),'selector_seconds':a_times,'enumerator_seconds':b_times,
                                    'median_ratio':statistics.median(b_times)/statistics.median(a_times),'stats':dict(stats)})
    for k in (10,100,1000,4096):
        grammar=barrier_grammar(k);a_times=[];replay=[]
        for rep in range(3):
            def select():
                G=grammar_graphs(grammar);p=exposure_from_graphs(G,(1,2));assert verify_exposure_graphs(G,(1,2),p);return p
            elapsed,p=clock(select);a_times.append(elapsed);move={key:p[key] for key in ('relation','multiplier','subset')}
            elapsed,ok=clock(lambda:verify_fused_exposure(grammar,move,cap=100));assert ok;replay.append(elapsed)
        report['compressed'].append({'k':k,'m':'2^'+str(k),'nodes':len(grammar['nodes']),'length_bit_length':(20*2**k+5).bit_length(),
                                      'summary_select_verify_seconds':a_times,'fused_replay_seconds':replay,'literal_image_cap':100})
        if k==1000:(ROOT/'certificates'/'barrier_2pow1000.json').write_text(json.dumps({'grammar':grammar,'exposure':p,'fused_move':move},indent=2)+'\n')
    corpus=[]
    for j in range(40):
        s=rng.randint(2,6);w=[rng.choice((-1,1))*i for i in range(1,s)]
        conjugator=[rng.choice((-1,1))*rng.randint(1,s-1) for _ in range(rng.randint(0,16))]
        w=conjugator+w+[-x for x in reversed(conjugator)]
        for _ in range(rng.randint(0,8)):
            i=rng.randrange(len(w)+1);a=rng.randint(1,s-1);w[i:i]=[a,-a]
        corpus.append((f'unknot-{j:02}',s,w,'UNKNOT'))
    for j in range(20):
        s=rng.randint(3,6)
        w=([1,1,1]+[rng.choice((-1,1))*i for i in range(2,s)]) if j%2 else ([1,-2,1,-2]+[rng.choice((-1,1))*i for i in range(3,s)])
        conj=[rng.choice((-1,1))*rng.randint(1,s-1) for _ in range(rng.randint(0,8))];w=conj+w+[-x for x in reversed(conj)]
        corpus.append((f'nontrivial-control-{j:02}',s,w,'NONTRIVIAL_CONTROL'))
    for name,s,w,label in corpus:
        record={'name':name,'strands':s,'crossings':len(w),'construction_label':label,'braid':w}
        for mode in ('strict','rank-first'):
            samples=[]
            for _ in range(3):
                elapsed,c=clock(lambda:recognize_braid(s,w,mode=mode,max_letters=20000,max_work=1000000));samples.append(elapsed)
                if c['status']=='UNKNOT':assert verify_braid_certificate(c)
                if label=='NONTRIVIAL_CONTROL':assert c['status']!='UNKNOT'
            alg=c.get('algebra',{})
            record[mode]={'seconds':samples,'status':c['status'],'moves':len(alg.get('moves',[])),
                          'exposures':sum(x['kind']=='exposure' for x in alg.get('trace',[]))}
        report['braids'].append(record)
    pd=json.loads((ROOT/'data'/'gordian_pd.json').read_text())['pd'];W,G,info=presentation_from_pd(pd)
    record={'validation':info,'initial_generators':len(G),'initial_length':sum(map(len,W))}
    for mode in ('strict','rank-first'):
        samples=[]
        for _ in range(3):
            elapsed,c=clock(lambda:search_presentation(W,G,mode=mode,max_work=20000000,max_letters=200000));samples.append(elapsed)
        record[mode]={'seconds':samples,'status':c['status'],'reason':c['reason'],'moves':len(c['moves']),
                      'peak_stored_letters':c['peak_stored_letters'],'exposures':sum(x['kind']=='exposure' for x in c['trace'])}
    report['gordian_isolated_stage']=record
    report['summary']={'unknot_positive_rank_first':sum(x['rank-first']['status']=='UNKNOT' for x in report['braids'] if x['construction_label']=='UNKNOT'),
                       'unknot_positive_strict':sum(x['strict']['status']=='UNKNOT' for x in report['braids'] if x['construction_label']=='UNKNOT'),
                       'total_nontrivial_controls':20,'exposure_events':sum(x['rank-first']['exposures'] for x in report['braids']),
                       'rank_first_sum_medians':sum(statistics.median(x['rank-first']['seconds']) for x in report['braids']),
                       'strict_sum_medians':sum(statistics.median(x['strict']['seconds']) for x in report['braids'])}
    (ROOT/'data'/'benchmark.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'summary':report['summary'],'gordian':record,'component_ratios':[x['median_ratio'] for x in report['component']]},indent=2))
if __name__=='__main__':main()
