#!/usr/bin/env python3
"""Literal support-aware polynomial construction; Python standard library only."""
from pathlib import Path
import json,hashlib
from collections import Counter
from common import DAG,coefficient_data,quadratic_form,geometric_pair,read_ports,evaluate_recipe,BETA_EXPONENT,ROOT
import nine_tail,ten_tail

def source(d,mode,layout='uniform'):
    data=coefficient_data();w=json.loads((ROOT/'data/weights.json').read_text())['weights_in_parent_coordinate_order'];W=max(w)
    A,M,S,P,c=d.plus,d.times,d.minus,d.power,d.const
    if mode=='ten_integer':
        variables=['f','g','h','k','l','w','x','y','z','m'];v={n:d.var(n) for n in variables}
        b=d.save('b',A(c(1),M(c(3),v['f'])));B=d.save('B',M(d.fixed('base_floor'),P(b,2)))
    else:
        variables=['epsilon','g','h','s','w','phi','i','j','n'];v={n:d.var(n) for n in variables}
        if mode=='nine_positive':
            for n in ['epsilon','phi','n']:v[n]=S(v[n],c(1))
        else:
            for n in ['g','h','s','w','i','j']:v[n]=A(v[n],c(1))
        b=d.save('b',A(d.fixed('base_floor'),v['epsilon']));B=d.save('B',P(b,3))
    if layout=='uniform':
        targets=[2*W+j*(2*W+1) for j in range(22)];order=list(range(22));signs=[1]*22
    else:
        rec=json.loads((ROOT/'data/overlap_layout.json').read_text());targets=rec['targets'];order=rec['row_indices_in_common_order'];signs=rec.get('row_signs',[1]*22)
    # Warm fixed powers using already available sums, preserving literal gates.
    needed={W,2*W}|set(w[1:])|{W-x for x in w[1:]}|{b-a for a,b in zip(targets,targets[1:])}
    known={0:c(1),1:B}
    for k in sorted(needed):
        if k in known:continue
        candidate=next(((a,k-a) for a in sorted(known,reverse=True) if a>0 and k-a>0 and k-a in known),None)
        if candidate:
            aa,bb=candidate;node=M(known[aa],known[bb]);d.powers[B,k]=node
        else:node=P(B,k)
        known.update({e:n for (base,e),n in d.powers.items() if base==B});known[k]=node
    top=d.save('top',P(B,W));coords=[top]+[P(B,W-x) for x in w[1:]]
    forms=[]
    for row_index,sign in zip(order,signs):
        terms=[]
        for term in data['rows'][row_index]:
            ex=(2-sum(term['alpha']),)+tuple(term['alpha'])
            leaf=c(term['leaf']) if isinstance(term['leaf'],int) else d.fixed(term['leaf'])
            if term['sign']*sign==-1:leaf=M(c(-1),leaf)
            terms.append((ex,leaf))
        forms.append(quadratic_form(d,terms,coords))
    D=forms[-1]
    for j in range(20,-1,-1):D=A(forms[j],M(P(B,targets[j+1]-targets[j]),D))
    if targets[0]!=2*W:D=M(P(B,targets[0]-2*W),D)
    D=d.save('Dcode',D);ell=d.save('ell',A(*(P(B,x) for x in w[1:])))
    span=targets[-1]+2*W
    N0=d.save('N0',M(top,B));end,geosum=geometric_pair(d,B,span+1)
    N1=d.save('N1',M(c(4),end));N=d.save('N',M(N0,N1))
    if layout=='uniform':
        _,blocks=geometric_pair(d,P(B,2*W+1),22);targetsum=M(P(top,2),blocks)
    else:
        targetsum=c(1)
        for j in range(20,-1,-1):targetsum=A(c(1),M(P(B,targets[j+1]-targets[j]),targetsum))
        targetsum=M(P(B,targets[0]),targetsum)
    targetsum=d.save('targetsum',targetsum)
    target=d.save('target',M(S(B,c(2)),targetsum))
    mask=d.save('mask',S(S(N0,c(1)),M(S(b,c(1)),ell)))
    T=d.save('Tcode',A(mask,M(target,N0)))
    J=d.save('Jcode',A(M(c(2),P(A(c(1),v['g']),2),D),M(B,geosum)))
    Sc=d.save('Scode',A(v['g'],M(J,N0)))
    R=d.save('Rcode',A(M(A(Sc,T,c(1)),N),T,c(1)))
    X=d.save('X',M(S(N,c(1)),R));Y=d.save('Y',P(N,2))
    cap=d.save('Gcap' if mode!='ten_integer' else 'Ccap',M(c(32),b,top) if mode!='ten_integer' else M(b,top))
    meta={'variables':variables,'weights':w,'W':W,'targets':targets,'row_order_in_common':order,'row_signs':signs,'source_span':span,'base_floor_exponent':BETA_EXPONENT,'layout':layout,'coefficient_binding':'../data/coefficient_recipes.json'}
    return v,b,B,N,X,Y,cap,meta,data

def build(mode,layout='uniform',certificate=False):
    d=DAG();v,b,B,N,X,Y,cap,meta,data=source(d,mode,layout)
    out=ten_tail.finish(d,v,b,B,N,X,Y,cap) if mode=='ten_integer' else (nine_tail.finish_certificate(d,v,b,B,N,X,cap) if certificate else nine_tail.finish(d,v,b,B,N,X,cap))
    nodes,out,names=d.export(out);counts=Counter(n['kind'] for n in nodes if 'left'in n)
    meta.update(schema='support-aware-consistency-polynomial-v1',domain={'ten_integer':'integers','nine_positive':'positive integers','nine_natural':'nonnegative integers'}[mode],nodes=nodes,output=out,named_nodes=names,operation_counts=dict(counts),total_operations=sum(counts.values()))
    return meta,data

def degree_bound_certificate(body,data,prime=1000000007):
    ports=read_ports();fixed={name:evaluate_recipe(rec,ports,prime) for name,rec in data['recipes'].items()};fixed['base_floor']=pow(2,BETA_EXPONENT,prime)
    degrees=[];leads=[]
    for n in body['nodes']:
        kind=n['kind']
        if kind=='variable':degree,lead=1,1
        elif kind=='literal':degree,lead=0,n['value']%prime
        elif kind=='fixed':degree,lead=0,fixed[n['name']]
        else:
            a,b=n['left'],n['right']
            if kind=='mul':degree,lead=degrees[a]+degrees[b],leads[a]*leads[b]%prime
            else:
                degree=max(degrees[a],degrees[b]);aa=leads[a] if degrees[a]==degree else 0;bb=leads[b] if degrees[b]==degree else 0
                lead=(aa+bb if kind=='add' else aa-bb)%prime
        degrees.append(degree);leads.append(lead)
    i=body['output']
    return {'prime':prime,'propagated_bound':degrees[i],'coefficient_at_bound':leads[i],'exact_if_nonzero':bool(leads[i]),'named_nodes':{n:{'degree_bound':degrees[j],'coefficient_at_bound':leads[j]} for n,j in body['named_nodes'].items()}}

def main():
    layouts=['uniform']+(['overlap'] if (ROOT/'data/overlap_layout.json').exists() else [])
    for layout in layouts:
        for mode in ['nine_positive','nine_natural','ten_integer']:
            body,data=build(mode,layout);cert=degree_bound_certificate(body,data)
            if mode!='ten_integer':
                cb,cd=build(mode,layout,True);cert=degree_bound_certificate(cb,cd)
                (ROOT/'generated'/f'{layout}_{mode}_degree_certificate.json').write_text(json.dumps(cb,separators=(',',':'))+'\n')
            body['syntactic_degree_upper_bound']=cert['propagated_bound'];body['diagonal_bound_certificate']=cert
            (ROOT/'generated'/f'{layout}_{mode}.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
            print(layout,mode,'operations',body['total_operations'],'degree bound',cert['propagated_bound'],'exact',cert['exact_if_nonzero'])
    (ROOT/'data/coefficient_recipes.json').write_text(json.dumps(data,indent=2)+'\n')
if __name__=='__main__':main()
