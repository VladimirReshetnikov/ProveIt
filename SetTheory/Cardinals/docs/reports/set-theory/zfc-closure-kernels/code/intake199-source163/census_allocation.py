#!/usr/bin/env python3
"""Small exact role/row census, not a fold search or runtime certificate."""
import hashlib, importlib.util, itertools, json, sys
from collections import defaultdict
from pathlib import Path
P=Path(__file__).resolve().parent
TOOLS=Path('/tmp/k216-permuted-partial-composition')
sys.path.insert(0,str(TOOLS))
import source_language as s
import build221 as b
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def census(table,source):
    T=b.read_table(table.read_bytes());tree=s.tree(json.loads(source.read_text()))
    groups,paths=b.decoder_map(T,tree);states=sorted({q for q,bit in T});bytype=defaultdict(set)
    for q,ns in groups.items():
        for n in ns:bytype[n].add(q)
    markers={q:set(('1'+p)[-1]for p in ps)for q,ps in paths.items()}
    pairs=[];exact=[];marker_options=[]
    for q,r in itertools.combinations(states,2):
        phi=lambda z:q if z==r else z
        act=lambda z:(z[0],z[1],phi(z[2]))
        same=[bit for bit in(0,1)if act(T[q,bit])==act(T[r,bit])]
        if len(same)==2:exact.append([q,r])
        if len(same)!=1:continue
        bit=1-same[0];pairs.append([q,r,same[0]])
        if markers.get(q)not in({'0'},{'1'})or markers.get(r)not in({'0'},{'1'})or markers[q]==markers[r]:continue
        if T[q,bit][:2]!=(bit,1)or T[r,bit][:2]!=(bit,1):continue
        targets={int(next(iter(markers[q]))):phi(T[q,bit][2]),int(next(iter(markers[r]))):phi(T[r,bit][2])}
        providers=[h for h in states if h not in(q,r)and all(act(T[h,m])==(m,1,targets[m])for m in(0,1))]
        if providers:marker_options.append({'q':q,'r':r,'common_bit':same[0],'q_marker':sorted(markers[q]),'r_marker':sorted(markers[r]),'providers':providers,
          'incoming_q':[[*k,*v]for k,v in sorted(T.items())if v[2]==q],
          'incoming_r':[[*k,*v]for k,v in sorted(T.items())if v[2]==r]})
    return {'states':len(states),'internal_prefixes':sum(map(len,paths.values())),
      'decoder_states':len(groups),'represented_interior_types':len(bytype),
      'types_with_multiple_states':[{'states':sorted(qs),'example_size':len(s.sites(n))}for n,qs in bytype.items()if len(qs)>1],
      'complete_row_equalities_after_pair_quotient':exact,'one_common_branch_pairs':pairs,
      'opposite_preceding_marker_with_exact_existing_two_row_provider':marker_options,
      'scope':'Only literal rows and all decoded source prefixes. A listed marker provider is not a valid state quotient until arithmetic/nondecoder callers and full successor relation are proved.'}

def main():
    K=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-k215')
    table=K/'k215.native.tm'
    if not table.exists():table=K/'machine/k215.native.tm'
    result={'baseline':census(table,K/'sites215.json'),'rho6':census(P/'allocation1/candidate.native.tm',P/'price1/sites215-rho6.json'),
      'inputs':{str(p):sha(p)for p in[table,K/'sites215.json',P/'allocation1/candidate.native.tm',P/'price1/sites215-rho6.json',TOOLS/'source_language.py',TOOLS/'build221.py',Path(__file__)]}}
    (P/'allocation-census.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:{j:v[j]for j in['states','decoder_states','represented_interior_types','complete_row_equalities_after_pair_quotient','opposite_preceding_marker_with_exact_existing_two_row_provider']}for k,v in result.items()if k!='inputs'},indent=2))
if __name__=='__main__':main()
