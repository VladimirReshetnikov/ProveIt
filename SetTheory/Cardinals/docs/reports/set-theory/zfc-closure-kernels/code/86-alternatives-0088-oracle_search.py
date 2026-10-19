#!/usr/bin/env python3
"""Complete exact C254 certificate search using the literal template oracle.

This is an executable finite-algorithm reference, NOT a compiled binary TM.
The binary finite-word parser and all non-template calculus checks are retained
from ProveIt's MIT-0 term-certificate protocol. The only semantic change is
replacing the fixed-pattern match by pattern_oracle.match_oracle, proved
extensionally equivalent on validated arenas. Resource failures propagate.
"""
from pathlib import Path
if not __debug__:
    raise RuntimeError('Assertions must be enabled; do not use python -O.')


import copy,itertools,json,sys
import pattern_oracle as O
C,P,T=O.load_source()
import pattern_codec as Codec
ORACLE=O.compile_oracle(T)
FORMAT=P.FORMAT


def verify(cert, *, control_goal=None, stats=None):
    """Verify all twelve rules, both freshness gates, and fixed F by default.

    `control_goal` is used only by the test harness. `accepts` and `semidecide`
    expose no caller-chosen endpoint.
    """
    if stats is None:stats={}
    stats.update(node_records=0,constructor_checks=0,path_edges=0,proof_rows=0,
                 oracle_queries=0,oracle_steps=0,oracle_actual_edges=0,reason=None)
    try:
        C.require(type(cert) is dict and cert.get('format')==FORMAT,'format')
        nodes=cert['nodes'];C.validate_nodes(nodes,stats)
        if control_goal is not None:
            C.require(type(control_goal) is int and 0<=control_goal<len(nodes),'control_goal')
        rows=cert['proof_rows'];C.require(type(rows) is list,'proof_list');formulas=[]
        for i,row in enumerate(rows):
            stats['proof_rows']+=1;C.require(type(row) is dict,'proof_row')
            tag,args,children,out=(row[k] for k in ('tag','args','children','formula'))
            C.require(type(tag) is int and 0<=tag<12,'proof_tag')
            fields={'tag','args','children','formula'}|({'gate_paths'} if tag==11 else set())
            C.require(set(row)==fields,'row_fields')
            C.require(type(args) is list and len(args)==C.ARITY[tag],'proof_arity')
            C.require(all(type(j) is int and 0<=j<len(nodes) for j in args),'argument')
            C.require(type(out) is int and 0<=out<len(nodes),'claimed_formula')
            C.require(type(children) is list and len(children)==(2 if tag==1 else 1 if tag==2 else 0),'premise_arity')
            C.require(all(type(j) is int and 0<=j<i for j in children),'premise_reference')
            if tag==0:C.require(out==0,'truth')
            elif tag==1:
                C.require(out==args[0],'mp_conclusion')
                C.require(C.constructor(nodes,formulas[children[1]],0,formulas[children[0]],out,stats),'mp_major')
            elif tag==2:
                C.require(C.constructor(nodes,out,2,args[0],formulas[children[0]],stats),'gen')
            else:
                if tag==11:
                    paths=row['gate_paths'];C.require(type(paths) is list and len(paths)==2,'gate_witness_arity')
                    C.require(C.distinguish(nodes,args[2],args[0],paths[0],stats),'bundle_gate_1')
                    C.require(C.distinguish(nodes,args[2],args[1],paths[1],stats),'bundle_gate_2')
                qs={};accepted=O.match_oracle(nodes,out,args,ORACLE,tag,qs)
                stats['oracle_queries']+=qs['queries'];stats['oracle_steps']+=qs['oracle_steps'];stats['oracle_actual_edges']+=qs['actual_edges']
                C.require(accepted,'fixed_pattern')
            formulas.append(out)
        C.require(bool(formulas),'empty_proof')
        C.require(formulas[-1]==control_goal if control_goal is not None else C.is_falsity(nodes,formulas[-1]),'fixed_or_control_endpoint')
        return True
    except (C.Invalid,ValueError,TypeError,KeyError,IndexError) as error:
        stats['reason']=str(error);return False


def accepts(bits):
    cert=Codec.decode(bits,T)
    return cert is not None and verify(cert)


def semidecide():
    """Halts by returning a finite accepted word iff C254 derives F.

    Under the inherited exact calculus calibration, this finite algorithm's
    nontermination is equivalent in ZFC to Con(ZFC). No claim is made about
    CPython, any physical runtime, or an unimplemented binary-table runtime.
    """
    for bits in Codec.words():
        if accepts(bits):return bits


def witness(nodes,left,right):
    pending=[(left,right,[])]
    while pending:
        a,b,path=pending.pop()
        if a==b:continue
        if a==0 or b==0 or nodes[a][1]!=nodes[b][1]:return path
        pending.extend((nodes[a][2+d],nodes[b][2+d],path+[d]) for d in (0,1))
    return None


def controls():
    certs=[]
    # Truth, normalized all-zero MP, GEN.
    base=O.canonical_start_arena()
    truth={'tag':0,'args':[],'children':[],'formula':0}
    certs.append(({'format':FORMAT,'nodes':base,'proof_rows':[truth]},0))
    mp={'tag':1,'args':[0],'children':[0,0],'formula':0}
    certs.append(({'format':FORMAT,'nodes':base,'proof_rows':[truth,mp]},0))
    nodes=copy.deepcopy(base);nodes.append(['b',2,1,0]);out=len(nodes)-1
    gen={'tag':2,'args':[1],'children':[0],'formula':out}
    certs.append(({'format':FORMAT,'nodes':nodes,'proof_rows':[truth,gen]},out))
    for rule,t in T.items():
        for args in itertools.product(range(3),repeat=t.arity):
            nodes=O.canonical_start_arena();intern={tuple(n[1:]):i for i,n in enumerate(nodes) if i}
            out=O.make_instance(ORACLE['syntax'][rule],args,nodes,intern)
            row={'tag':rule,'args':list(args),'children':[],'formula':out}
            if rule==11:
                pp=[witness(nodes,args[2],args[j]) for j in (0,1)]
                row['gate_paths']=[p if p is not None else [] for p in pp]
            certs.append(({'format':FORMAT,'nodes':nodes,'proof_rows':[row]},out))
    return certs


def main():
    assert __debug__,'Assertions must be enabled; do not use -O.'
    cases=controls();counts={'complete_controls':0,'complete_control_acceptances':0,
       'fixed_f_rejections':0,'codec_roundtrips':0,'malformed_mutations':0,
       'exhaustive_binary_words':0,'successful_structural_decodes':0}
    for cert,out in cases:
        old=P.verify_certificate(cert,T,goal=out)
        new=verify(cert,control_goal=out)
        assert old==new
        counts['complete_controls']+=1;counts['complete_control_acceptances']+=bool(new)
        assert not verify(cert);counts['fixed_f_rejections']+=1
        bits=Codec.encode(cert,T);decoded=Codec.decode(bits,T);assert decoded==cert
        assert not accepts(bits);counts['codec_roundtrips']+=1
        mutations=[]
        bad=copy.deepcopy(cert);bad['nodes'].append(['b',0,0,0]);mutations.append(bad)
        bad=copy.deepcopy(cert);bad['nodes'].append(['b',1,len(bad['nodes']),0]);mutations.append(bad)
        bad=copy.deepcopy(cert);bad['proof_rows']=[];mutations.append(bad)
        bad=copy.deepcopy(cert);bad['proof_rows'][-1]['tag']=12;mutations.append(bad)
        for bad in mutations:
            assert not verify(bad,control_goal=out)
            assert verify(bad,control_goal=out)==P.verify_certificate(bad,T,goal=out)
            counts['malformed_mutations']+=1
    for length in range(18):
        for bits in Codec.words_at_length(length):
            cert=Codec.decode(bits,T);counts['exhaustive_binary_words']+=1
            if cert is not None:
                counts['successful_structural_decodes']+=1
                assert verify(cert)==P.verify_certificate(cert,T)
                assert not verify(cert)
    result={'scope':'Complete exact finite-algorithm search reference, not full binary TM',
      'source_spec_sha256':O.EXPECTED_SPEC_HASH,**counts}
    (Path(__file__).parent/'oracle_search_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
