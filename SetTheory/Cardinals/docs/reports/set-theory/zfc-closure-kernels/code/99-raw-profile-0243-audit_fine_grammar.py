#!/usr/bin/env python3
"""Exact closed-token audit, independent of the C++ discovery program.

This validates source identities and local transparent routing. Full binary
simulation remains the separate all-instruction check in build_fine_machine.
"""
from collections import defaultdict
from functools import cache
from pathlib import Path
import hashlib
import json

BASE=Path(__file__).resolve().parents[1]
INPUTS=BASE/'inputs'
TABLE=BASE/'reference/context246/machine/zfc_prefix246_old.tm'

def make_vocabulary(override=None):
    source=json.loads((INPUTS/'closed-sequence-grammar-next22.json').read_text())
    symbols=json.loads((INPUTS/'semantic-symbols.json').read_text())
    ast=source['ast_dag']
    @cache
    def bounds(i):
        r=ast[i]
        if r[0]=='L':
            op,*a=r[1]
            return (1,0) if op=='dec' else (a[0],0) if op=='brk' else (0,a[0]) if op=='cont' else (0,0)
        a,b=map(bounds,r[1:])
        return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
    @cache
    def fine(i):
        r=ast[i]
        return fine(r[1])+fine(r[2]) if r[0]=='N' and bounds(r[1])==bounds(r[2])==(0,0) else (i,)
    raw={c:fine(source['atoms'][name]['ast']) for c,name in symbols.items()}
    assert all(bounds(source['atoms'][name]['ast'])==(0,0) for name in symbols.values())
    tokens=sorted(set(x for w in raw.values() for x in w))
    alphabet='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'
    assert len(tokens)<=len(alphabet)
    table={t:alphabet[k] for k,t in enumerate(tokens)}
    atom_words={c:''.join(table[t] for t in w) for c,w in raw.items()}
    terminals={w:symbols[c] for c,w in atom_words.items()}
    assert len(terminals)==len(raw)==44
    encode=lambda w: ''.join(atom_words[c] for c in w)
    inv={name:c for c,name in symbols.items()}
    names={int(q):encode(''.join(inv[x] for x in w)) for q,w in source['flattened_semantic_words'].items()}
    for q,i in source['sequence_ast_roots'].items():
        assert names[int(q)]==''.join(table[t] for t in fine(i)),q
    lines=(INPUTS/'semantic.txt').read_text().splitlines()
    n,nr,na=map(int,lines[0].split())
    allowed={atom_words[c]:int(m) for c,m in map(str.split,lines[1+n+nr:])}
    if override is not None:
        assert override['state']==76 and override['original_word']==names[76]
        revised=override['new_word']
        assert revised and set(revised)<=set(table.values())
        names[76]=revised
    return source,terminals,names,allowed,encode

def audit(path,short_scan=False,allow_scanner_risk=False):
    data=json.loads(path.read_text())
    source,terminals,names,allowed,encode=make_vocabulary(data.get('source_override'))
    permissions=data.get('terminal_orientation_relaxations',[])
    assert len({x['word']for x in permissions})==len(permissions)
    for change in permissions:
        w=change['word']
        assert w in terminals and allowed[w]==change['old_mask']
        assert source['atoms'][terminals[w]]['state']==change['state']
        assert change['new_mask']==3 and change['old_mask']in (1,2)
        allowed[w]=3
    # These are explicitly requested candidate permissions, not proved
    # interfaces. They are discharged only by actual-table all-case proofs.
    rules={w:(a,b) for w,a,b in data['rules']}
    assert len(rules)==len(data['rules'])==data['rules_count']
    assert not (set(rules)&set(terminals)), 'An atomic and pure-node implementation must be distinguished.'
    for w,(a,b) in rules.items():
        assert a and b and w==a+b
        for side,c in enumerate((a,b)):
            assert c in rules or c in terminals,(w,c)
            if c in terminals: assert allowed[c]&(1<<side),(w,side,c)
    def project(w,p):
        for bit in p:
            assert w in rules,('Routing enters a nontransparent atom',w,p)
            w=rules[w][int(bit)]
        return w
    table={}
    for line in TABLE.read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,t=line.split();table[int(q),int(b)]=(int(w),d,int(t))
    states={q for q,b in table};sequences=set(source['sequence_states'])
    assert len(states)==246 and len(table)==492
    assert {t for w,d,t in table.values()}-states=={254}
    for q in sequences:
        assert [table[q,b] for b in (0,1)]==[(b,'R',source['rules'][str(q)][b]) for b in (0,1)]
        assert sorted([p,b] for p,b in table if table[p,b][2]==q)==sorted(source['incoming'][str(q)])
    erase177=data.get('erase177',False)
    assert erase177 and data['retarget']==-2
    requested=bool(short_scan or data.get('short_scan',False))
    erased={177}|({74} if requested else set())
    assert table[177,0]==(0,'R',175) and table[177,1]==(1,'R',207)
    assert {(q,b) for q,b in table if table[q,b][2]==177}=={(153,1),(159,0)}
    if requested:
        assert table[58,0]==(0,'L',74)
        assert table[74,0]==(0,'L',84) and table[74,1]==(1,'L',4)
        assert {(q,b) for q,b in table if table[q,b][2]==74}=={(58,0)}
    groups=defaultdict(list)
    symbols=json.loads((INPUTS/'semantic-symbols.json').read_text())
    inv={name:c for c,name in symbols.items()}
    for c in source['left_entry_projection_constraints']:
        reason=c['reason'];assert 'via' not in reason or reason['via']==177
        groups[reason['source'],reason['read']].append(c)
    routes={(r['source'],r['read']):r['word'] for r in data['routes']}
    assert len(routes)==len(data['routes']) and set(routes)==set(groups)
    assert all(w in rules for w in routes.values())
    traces=[]
    for key,cs in groups.items():
        assert {c['reason']['previous'] for c in cs}=={0,1}
        w,d,old_entry=table[key];assert d=='L'
        for c in cs:
            reason=c['reason'];assert w==reason['write']
            p=(str(reason['previous']) if 'via' in reason else '')+c['prefix']
            assert 1<=len(p)<=2 and p==(str(reason['previous'])+str(w))[:len(p)]
            endpoint=old_entry
            for b in p:
                assert table[endpoint,int(b)][:2]==(int(b),'R')
                endpoint=table[endpoint,int(b)][2]
            target=encode(''.join(inv[x] for x in c['word']))
            assert project(routes[key],p)==target
            if target in terminals:
                assert source['atoms'][terminals[target]]['state']==endpoint
            else: assert names[endpoint]==target
            traces.append(dict(caller=list(key),previous=reason['previous'],prefix=p,target=target))
    released=[]
    for q in source['required_entry_roots']:
        edges=[tuple(e) for e in source['incoming'][str(q)] if e[0] not in sequences]
        if edges and all(e in routes or e[0] in erased for e in edges):released.append(q)
        elif q not in erased:assert names[q] in rules,q
    for key,(w,d,t) in table.items():
        if key[0] in sequences|erased or key in routes or (requested and key==(58,0)):continue
        assert t not in erased
        if t in sequences:assert names[t] in rules,t
    assert names[96] in rules
    locks=(BASE/'inputs/state_reduction/bootstrap-lock54.txt').read_text().splitlines()
    assert len(locks)-1==int(locks[0])==54
    permitted_relaxation = {
        ('eijkKCqkjGeU','0','eijkKCqkjGe'),
        ('eijkKCqkjGeU','1','U'),
        ('eijkKCqkjGe','0','eijkKCqkjG'),
        ('eijkKCqkjGe','1','e'),
    }
    original_locks={tuple(row.split()) for row in locks[1:]}
    declared={(x['word'],str(x['bit']),x['target'])
              for x in data.get('bootstrap_projection_relaxations',[])}
    assert declared<=original_locks
    assert len(declared)==len(data.get('bootstrap_projection_relaxations',[]))
    permitted_relaxation |= declared
    # Four previously audited relaxed interfaces are inherited.  Any further
    # omissions must be declared row by row in candidate metadata.  This
    # structural check makes no initialization claim; the actual blank run is
    # an independent proof obligation for every newly compiled table.
    observed_relaxation=set(); checked_locks=0
    for w,b,t in map(str.split,locks[1:]):
        if (w,b,t) in permitted_relaxation:
            observed_relaxation.add((w,b,t));continue
        assert project(encode(w),b)==encode(t),(w,b,t)
        checked_locks+=1
    assert observed_relaxation==permitted_relaxation
    assert checked_locks==54-len(permitted_relaxation)
    old={}
    _,_,immutable_names,_,_=make_vocabulary()
    for q,ab in source['rules'].items():
        if int(q) not in sequences:continue
        # Original words are reconstructed through the source's fixed symbol words.
        line=next(x for x in (INPUTS/'semantic.txt').read_text().splitlines()[1:128] if x.split()[2]==q)
        k,w,_=line.split();k=int(k);old[immutable_names[int(q)]]=(encode(w[:k]),encode(w[k:]))
    by_ast={int(i):names[int(q)] for q,i in source['sequence_ast_roots'].items()}
    visiting=set()
    def join(a,b):return 1+a[0],max(1+a[0],a[1],b[1]),1+max(a[2],b[2])
    @cache
    def astprop(i):
        key=('ast',i);assert key not in visiting;visiting.add(key)
        r=source['ast_dag'][i]
        result=wordprop(by_ast[i]) if i in by_ast else (0,0,0) if r[0]=='L' else join(astprop(r[1]),astprop(r[2]))
        visiting.remove(key);return result
    @cache
    def wordprop(w):
        key=('word',w);assert key not in visiting;visiting.add(key)
        if w in terminals: result=astprop(source['atoms'][terminals[w]]['ast'])
        else:
            a,b=rules[w] if w in rules else old[w];result=join(wordprop(a),wordprop(b))
        visiting.remove(key);return result
    props=astprop(source['original_ast'])
    assert (not data['properties'] or list(props)==data['properties']) and props[2]<=64
    if requested and not allow_scanner_risk:assert props[1]<=6
    live=set()
    def visit(w):
        if w in terminals or w in live:return
        assert w in rules;live.add(w)
        for c in rules[w]:visit(c)
    for q in source['required_entry_roots']:
        if q not in released:visit(names[q])
    for w in routes.values():visit(w)
    return dict(status='PASS_STRUCTURAL_GRAMMAR_ORIENTATION_RELAXED' if permissions else 'PASS_FINE_GRAMMAR',candidate=str(path),
      terminal_orientation_relaxations=permissions,
      orientation_scope='Candidate permissions require actual-table all-case proofs' if permissions else 'Inherited checked entry masks',
      grammar_states=len(rules),framework_states=len(states-sequences-erased),
      working_states=len(rules)+len(states-sequences-erased),
      local_routing_cases=len(traces),route_traces=traces,
      root_word_override_checks=[],fine_tokens=30,closed_atoms=44,
      boot_lock_projections=checked_locks,
      relaxed_bootstrap_interfaces=sorted(permitted_relaxation),
      bootstrap_scope="Exact blank simulation is separately required",unreachable_but_charged_rules=sorted(set(rules)-live),
      search_AST_properties=dict(leading_zeros=props[0],maximum_zero_run=props[1],depth=props[2]),
      source_override=data.get('source_override'),
      source_meaning_scope='AX replacement needs its separate logical calibration' if data.get('source_override') else 'Unchanged exact source',
      candidate_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
