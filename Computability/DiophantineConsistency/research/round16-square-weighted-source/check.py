#!/usr/bin/env python3
"""CODE ONLY / HOLD: independent literal quadratic-source audit; no producer import."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CORE = {'build.py','check.py','PROOF.md','README.md','BOUNDARY.md','COPIED_INPUTS.json','ARCHIVE_MEMBERS.json'}
SEALS = {'research/round16-square-radix-compression':'aeb8e0988d86b7dd08e15e7db439ba1122a7095a93b311e26e07d2caaf5dabad',
         'research/round16-weighted-guard-products':'66d5c89f48f5d8a7fc2f13f86205c46ddff52b4821a6c1683188fc93d8772ce3'}
REPAIRS = [(183,184,164,165,412),(191,192,169,170,413),(197,198,172,173,414),
           (202,203,175,176,415),(207,208,178,179,416),(213,214,182,183,417),
           (219,220,185,186,418),(225,226,189,190,419),(231,232,192,193,420),
           (236,237,196,197,421),(242,243,199,200,422)]
DELETED_ROWS = {398,*range(401,410)}
DELETED_COORDS = [*range(541,544),*range(550,577)]
CALL_ROWS = [217,228,233,244,250,258,266,274,282,290,298,306,314,322,330,338,346,354]
TS = [268,285,291,307,313,307,313,307,307,307,307,313,307,307,313,307,307,307]
CALL_SEEDS = [0,1,1,2,0,3,0,4,5,6,7,8,9,10,11,12,13,14]
PAIRS = [(257,258),(274,275),(296,297),(319,320),(341,342),(355,356),(369,370),
         (383,384),(397,398),(411,412),(425,426),(439,440),(453,454),(467,468),(481,482)]
SCOPE = 'Literal quadratic source only; ordinary Hstar/remainder/strict-product contracts retained; no projection, quartic or frontier claim.'


def need(ok,message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(x):
    return (json.dumps(x,indent=2,sort_keys=True)+'\n').encode()


def load(p):
    return json.loads(p.read_bytes())


def closed(folder,manifest):
    entries = load(manifest)['files']
    need({p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file() and p!=manifest}==set(entries), 'Whole closed inventory')
    for name,record in entries.items():
        p = folder/name
        raw = p.read_bytes()
        need(not p.is_symlink() and digest(raw)==(record if isinstance(record,str) else record['sha256']), 'Whole closed member '+name)
        need(isinstance(record,str) or len(raw)==record['bytes'], 'Whole closed member length')


def authenticate():
    pins = load(HERE/'SOURCE_PINS.json')
    need(set(pins['core'])==CORE and pins['required_seals']==SEALS, 'Exact reviewed core and ordinary contracts')
    for key,folder in [('core',HERE),('external_whole_files',ROOT)]:
        for name,record in pins[key].items():
            p = folder/name
            raw = p.read_bytes()
            need(not p.is_symlink() and digest(raw)==record['sha256'] and len(raw)==record['bytes'], 'Entire reviewed file '+name)
    for name,seal in SEALS.items():
        folder = ROOT/name
        need(digest((folder/'MANIFEST.json').read_bytes())==seal, 'Exact ordinary theorem seal')
        closed(folder,folder/'MANIFEST.json')
    copies = load(HERE/'COPIED_INPUTS.json')['files']
    actual = {p.relative_to(HERE).as_posix() for name in ['inputs','provenance'] for p in (HERE/name).rglob('*') if p.is_file() or p.is_symlink()}
    need(actual==set(copies), 'Every exact input copy declared')
    for name,record in copies.items():
        p = HERE/name
        raw = p.read_bytes()
        need(not p.is_symlink() and raw==(ROOT/record['source']).read_bytes() and digest(raw)==record['sha256'] and len(raw)==record['bytes'], 'Whole accepted copy '+name)
    archive = load(HERE/'ARCHIVE_MEMBERS.json')
    need(archive['archive_sha256']=='97c828ef295d52ea53800dc0761e94cc5605dec306aae3eeecef1d074fa254f8' and
         archive['git_blob']=='d48000bbfe86ad6a3d8ade43f8bdfd19d20f33d7' and
         archive['commit']=='fd3e384e92ed4813a5536f877c5cd835ca4c75d2', 'Exact original archive provenance')
    source_prefix = 'con-zfc-diophantine-forms/131-shared-pell-caps-round16/'
    need(set(archive['members'])=={n for n,r in copies.items() if r['source'].startswith(source_prefix)}, 'Every selected source131 member has whole original-archive provenance')
    for local,record in archive['members'].items():
        need(local in copies and record['sha256']==copies[local]['sha256'] and record['bytes']==copies[local]['bytes'], 'Original member binds entire exact copy')
        need(record['member']=='ConZFC_Shared_Pell_Caps_Round16_2026-10-25/'+copies[local]['source'][len(source_prefix):], 'Exact original member path, not a duplicate dependency member')
    if (HERE/'MANIFEST.json').exists():
        closed(HERE,HERE/'MANIFEST.json')
    return pins


def C(n):
    return {():n} if n else {}


def V(v):
    return {(v,):1}


def add(a,b,sign=1):
    out = dict(a)
    for m,c in b.items():
        out[m] = out.get(m,0)+sign*c
    return {m:c for m,c in out.items() if c}


def mul(a,b):
    out = {}
    for m,c in a.items():
        for n,d in b.items():
            key = tuple(sorted(m+n))
            out[key] = out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}


def poly(terms):
    need(type(terms) is list, 'Actual term list')
    out = {}
    for term in terms:
        need(type(term) is list and len(term)==2 and type(term[0]) is int and term[0]!=0 and type(term[1]) is list and
             all(type(v) is int and v>=0 for v in term[1]), 'Literal integral term')
        c,m = term
        key = tuple(sorted(m))
        out[key] = out.get(key,0)+c
    return {m:c for m,c in out.items() if c}


def terms(p):
    return [[c,list(m)] for m,c in sorted(p.items())]


def affine(v):
    return add(C(1),V(v))


def change(p,mapping):
    out = {}
    for monomial,c in p.items():
        key = tuple(sorted(mapping[v] for v in monomial))
        out[key] = out.get(key,0)+c
    return {m:c for m,c in out.items() if c}


def occurrences(rows,v):
    return [i for i,r in enumerate(rows) if any(v in m for _,m in r['terms'])]


def source_binding(source,old,cert):
    need(len(source['variables'])==541 and len(source['residuals'])==398 and len(old['variables'])==622 and len(old['residuals'])==425, 'Exact entire input namespace')
    need(old['variables'][:541]==source['variables'] and old['residuals'][:398]==source['residuals'], 'Whole raw prefix of guarded input')
    need({k:v for k,v in source.items() if k not in ['variables','residuals']}=={k:v for k,v in old.items() if k not in ['variables','residuals']}, 'Every input header field')
    need(cert['source_sha256']==digest((HERE/'inputs/source.json').read_bytes()), 'Certificate binds the entire actual raw source')
    need(occurrences(old['residuals'],175)==[158], 'Entire old private N-square occurrence set')
    need(poly(source['residuals'][158]['terms'])==add(V(175),mul(V(26),V(26)),-1), 'Exact old N-square definition')
    for r,s,d,b,g in REPAIRS:
        need(occurrences(source['residuals'],r)==[d,b], 'Every raw remainder occurs only in two rows')
        for row in [d,b]:
            p = poly(source['residuals'][row]['terms'])
            need(p.get((r,))==-1 and all(r not in m or m==(r,) for m in p), 'Exact linear coefficient for residue-one repair')
        guard = cert['guards'][g-398]
        need(guard['row']==g and guard['pair']==[r,s] and guard['bound_row']==b, 'All eleven exact guard interfaces')
        for v in guard['auxiliary']:
            need(occurrences(old['residuals'],v)==[g], 'Whole interval auxiliary privacy')
    removed,all_aux = [],[]
    scalar_meanings = {398:1,399:7,400:8,**{401+i:16+i for i in range(9)},410:185,411:246,423:532}
    need([g['row'] for g in cert['guards']]==list(range(398,425)), 'Every original guard in exact original order')
    for guard in cert['guards']:
        row,aux = guard['row'],guard['auxiliary']
        need(len(aux)==3, 'Complete Legendre triple')
        all_aux += aux
        for v in aux:
            need(occurrences(old['residuals'],v)==[row], 'Every old guard auxiliary private in the whole source')
        if row in scalar_meanings:
            need(poly(guard['expression'])==V(scalar_meanings[row]), 'Exact retained/removed scalar guard meaning')
        if row==424:
            cap_expression = add(add(V(525),V(245),-1),C(1),-1)
            for _,y in PAIRS:
                cap_expression = add(cap_expression,mul(V(y),V(y)),-1)
            need(poly(guard['expression'])==cap_expression, 'Entire positive linear cap predicate')
        a,b,c = aux
        expected = add(poly(guard['expression']),add(add(mul(V(a),V(a)),mul(V(b),V(b))),add(mul(V(c),V(c)),V(c))),-1)
        need(poly(old['residuals'][row]['terms'])==expected, 'Every exact original guard graph')
        if row in DELETED_ROWS:
            removed += aux
            for v in aux:
                need(occurrences(old['residuals'],v)==[row], 'Every removed scalar auxiliary private')
    need(sorted(removed)==DELETED_COORDS, 'Only x and nine CRT scalar triples removed')
    need(sorted(all_aux)==list(range(541,622)), 'All 81 exact original private guard witnesses')
    for v,expected in [(139,[123,124,132]),(140,[124,129]),(141,[125,127]),(143,[127,128])]:
        need(occurrences(old['residuals'],v)==expected, 'Whole weighted-pair gate occurrence set')
    a,b,S,Sp,F = affine(16),affine(17),affine(20),affine(21),V(3)
    EA,EB = add(V(143),S,-1),add(V(140),Sp,-1)
    need(add(EA,mul(mul(F,a),S),-1)==add(poly(source['residuals'][127]['terms']),mul(S,poly(source['residuals'][125]['terms']))), 'Entire first weighted-pair ideal identity')
    need(add(EB,mul(mul(F,b),Sp),-1)==add(poly(source['residuals'][124]['terms']),mul(Sp,poly(source['residuals'][123]['terms']))), 'Entire second weighted-pair ideal identity')
    need(add(add(V(148),S,-1),mul(mul(F,b),S),-1)==add(poly(source['residuals'][132]['terms']),mul(S,poly(source['residuals'][123]['terms']))), 'Entire bounded-search third weighted-pair identity')
    return {'eleven_remainder_privacies':len(REPAIRS),'removed_scalar_private_coordinates':removed,'weighted_ideal_identities':3,'old_private175_occurrences':[158]}


def expected_calls():
    t,k,q = add(C(16),V(0)),{(25,):2},V(179)
    records = [(affine(4),t,V(6)),(V(5),k,V(26)),(V(522),k,q),
               (affine(179),add(t,V(4)),V(180)),(q,t,V(181)),(affine(179),affine(16),V(188)),
               (q,add(C(17),V(0)),V(189))]
    records += [(affine(179),affine(v),V(o)) for v,o in [(17,195),(18,200),(19,205),(20,210)]]
    records += [(q,affine(2),V(211)),(affine(179),affine(21),V(217)),(affine(179),affine(22),V(222)),
                (q,affine(1),V(223)),(affine(179),affine(23),V(229)),(affine(179),affine(24),V(234)),(affine(179),affine(171),V(240))]
    return records


def context_audit(context,source,cert):
    rows = source['residuals']
    calls = expected_calls()
    need(cert['square_budget']['power_calls']==[{'base':terms(a),'exponent':terms(k),'output':terms(m)} for a,k,m in calls], 'All eighteen independently stated actual request ports')
    atoms = {tuple(sorted(a.items())):a for call in calls for a in call}
    need(len(calls)*3==54 and len(atoms)==38, 'Exact 54-port/38-distinct-atom census')
    need({tuple(sorted(poly(a['affine']).items())) for a in cert['square_budget']['atoms']}==set(atoms), 'Whole affine atom union')
    frame = add(V(245),C(2),-1)
    for a in atoms.values():
        frame = add(frame,mul(a,a),-1)
    need(poly(rows[381]['terms'])==frame, 'Entire expanded squared frame polynomial')
    need([tuple(s['pair']) for s in cert['seed_data']]==PAIRS and len(cert['seed_data'])==15, 'All fifteen primary seeds')
    for j,seed in enumerate(cert['seed_data']):
        used = [i for i,s in enumerate(CALL_SEEDS) if s==j and i!=6]
        need(seed['calls']==used and poly(seed['exponent'])==calls[used[0]][1], 'Every target/seed alias; derived call6 excluded from a fresh seed')
    definitions = {}
    for v,record in enumerate(source['variables']):
        if record['kind']!='gate':
            continue
        for row in rows:
            p = poly(row['terms'])
            if p.get((v,))==1 and all(v not in m or m==(v,) for m in p):
                definitions[v] = add(V(v),p,-1)
                break
    def expand(p,boundary):
        memo = {v:V(v) for v in boundary}
        active = set()
        def node(v):
            if v in memo:
                return memo[v]
            need(v in definitions and v not in active, 'Only finite monic helper definitions expanded')
            active.add(v)
            memo[v] = expression(definitions[v])
            active.remove(v)
            return memo[v]
        def expression(q):
            out = {}
            for m,c in q.items():
                part = C(c)
                for v in m:
                    part = mul(part,node(v))
                out = add(out,part)
            return out
        return expression(p)
    # The derived recurrence's D is metadata-kind witness, but these two
    # exact rows prove its definition. It is the sole explicit exception.
    need(poly(rows[259]['terms'])==add(V(334),mul(V(246),V(246)),-1) and
         poly(rows[260]['terms'])==add(add(V(334),V(333),-1),C(1),-1), 'Exact derived D=A^2-1 lowering')
    definitions[333] = add(mul(V(246),V(246)),C(1),-1)
    nongates = {v for v,r in enumerate(source['variables']) if r['kind']!='gate'}-{333}
    norm_indices = []
    for x,y in PAIRS:
        want = add(add(add(mul(V(x),V(x)),mul(V(y),V(y))),mul(mul(V(246),V(246)),mul(V(y),V(y))),-1),C(1),-1)
        candidates = [i for i,r in enumerate(rows) if r['label'].endswith('.norm1') and expand(poly(r['terms']),nongates|{x,y,246})==want]
        need(len(candidates)==1, 'Whole primary Pell norm at actual coordinates')
        norm_indices += candidates
    request_records = []
    for i,(n,k,m) in enumerate(calls):
        x,y = PAIRS[CALL_SEEDS[i]]
        boundary = nongates|{v for a in [n,k,m] for mon in a for v in mon}|{x,y,246}
        actual = expand(poly(rows[CALL_ROWS[i]]['terms']),boundary)
        T = TS[i]
        quotients = [other for mon,c in actual.items() if c==-1 and len(mon)==2 and T in mon for other in mon if other!=T]
        need(len(quotients)==1, 'One actual T-divisibility witness')
        d = quotients[0]
        if i==6:
            want = add(add(mul(V(179),V(x)),mul(mul(V(179),V(246)),V(y))),V(y),-1)
        else:
            want = add(V(x),mul(V(246),V(y)),-1)
            want = add(want,mul(n,V(y)))
        want = add(add(want,m,-1),mul(V(T),V(d)),-1)
        need(actual==want, 'Entire joined power congruence, including actual t+1 recurrence')
        request_records.append({'call':i,'row':CALL_ROWS[i],'T':T,'quotient':d,'joined_terms':len(actual)})
    modulus_records = []
    for T in sorted(set(TS)):
        n = calls[TS.index(T)][0]
        boundary = nongates|{v for mon in n for v in mon}
        expected_T = add(add(mul(mul(C(2),V(246)),n),mul(n,n),-1),add(V(T),C(1)),-1)
        indices = [i for i,r in enumerate(rows) if r['label'].endswith('.T_definition') and
                   expand(poly(r['terms']),boundary)==expected_T]
        need(len(indices)==1, 'Every entire shared T=2An-n^2-1 definition')
        modulus_records.append({'T':T,'definition_row':indices[0]})
    for index,x,y,parameter in [(386,524,525,246),(388,526,527,246),(390,528,529,530)]:
        expected_norm = add(add(add(mul(V(x),V(x)),mul(V(y),V(y))),mul(mul(V(parameter),V(parameter)),mul(V(y),V(y))),-1),C(1),-1)
        need(expand(poly(rows[index]['terms']),nongates|{x,y,parameter})==expected_norm, 'Whole complete-anchor norm identity')
    expected = {'namespace':'Original source131 indices; ROW_MAPS supplies every active profile index. Certificate tokens/stale addresses are provenance only.',
                'old_source_sha256':digest((HERE/'inputs/source.json').read_bytes()),'old_guarded_sha256':digest((HERE/'inputs/guarded.json').read_bytes()),
                'actual_frame_row':381,'stale_certificate_frame_address':cert['square_budget']['frame_row'],
                'power_calls':cert['square_budget']['power_calls'],'frame_atoms':cert['square_budget']['atoms'],'seed_data':cert['seed_data'],
                'guards':cert['guards'],'cap_variables':cert['cap_variables'],
                'primary_norm_rows':[{'index':i,'row':r} for i,r in enumerate(rows) if r['label'].endswith('.norm1')],
                'shared_T_rows':[{'index':i,'row':r} for i,r in enumerate(rows) if r['label'].endswith('.T_definition')],
                'request_rows':[{'call':j,'index':i,'row':rows[i]} for j,i in enumerate(CALL_ROWS)],
                'derived_t_recurrence_rows':[{'index':i,'row':rows[i]} for i in range(259,267)],
                'early_rows':[{'index':i,'row':rows[i]} for i in [1,2,3,11,12,201,202,203,383,384]],
                'cap_rows':[{'index':i,'row':rows[i]} for i in range(385,398)]}
    need(encoded(context)==encoded(expected) and len(norm_indices)==15, 'Entire typed source context, cap/pool and actual row bindings')
    pool = {}
    for seed in cert['seed_data']:
        difference = add(V(seed['pair'][1]),poly(seed['exponent']),-1)
        pool = add(pool,mul(difference,difference))
    pool = add(pool,V(540))
    pool = add(pool,mul(V(246),V(540)),-1)
    need(poly(rows[397]['terms'])==pool, 'Entire original primary-only pooled residue row')
    return {'actual_requests':request_records,'shared_T_definitions':modulus_records,'primary_norm_rows':norm_indices,
            'request_ports':54,'distinct_frame_atoms':38,'cap_norms':[386,388,390],'cap_rows':list(range(385,398)),'pooled_row':397}


def quadratic_rows(packet):
    need(type(packet['variables']) is list and type(packet['residuals']) is list, 'Whole variable and residual lists')
    used = set()
    maximum = 0
    for row in packet['residuals']:
        need(type(row) is dict and set(row)=={'label','terms'} and type(row['label']) is str, 'Entire typed residual row')
        p = poly(row['terms'])
        need(row['terms']==terms(p), 'Collected nonzero canonical integer row')
        for m in p:
            need(len(m)<=2 and all(v<len(packet['variables']) for v in m), 'Every actual row quadratic and every coordinate declared')
            used.update(m)
            maximum = max(maximum,len(m))
    return {'variables':len(packet['variables']),'rows':len(packet['residuals']),'max_row_degree':maximum,
            'raw_unconstrained_coordinates':[i for i in range(len(packet['variables'])) if i not in used]}


def profile_audit(packet,declaration,which,old,pins):
    census = quadratic_rows(packet)
    retained = [i for i in range(len(old['variables'])) if i not in DELETED_COORDS]
    mapping = {v:i for i,v in enumerate(retained)}
    need(all(mapping[v]==v for v in range(541)), 'Every original kernel coordinate preserved before old guard compaction')
    expected_variables = [deepcopy(old['variables'][i]) for i in retained]
    expected_variables[175]['name'] = 'radix.Hstar.reused_private_175'
    for r,_,_,_,_ in REPAIRS:
        expected_variables[r]['name'] += '.residue_one_quotient'
    replacements = {158:add(V(175),C(2),-1),382:add(V(522),mul(V(5),V(175)),-1)}
    for v in range(16,25):
        replacements[158] = add(replacements[158],mul(V(v),V(v)),-1)
    for r,_,d,b,_ in REPAIRS:
        for row in [d,b]:
            p = add(poly(old['residuals'][row]['terms']),V(r))
            replacements[row] = add(add(p,C(1),-1),mul(V(179),V(r)),-1)
    entries,expected_rows = [],[]
    for i,row in enumerate(old['residuals']):
        newrow,j = None,None
        action = 'deleted_scalar_guard'
        if i not in DELETED_ROWS:
            wanted = replacements.get(i,poly(row['terms']))
            newrow = dict(row,terms=terms(change(wanted,mapping)))
            j = len(expected_rows)
            expected_rows.append(newrow)
            action = 'replaced_body' if i in replacements else 'retained'
        entries.append({'old_index':i,'old_row':row,'action':action,'new_index':j,'new_row':newrow})
    need(packet['residuals'][:len(expected_rows)]==expected_rows, 'Every whole retained/replaced/deleted original row, including all guards and cap')
    if which=='plain':
        factors = [affine(mapping[v]) for v in range(16,24)]
        abstract_factors = [V(v) for v in range(16,24)]
    else:
        factors = [add(V(mapping[143]),affine(mapping[20]),-1),add(V(mapping[140]),affine(mapping[21]),-1)]
        factors += [affine(mapping[v]) for v in [18,19,22,23]]
        abstract_factors = [mul(mul(V(3),V(16)),V(20)),mul(mul(V(3),V(17)),V(21))]+[V(v) for v in [18,19,22,23]]
    new_rows = []
    left,abstract = factors[0],abstract_factors[0]
    for offset in range(1,len(factors)):
        output = len(expected_variables)
        j = offset+1
        expected_variables.append({'kind':'gate','name':f'strict8.{which}.partial.{j}'})
        want = add(V(output),mul(left,factors[offset]),-1)
        row = {'label':f'strict8.{which}.partial.{j}','terms':terms(want)}
        new_rows.append({'index':len(expected_rows),'row':row,'output':output})
        expected_rows.append(row)
        left = V(output)
        abstract = mul(abstract,abstract_factors[offset])
    expected_abstract = C(1)
    for v in range(16,24):
        expected_abstract = mul(expected_abstract,V(v))
    if which=='weighted':
        expected_abstract = mul(mul(V(3),V(3)),expected_abstract)
    need(abstract==expected_abstract, 'Entire chain consequence P8 or F^2*P8 at independent semantic factors')
    root = next(iter(left))[0]
    aux = list(range(len(expected_variables),len(expected_variables)+3))
    expected_variables += [{'kind':'integer_guard','name':f'guard.fused_x_strict8.{which}.{letter}'} for letter in ['a','b','c']]
    expr = add(mul(affine(mapping[1]),V(root)),C(1),-1)
    a,b,c = aux
    guard = add(expr,add(add(mul(V(a),V(a)),mul(V(b),V(b))),add(mul(V(c),V(c)),V(c))),-1)
    row = {'label':f'guard.fused_x_strict8.{which}','terms':terms(guard)}
    new_rows.append({'index':len(expected_rows),'row':row,'auxiliary':aux})
    expected_rows.append(row)
    need(packet['residuals']==expected_rows and packet['variables']==expected_variables, 'Entire actual source and every typed variable, including new definitions/triple')
    expected_map = {'old_to_new':[mapping.get(i) for i in range(len(old['variables']))],
        'new_to_old':retained+[None]*(len(expected_variables)-len(retained)),'removed_coordinates':DELETED_COORDS,
        'variables':[{'old_index':i,'old_metadata':old['variables'][i],'new_index':mapping.get(i),
                      'new_metadata':None if i not in mapping else expected_variables[mapping[i]]} for i in range(len(old['variables']))],
        'rows':entries,'new_rows':new_rows,'new_product_root':root,'new_guard_auxiliary':aux}
    need(encoded(declaration)==encoded(expected_map), 'Complete coordinate/row/metadata inverse maps and new-row privacy')
    expected_header = deepcopy(old)
    expected_header.update(variables=expected_variables,residuals=expected_rows,
        variant=old['variant']+':Hstar_reused175:residue_one:'+which,
        literal_policy={'profile':which,'parent_sha256':digest((HERE/'inputs/guarded.json').read_bytes()),
                        'source_sha256':digest((HERE/'inputs/source.json').read_bytes()),'ordinary_seals':SEALS,'scope':SCOPE})
    need(encoded(packet)==encoded(expected_header), 'Entire new and retained historical source metadata')
    for output in [entry['output'] for entry in new_rows if 'output' in entry]:
        expected = [entry['index'] for entry in new_rows if any(output in mon for _,mon in entry['row']['terms'])]
        need(occurrences(packet['residuals'],output)==expected, 'No unexpected partial-product consumer or frame inclusion')
    for v in aux:
        need(occurrences(packet['residuals'],v)==[len(expected_rows)-1], 'Fresh fused triple private in whole source')
    record = {'profile':which,**census,'scope':'Literal raw source only; no all-variable-liveness or projected/frontier claim.'}
    return record,{'profile':which,'all_old_rows':len(entries),'new_partial_products':len(factors)-1,'new_guard_auxiliary':aux,
                   'old_body_coordinate_indices_preserved':all(mapping[v]==v for v in range(541)),
                   'complete_chain_semantic_monomial':terms(abstract),'new_root':root}


def witness_metadata(value):
    expected = {'removed_scalar_guards':sorted(DELETED_ROWS),'removed_private_coordinates':DELETED_COORDS,
        'remainder_records':[{'raw_remainder':r,'new_quotient_same_slot':r,'slack':s,'digit_row':d,'bound_row':b,'interval_guard':g,
            'raw_from_new':'r=1+q*u','new_from_complete_Hstar_raw':'u=(r-1)/q',
            'interval_triples':'Fresh in both directions; represented integers change from r*s to u*s.'} for r,s,d,b,g in REPAIRS],
        'private_175':{'new_value':'2+sum(v16^2,...,v24^2)','old_Nsq_restore':'v26^2',
            'fresh_Hstar_view':'Copy reused175 to a fresh Hstar coordinate; restore old private175=N^2.'},
        'strict_products':{'plain':'P8','weighted':'F^2*P8','fresh_extensions':'Unique unrestricted partial products, fresh Legendre triples.'},
        'source_boundary':'Pointwise common Hstar/repaired kernel, not old H0 tuples. Decode/refutation and fresh canonical construction transfer the H0 architecture.',
        'scalar_restore':'After signed-request residue recovery, weighted/plain fused strict support restores x and all CRT scalar signs; choose fresh old scalar triples.',
        'unaffected_witnesses':'Fixed through coordinate compaction; eleven interval witnesses and removed scalar witnesses are explicitly excluded.'}
    need(encoded(value)==encoded(expected), 'Every existential witness-map instruction; no false identity of changed private witnesses')


def calibration(value):
    expected = {'ordinary_seals':SEALS,
        'source131_proof_sha256':digest((HERE/'provenance/direct-proof.md').read_bytes()),
        'architecture_proof_sha256':digest((HERE/'provenance/architecture-proof.md').read_bytes()),
        'scope':'Exact retained source131/Round15/C222/ZF-to-ZFC ordinary contract; no incoming compiler/native runtime replay, old327 body identity or old324 polynomial identity.',
        'future_projection':'Separate proof, code reviews and release required; no factoring, elimination, translation or quartic here.'}
    need(encoded(value)==encoded(expected), 'Complete direct ordinary/source calibration and explicit excluded claims')


def data_inventory(folder):
    names = {'data/plain.json','data/weighted.json','data/ROW_MAPS.json','data/SOURCE_CONTEXT.json',
             'data/WITNESS_MAPS.json','data/CALIBRATION_BINDING.json','data/METRICS.json'}
    need(not (folder/'data').is_symlink(), 'No generated directory symlink')
    index = load(folder/'data/INDEX.json')
    need(set(index)=={'schema','producer_sha256','source_pins_sha256','files'} and
         index['schema']=='round16_two_literal_quadratic_sources_v1' and set(index['files'])==names, 'Entire index schema/eight-file scope')
    need(index['producer_sha256']==digest((HERE/'build.py').read_bytes()) and
         index['source_pins_sha256']==digest((HERE/'SOURCE_PINS.json').read_bytes()), 'Whole producer and pin binding')
    actual = {p.relative_to(folder).as_posix() for p in (folder/'data').rglob('*') if p.is_file() or p.is_symlink()}
    need(actual==names|{'data/INDEX.json'}, 'Every actual generated file indexed')
    for name,record in index['files'].items():
        p = folder/name
        raw = p.read_bytes()
        need(set(record)=={'bytes','sha256'} and not p.is_symlink() and len(raw)==record['bytes'] and digest(raw)==record['sha256'], 'Whole actual artifact '+name)


def controls(packets,maps,old,pins,context,source,cert,witnesses):
    rejected,positives = [],[]
    def reject(label,action):
        try:
            action()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise ValueError('Actual mutation not rejected: '+label)
    for which in ['plain','weighted']:
        packet,decl = packets[which],maps[which]
        translated = {x['old_index']:x['new_index'] for x in decl['rows']}
        changes = [('source domain',lambda p:p.update(domain='natural numbers')),
                   ('historical header',lambda p:p.update(source_commit='0'*40)),
                   ('ordinary seal',lambda p:p['literal_policy']['ordinary_seals'].update({next(iter(SEALS)):'0'*64})),
                   ('old Nsquare name',lambda p:p['variables'][175].update(name='mul.385')),
                   ('raw remainder meaning',lambda p:p['variables'][183].update(name=old['variables'][183]['name'])),
                   ('missing final cap/guard row',lambda p:p['residuals'].pop()),
                   ('fused triple alias',lambda p:p['residuals'][-1]['terms'].__setitem__(0,[1,[7]]))]
        for label,alter in changes:
            bad = deepcopy(packet)
            alter(bad)
            with TemporaryDirectory(prefix='round16-source-mutation-') as temporary:
                path = Path(temporary)/'actual.json'
                path.write_bytes(encoded(bad))
                reject(which+': '+label,lambda:profile_audit(load(path),decl,which,old,pins))
        for label,oldrow,monomial in [('Hstar square coefficient',158,(16,16)),('self radix wrong factor',382,(5,175)),
                                     ('digit residue constant',164,()),('bound residue constant',165,()),
                                     ('frame N square',381,(26,26)),('cap pooled Y square',397,(258,258)),
                                     ('primary power congruence',217,(6,)),('retained factorial graph',399,(7,))]:
            bad = deepcopy(packet)
            row = bad['residuals'][translated[oldrow]]
            pp = poly(row['terms'])
            pp[monomial] = pp.get(monomial,0)+1
            row['terms'] = terms(pp)
            reject(which+': '+label,lambda:profile_audit(bad,decl,which,old,pins))
        bad = deepcopy(packet)
        row = bad['residuals'][translated[412]]
        row['terms'] = terms(add(poly(row['terms']),{(179,183,184):1}))
        reject(which+': cubic naive old interval substitution',lambda:profile_audit(bad,decl,which,old,pins))
        bad = deepcopy(packet)
        row = bad['residuals'][decl['new_rows'][0]['index']]
        pp = poly(row['terms'])
        pp[()] = pp.get((),0)+1
        row['terms'] = terms(pp)
        reject(which+': actual first product',lambda:profile_audit(bad,decl,which,old,pins))
        for label,key in [('coordinate inverse','new_to_old'),('removed coordinate set','removed_coordinates')]:
            bad = deepcopy(decl)
            bad[key][0] = -1
            reject(which+': '+label,lambda:profile_audit(packet,bad,which,old,pins))
        for label,transform in [('semantic term permutation',lambda ts:list(reversed(ts))),
                                ('semantic zero-pair insertion',lambda ts:ts+[[1,[7]],[-1,[7]]])]:
            good = deepcopy(packet)
            index = decl['new_rows'][0]['index']
            good['residuals'][index]['terms'] = transform(good['residuals'][index]['terms'])
            with TemporaryDirectory(prefix='round16-valid-polynomial-control-') as temporary:
                path = Path(temporary)/'actual.json'
                path.write_bytes(encoded(good))
                actual = load(path)
                need(poly(actual['residuals'][index]['terms'])==poly(packet['residuals'][index]['terms']), 'Valid entire polynomial control')
                positives.append(which+': '+label+'; canonical literal format remains separately enforced')
    bad = deepcopy(context)
    bad['power_calls'][0]['base'] = [[1,[5]]]
    reject('actual source-context base',lambda:context_audit(bad,source,cert))
    bad = deepcopy(witnesses)
    bad['private_175']['old_Nsq_restore'] = 'unchanged175'
    reject('false old-private identity',lambda:witness_metadata(bad))
    bad = deepcopy(witnesses)
    bad['remainder_records'][0]['interval_triples'] = 'fixed'
    reject('false fixed interval witnesses',lambda:witness_metadata(bad))
    with TemporaryDirectory(prefix='round16-index-control-') as temporary:
        folder = Path(temporary)
        (folder/'data').mkdir()
        for p in (HERE/'data').iterdir():
            (folder/'data'/p.name).write_bytes(p.read_bytes())
        p = folder/'data/INDEX.json'
        original = load(p)
        bad = deepcopy(original)
        bad['producer_sha256'] = '0'*64
        p.write_bytes(encoded(bad))
        reject('whole actual index producer',lambda:data_inventory(folder))
        p.write_bytes(encoded(original))
        p = folder/'data/METRICS.json'
        p.write_bytes(p.read_bytes()+b' ')
        reject('whole actual indexed bytes',lambda:data_inventory(folder))
    need(len(rejected)==43 and len(positives)==4, 'Every planned negative and valid semantic control')
    return {'negative_count':len(rejected),'negative_labels':rejected,'positive_count':len(positives),'positive_labels':positives}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    pins = authenticate()
    source,old,cert = [load(HERE/'inputs'/n) for n in ['source.json','guarded.json','transform_certificate.json']]
    original = source_binding(source,old,cert)
    data_inventory(HERE)
    context = load(HERE/'data/SOURCE_CONTEXT.json')
    source_context = context_audit(context,source,cert)
    maps = load(HERE/'data/ROW_MAPS.json')
    need(set(maps)=={'plain','weighted'}, 'Exactly two complete profile maps')
    packets,metrics,profiles = {},[],[]
    for which in ['plain','weighted']:
        packets[which] = load(HERE/f'data/{which}.json')
        census,record = profile_audit(packets[which],maps[which],which,old,pins)
        metrics.append(census)
        profiles.append(record)
    need(encoded(load(HERE/'data/METRICS.json'))==encoded(metrics), 'Every actual raw count and unconstrained-coordinate set')
    witnesses = load(HERE/'data/WITNESS_MAPS.json')
    witness_metadata(witnesses)
    calibration(load(HERE/'data/CALIBRATION_BINDING.json'))
    result = {'status':'PASS','optimized_python':bool(sys.flags.optimize),'checker_sha256':digest(Path(__file__).read_bytes()),
              'source_pins_sha256':digest((HERE/'SOURCE_PINS.json').read_bytes()),'actual_raw_census':metrics,
              'whole_input_binding':original,'source_context':source_context,'profiles':profiles,
              'actual_controls':controls(packets,maps,old,pins,context,source,cert,witnesses),
              'closed_ordinary_theorems':SEALS,'external_pins':len(pins['external_whole_files']),
              'no_producer_import_compiler_or_projection':True,'scope':SCOPE}
    raw = encoded(result)
    output = args.output.resolve()
    protected = {(HERE/n).resolve() for n in CORE|{'SOURCE_PINS.json','HOLD_INVENTORY.json','MANIFEST.json'}}
    folders = [(HERE/n).resolve() for n in ['data','inputs','provenance']]
    need(not args.output.is_symlink() and output not in protected and not any(p==output or p in output.parents for p in folders) and
         (not args.output.exists() or args.output.read_bytes()==raw), 'Fresh or identical separate receipt only')
    args.output.write_bytes(raw)
    print(raw.decode(),end='')


if __name__=='__main__':
    main()
