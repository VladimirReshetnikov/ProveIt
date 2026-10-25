#!/usr/bin/env python3
"""CODE ONLY / HOLD: two literal quadratic sources; no compiler or projection."""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REM = [(183,184,164,165,412), (191,192,169,170,413), (197,198,172,173,414),
       (202,203,175,176,415), (207,208,178,179,416), (213,214,182,183,417),
       (219,220,185,186,418), (225,226,189,190,419), (231,232,192,193,420),
       (236,237,196,197,421), (242,243,199,200,422)]
DROP = {398, *range(401,410)}
REQUEST_ROWS = [217,228,233,244,250,258,266,274,282,290,298,306,314,322,330,338,346,354]
SCOPE = 'Literal quadratic source only; ordinary Hstar/remainder/strict-product contracts retained; no projection, quartic or frontier claim.'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(x):
    return (json.dumps(x, indent=2, sort_keys=True) + '\n').encode()


def load(p):
    return json.loads(p.read_bytes())


def digest(b):
    return sha256(b).hexdigest()


def authenticate():
    pins = load(HERE/'SOURCE_PINS.json')
    for group, folder in [('core',HERE),('external_whole_files',ROOT)]:
        for name, record in pins[group].items():
            path = folder/name
            raw = path.read_bytes()
            need(not path.is_symlink() and digest(raw)==record['sha256'] and len(raw)==record['bytes'], 'Whole reviewed file '+name)
    for name, seal in pins['required_seals'].items():
        folder = ROOT/name
        manifest = folder/'MANIFEST.json'
        need(digest(manifest.read_bytes())==seal, 'Exact ordinary seal '+name)
        entries = load(manifest)['files']
        need({p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file() and p!=manifest}==set(entries), 'Whole ordinary inventory')
        for name, record in entries.items():
            raw = (folder/name).read_bytes()
            need(digest(raw)==(record if isinstance(record,str) else record['sha256']), 'Ordinary member '+name)
            need(isinstance(record,str) or len(raw)==record['bytes'], 'Ordinary member length')
    copies = load(HERE/'COPIED_INPUTS.json')['files']
    actual = {p.relative_to(HERE).as_posix() for name in ['inputs','provenance'] for p in (HERE/name).rglob('*') if p.is_file() or p.is_symlink()}
    need(actual==set(copies), 'Complete copied-input set')
    for name, record in copies.items():
        path = HERE/name
        raw = path.read_bytes()
        need(not path.is_symlink() and raw==(ROOT/record['source']).read_bytes() and digest(raw)==record['sha256'] and len(raw)==record['bytes'], 'Whole exact copy '+name)
    return pins


def collected(terms):
    result = {}
    for c, m in terms:
        key = tuple(sorted(m))
        result[key] = result.get(key,0)+c
    return [[c,list(m)] for m,c in sorted(result.items()) if c]


def remap(terms, mapping):
    return collected([[c,[mapping[v] for v in m]] for c,m in terms])


def profile(which, source, old, cert, pins):
    removed = sorted(a for g in cert['guards'] if g['row'] in DROP for a in g['auxiliary'])
    retained = [i for i in range(len(old['variables'])) if i not in removed]
    mapping = {i:j for j,i in enumerate(retained)}
    variables = [deepcopy(old['variables'][i]) for i in retained]
    variables[mapping[175]]['name'] = 'radix.Hstar.reused_private_175'
    for r,_,_,_,_ in REM:
        variables[mapping[r]]['name'] += '.residue_one_quotient'
    changed = {158:[[1,[175]],[-2,[]]]+[[-1,[v,v]] for v in range(16,25)],
               382:[[1,[522]],[-1,[5,175]]]}
    for r,_,d,b,_ in REM:
        for row in [d,b]:
            ts = []
            for c,m in old['residuals'][row]['terms']:
                if r in m:
                    need(m==[r], 'Only a raw linear remainder is substituted')
                    ts += [[c,[]],[c,[179,r]]]
                else:
                    ts.append([c,m])
            changed[row] = collected(ts)
    rows, entries = [], []
    for i, row in enumerate(old['residuals']):
        action = 'deleted_scalar_guard' if i in DROP else 'replaced_body' if i in changed else 'retained'
        new = None
        if i not in DROP:
            new = deepcopy(row)
            new['terms'] = remap(changed.get(i,row['terms']),mapping)
            rows.append(new)
        entries.append({'old_index':i,'old_row':row,'action':action,'new_index':None if new is None else len(rows)-1,'new_row':new})
    if which=='plain':
        factors = [[[1,[]],[1,[mapping[v]]]] for v in range(16,24)]
    else:
        factors = [[[1,[mapping[143]]],[-1,[mapping[20]]],[-1,[]]],
                   [[1,[mapping[140]]],[-1,[mapping[21]]],[-1,[]]]]
        factors += [[[1,[]],[1,[mapping[v]]]] for v in [18,19,22,23]]
    added = []
    left = factors[0]
    for j,right in enumerate(factors[1:],2):
        out = len(variables)
        variables.append({'kind':'gate','name':f'strict8.{which}.partial.{j}'})
        ts = [[1,[out]]]+[[-a*b,ma+mb] for a,ma in left for b,mb in right]
        row = {'label':f'strict8.{which}.partial.{j}','terms':collected(ts)}
        added.append({'index':len(rows),'row':row,'output':out})
        rows.append(row)
        left = [[1,[out]]]
    root = left[0][1][0]
    aux = list(range(len(variables),len(variables)+3))
    variables += [{'kind':'integer_guard','name':f'guard.fused_x_strict8.{which}.{letter}'} for letter in ['a','b','c']]
    ts = [[1,[root]],[1,[mapping[1],root]],[-1,[]],[-1,[aux[0],aux[0]]],[-1,[aux[1],aux[1]]],[-1,[aux[2]]],[-1,[aux[2],aux[2]]]]
    row = {'label':f'guard.fused_x_strict8.{which}','terms':collected(ts)}
    added.append({'index':len(rows),'row':row,'auxiliary':aux})
    rows.append(row)
    packet = deepcopy(old)
    packet.update(variables=variables,residuals=rows,variant=old['variant']+':Hstar_reused175:residue_one:'+which,
                  literal_policy={'profile':which,'parent_sha256':digest((HERE/'inputs/guarded.json').read_bytes()),
                                  'source_sha256':digest((HERE/'inputs/source.json').read_bytes()),
                                  'ordinary_seals':pins['required_seals'],'scope':SCOPE})
    maps = {'old_to_new':[mapping.get(i) for i in range(len(old['variables']))],
            'new_to_old':retained+[None]*(len(variables)-len(retained)), 'removed_coordinates':removed,
            'variables':[{'old_index':i,'old_metadata':old['variables'][i],'new_index':mapping.get(i),
                          'new_metadata':None if i not in mapping else variables[mapping[i]]} for i in range(len(old['variables']))],
            'rows':entries,'new_rows':added,'new_product_root':root,'new_guard_auxiliary':aux}
    return packet,maps


def construct():
    pins = authenticate()
    source,old,cert = [load(HERE/'inputs'/n) for n in ['source.json','guarded.json','transform_certificate.json']]
    artifacts, maps, census = {},{},[]
    for name in ['plain','weighted']:
        packet,maps[name] = profile(name,source,old,cert,pins)
        artifacts[f'data/{name}.json'] = encoded(packet)
        used = {v for r in packet['residuals'] for _,m in r['terms'] for v in m}
        census.append({'profile':name,'variables':len(packet['variables']),'rows':len(packet['residuals']),
                       'max_row_degree':max(len(m) for r in packet['residuals'] for _,m in r['terms']),
                       'raw_unconstrained_coordinates':[i for i in range(len(packet['variables'])) if i not in used],
                       'scope':'Literal raw source only; no all-variable-liveness or projected/frontier claim.'})
    artifacts['data/ROW_MAPS.json'] = encoded(maps)
    context = {'namespace':'Original source131 indices; ROW_MAPS supplies every active profile index. Certificate tokens/stale addresses are provenance only.',
               'old_source_sha256':digest((HERE/'inputs/source.json').read_bytes()),
               'old_guarded_sha256':digest((HERE/'inputs/guarded.json').read_bytes()),
               'actual_frame_row':381,'stale_certificate_frame_address':cert['square_budget']['frame_row'],
               'power_calls':cert['square_budget']['power_calls'],'frame_atoms':cert['square_budget']['atoms'],
               'seed_data':cert['seed_data'],'guards':cert['guards'],'cap_variables':cert['cap_variables'],
               'primary_norm_rows':[{'index':i,'row':r} for i,r in enumerate(source['residuals']) if r['label'].endswith('.norm1')],
               'shared_T_rows':[{'index':i,'row':r} for i,r in enumerate(source['residuals']) if r['label'].endswith('.T_definition')],
               'request_rows':[{'call':j,'index':i,'row':source['residuals'][i]} for j,i in enumerate(REQUEST_ROWS)],
               'derived_t_recurrence_rows':[{'index':i,'row':source['residuals'][i]} for i in range(259,267)],
               'early_rows':[{'index':i,'row':source['residuals'][i]} for i in [1,2,3,11,12,201,202,203,383,384]],
               'cap_rows':[{'index':i,'row':source['residuals'][i]} for i in range(385,398)]}
    artifacts['data/SOURCE_CONTEXT.json'] = encoded(context)
    witness = {'removed_scalar_guards':sorted(DROP),'removed_private_coordinates':maps['plain']['removed_coordinates'],
               'remainder_records':[{'raw_remainder':r,'new_quotient_same_slot':r,'slack':s,'digit_row':d,'bound_row':b,'interval_guard':g,
                                    'raw_from_new':'r=1+q*u','new_from_complete_Hstar_raw':'u=(r-1)/q',
                                    'interval_triples':'Fresh in both directions; represented integers change from r*s to u*s.'} for r,s,d,b,g in REM],
               'private_175':{'new_value':'2+sum(v16^2,...,v24^2)','old_Nsq_restore':'v26^2',
                              'fresh_Hstar_view':'Copy reused175 to a fresh Hstar coordinate; restore old private175=N^2.'},
               'strict_products':{'plain':'P8','weighted':'F^2*P8','fresh_extensions':'Unique unrestricted partial products, fresh Legendre triples.'},
               'source_boundary':'Pointwise common Hstar/repaired kernel, not old H0 tuples. Decode/refutation and fresh canonical construction transfer the H0 architecture.',
               'scalar_restore':'After signed-request residue recovery, weighted/plain fused strict support restores x and all CRT scalar signs; choose fresh old scalar triples.',
               'unaffected_witnesses':'Fixed through coordinate compaction; eleven interval witnesses and removed scalar witnesses are explicitly excluded.'}
    artifacts['data/WITNESS_MAPS.json'] = encoded(witness)
    artifacts['data/CALIBRATION_BINDING.json'] = encoded({'ordinary_seals':pins['required_seals'],
        'source131_proof_sha256':digest((HERE/'provenance/direct-proof.md').read_bytes()),
        'architecture_proof_sha256':digest((HERE/'provenance/architecture-proof.md').read_bytes()),
        'scope':'Exact retained source131/Round15/C222/ZF-to-ZFC ordinary contract; no incoming compiler/native runtime replay, old327 body identity or old324 polynomial identity.',
        'future_projection':'Separate proof, code reviews and release required; no factoring, elimination, translation or quartic here.'})
    artifacts['data/METRICS.json'] = encoded(census)
    artifacts['data/INDEX.json'] = encoded({'schema':'round16_two_literal_quadratic_sources_v1',
        'producer_sha256':digest(Path(__file__).read_bytes()),'source_pins_sha256':digest((HERE/'SOURCE_PINS.json').read_bytes()),
        'files':{n:{'sha256':digest(b),'bytes':len(b)} for n,b in sorted(artifacts.items())}})
    return artifacts,census


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    artifacts,census = construct()
    output = args.output.resolve()
    protected = {(HERE/n).resolve() for n in set(load(HERE/'SOURCE_PINS.json')['core'])|{'SOURCE_PINS.json','HOLD_INVENTORY.json','MANIFEST.json'}}
    folders = [(HERE/n).resolve() for n in ['data','inputs','provenance']]
    need(not args.output.is_symlink() and output not in protected and not any(p==output or p in output.parents for p in folders), 'Separate unprotected receipt')
    need(not (HERE/'data').is_symlink(), 'No data directory symlink')
    actual = {p.relative_to(HERE).as_posix() for p in (HERE/'data').rglob('*') if p.is_file() or p.is_symlink()}
    need(actual==set(artifacts) if args.check else actual<=set(artifacts), 'Exact generated file set')
    for n,b in artifacts.items():
        p = HERE/n
        need(not p.is_symlink(), 'No data symlink')
        if args.check or p.exists():
            need(p.is_file() and p.read_bytes()==b, 'Whole deterministic data '+n)
    report = {'status':'PASS','optimized_python':bool(sys.flags.optimize),'mode':'pure rebuild' if args.check else 'literal source materialization',
              'files':{n:{'sha256':digest(b),'bytes':len(b)} for n,b in sorted(artifacts.items())},'actual_raw_census':census,'no_projection_or_compiler':True}
    raw = encoded(report)
    need(not args.output.exists() or args.output.read_bytes()==raw, 'Reject different existing receipt')
    if not args.check:
        for n,b in artifacts.items():
            p = HERE/n
            if not p.exists():
                p.parent.mkdir(parents=True,exist_ok=True)
                p.write_bytes(b)
    args.output.write_bytes(raw)
    print(raw.decode(),end='')


if __name__=='__main__':
    main()
