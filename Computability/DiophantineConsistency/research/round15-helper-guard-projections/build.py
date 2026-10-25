#!/usr/bin/env python3
"""Guard-filter adapter; full compiler branch is under review, not yet released."""
import argparse, contextlib, copy, hashlib, io, json, sys, tempfile
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'con-zfc-diophantine-forms/125-unified-binomial-round15/direct/unified_reparam_derived_shell'
VARIANTS={'joint_helper':[2,25,27,30]}
sys.dont_write_bytecode=True

def need(ok,msg):
    if not ok:raise ValueError(msg)
def canon(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(b):return hashlib.sha256(b).hexdigest()
def sha(x):return digest(canon(x))
def get(p):return json.loads(p.read_bytes())
def put(p,x):
    p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(canon(x))
def inventory(p):return {str(q.relative_to(p)):digest(q.read_bytes()) for q in sorted(p.rglob('*')) if q.is_file() and q.name!='INDEX.json'}
def authenticate():
    pins=get(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'source pin '+n)
    for n,h in pins['vendor'].items():need(digest((HERE/'vendor'/n).read_bytes())==h,'vendor pin '+n)
    for n,h in pins['core'].items():need(digest((HERE/n).read_bytes())==h,'core pin '+n)
    return digest((HERE/'SOURCE_PINS.json').read_bytes())
def remap_terms(ts,mapping):return [[c,[mapping[i] for i in mon]] for c,mon in ts]

def source_variant(variant):
    source=get(PARENT/'source.json');old=get(PARENT/'guarded.json');cert=get(PARENT/'transform_certificate.json')
    omit=VARIANTS[variant];removed_vars={a for j in omit for a in cert['guards'][j]['auxiliary']}
    removed_rows={cert['guards'][j]['row'] for j in omit}
    kept_vars=[i for i in range(len(old['variables'])) if i not in removed_vars]
    kept_rows=[i for i in range(len(old['residuals'])) if i not in removed_rows]
    vm={v:i for i,v in enumerate(kept_vars)};rm={r:i for i,r in enumerate(kept_rows)}
    result=copy.deepcopy(old);result['variables']=[old['variables'][i] for i in kept_vars]
    result['residuals']=[dict(old['residuals'][r],terms=remap_terms(old['residuals'][r]['terms'],vm)) for r in kept_rows]
    graphs=[]
    for j,g in enumerate(cert['guards']):
        if j in omit:continue
        ng=copy.deepcopy(g);ng['expression']=remap_terms(g['expression'],vm)
        ng['auxiliary']=[vm[a] for a in g['auxiliary']];ng['row']=rm[g['row']]
        graphs.append({'original_guard':j,'old':g,'new':ng})
    a=len(result['variables']);b=a+1;d=a+2
    new_guard={'kind':'helper_comparison_lower_bound','expression':[[-4,[]],[1,[255]]],
        'auxiliary':[a,b,d],'row':len(result['residuals'])}
    result['variables'] += [{'name':'helper_bound.'+x,'kind':'integer_guard'} for x in ['a','b','c']]
    result['residuals'].append({'label':'domain_guard.helper_lower_bound',
        'terms':[[-4,[]],[1,[255]],[-1,[a,a]],[-1,[b,b]],[-1,[d]],[-1,[d,d]]]})
    helper=get(ROOT/'research/round15-helper-reflection/CERTIFICATE.json')
    mapping={'schema':'round15_helper_guard_filter_v1','variant':variant,'input_sha256':sha(old),'body_sha256':sha(source),
        'output_sha256':sha(result),'omitted_guards':[{'original_guard':j,'guard':cert['guards'][j]} for j in omit],
        'removed_variables':sorted(removed_vars),'removed_rows':sorted(removed_rows),
        'retained_variables':[[v,vm[v]] for v in kept_vars],'retained_rows':[[r,rm[r]] for r in kept_rows],
        'body_coordinates':list(range(len(source['variables']))),'body_rows':list(range(len(source['residuals']))),
        'retained_guards':graphs,'new_guard':new_guard,
        'helper_reflection':helper['reflection'],'fixed_body_coordinates':helper['fixed_body_coordinates'],
        'witness_schedule':['restore_projected_Horn_and_slack_body','normalize_helper','restore_old_d_and_V_triples','apply_joint_F_A_theorem','restore_old_F_A_triples'],
        'witness_map':'Retained triples are renamed; normalize the five private helper ports and restore old d/V graphs FIRST, then apply the joint F/A theorem with fresh omitted triples.'}
    oldprune=get(PARENT/'pruning_certificate.json');drop=[]
    for s in oldprune['dropped_private_slacks']:
        drop.append({'row':rm[s['row']],'variable':vm[s['variable']],'restoration':remap_terms(s['restoration'],vm)})
    pruned=copy.deepcopy(result);deleted={s['row'] for s in drop}
    pruned['residuals']=[r for i,r in enumerate(pruned['residuals']) if i not in deleted]
    pruning={'input_sha256':sha(result),'output_sha256':sha(pruned),'dropped_private_slacks':drop}
    return result,mapping,pruned,pruning

def census(eq,poly):
    return {'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max((len(m) for c,m in poly['terms']),default=0),
        'monomials':len(poly['terms']),'height':max((abs(c) for c,m in poly['terms']),default=0),
        'row_height':max((abs(c) for r in eq['residuals'] for c,m in r['terms']),default=0)}

def compile_variant(target,guarded,mapping,pruned,pruning):
    # These exact reviewed imports are deliberately isolated from source mode.
    import terminal_elimination as E
    import factor_horn as F
    import translate_coordinates as T
    import center_integer as C
    factored,fc=F.transform(pruned)
    projected,pc,engine_metrics=E.optimize(factored,max_support=16)
    receipt=E.verify(factored,projected,pc)
    for n,x in [('factored_source.json',factored),('factorization_certificate.json',fc),('projected.json',projected),
                ('terminal_elimination_certificate.json',pc),('ENGINE_VERIFICATION.json',receipt)]:put(target/n,x)
    shifts={i:-1 for i,v in enumerate(projected['variables']) if v['name'].startswith('crt.encoded') or v['name'] in ('t0','M0') or v['name'].endswith('minus1')}
    cert=get(PARENT/'transform_certificate.json')
    tconstant=next((c for c,m in cert['square_budget']['power_calls'][0]['exponent'] if not m),0)
    for i,v in enumerate(projected['variables']):
        if v['name']=='t0':shifts[i]=-tconstant
    plain=T.translate(projected,shifts);poly=E.expand(plain)
    tc={'schema':'integral_translation_v1','input_sha256':sha(projected),'output_sha256':sha(plain),
        'shifts':[[i,s] for i,s in shifts.items()],'convention':'old=new+shift'}
    for n,x in [('equation.json',plain),('expanded_polynomial.json',poly),('translation_certificate.json',tc),
                ('METRICS.json',census(plain,poly)),('projected.json',projected)]:put(target/'plain'/n,x)
    transcript=io.StringIO()
    with contextlib.redirect_stdout(transcript):C.center(target/'plain',target/'centered')
    put(target/'CENTER_SEARCH.json',{'transcript':transcript.getvalue(),
        'scope':'Exact accepted finite coordinate-descent policy; no global optimum claim.'})
    return {'engine':engine_metrics,'plain':census(plain,poly),'centered':get(target/'centered/METRICS.json')}

def materialize(destination,mode,pin_hash):
    need(not destination.exists() or not any(destination.iterdir()),'destination must be empty')
    destination.mkdir(parents=True,exist_ok=True);summary={}
    if mode=='full':sys.path.insert(0,str(HERE/'vendor'))
    for name in VARIANTS:
        guarded,mapping,pruned,pruning=source_variant(name);target=destination/name
        for n,x in [('guarded.json',guarded),('GUARD_MAP.json',mapping),('pruned_source.json',pruned),('pruning_certificate.json',pruning)]:put(target/n,x)
        summary[name]={'guarded_variables':len(guarded['variables']),'guarded_rows':len(guarded['residuals']),
            'guards':len(mapping['retained_guards'])+1,'pruned_private_slacks':len(pruning['dropped_private_slacks'])}
        if mode=='full':summary[name].update(compile_variant(target,guarded,mapping,pruned,pruning))
    index={'schema':'round15_helper_guard_projection_inventory_v1','mode':mode,'source_pins_sha256':pin_hash,
        'policy':{'max_support':16,'affine_support':None,'quadratic_first':False,'variants':VARIANTS,
                  'charts':['plain','centered'] if mode=='full' else []},'summary':summary,'files':inventory(destination)}
    put(destination/'INDEX.json',index);return index

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--mode',choices=['source','full'],default='full');ap.add_argument('--check',action='store_true')
    ap.add_argument('--destination',type=Path);ap.add_argument('--output',type=Path);a=ap.parse_args();pin_hash=authenticate()
    dest=a.destination or HERE/('full-data' if a.mode=='full' else 'data')
    if a.check:
        with tempfile.TemporaryDirectory(prefix='round15-helper-rebuild-') as td:
            scratch=Path(td)/'data';index=materialize(scratch,a.mode,pin_hash)
            expected={str(p.relative_to(scratch)):p.read_bytes() for p in scratch.rglob('*') if p.is_file()}
            actual={str(p.relative_to(dest)):p.read_bytes() for p in dest.rglob('*') if p.is_file()}
            need(actual==expected,'deterministic rebuild differs')
    else:index=materialize(dest,a.mode,pin_hash)
    receipt={'verified':True,'mode':a.mode,'pure_check':a.check,'files':len(index['files']),
        'index_sha256':sha(index),'summary':index['summary'],'source_pins_sha256':pin_hash}
    out=json.dumps(receipt,sort_keys=True,indent=2)+'\n'
    if a.output:
        need(not a.output.exists() or a.output.read_text()==out,'different existing output');a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(out)
    print(out,end='')
if __name__=='__main__':main()
