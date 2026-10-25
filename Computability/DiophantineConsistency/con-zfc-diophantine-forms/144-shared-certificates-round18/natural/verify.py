#!/usr/bin/env python3
"""Independent row-change, natural-restoration and complete-coefficient audit."""
from pathlib import Path
from copy import deepcopy
import argparse,hashlib,json,sys,tempfile,subprocess
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
def read(p):return json.loads(p.read_text())
def require(ok,msg):
    if not ok:raise ValueError(msg)
def digest(o):return hashlib.sha256(check.canonical(o)).hexdigest()

PINNED_INPUTS={
    'source/equation.json':'e3de14bec54b0a53727ac69e9cbdbbce3894281e5a1cc28f446ed9bcc09c947f',
    'source/semantic.json':'f9f740a89538b52be7599bc5916c8d895f0b50ba1fcc08c5c543adf05754f530',
    'code/check.py':'aa2b82c748de974bb749917706055b3e52f3b4135a0a7b8153be148821f75f24',
    'code/contract.py':'e6dd8486c5426a41ccda1463071799dddb988103457f04b44bfb6cfb581f018d',
    'code/affine_check.py':'8f257c83c8d4ff9f2b21f1da21b51b522fb2dad237957eef2488874dcd6e9ab9',
}

def authenticate_inputs():
    ledger=read(HERE/'SOURCE_LEDGER.json')
    recorded={'source/equation.json':ledger['parent_raw_equation_sha256'],
              'source/semantic.json':ledger['parent_semantic_sha256'],
              **ledger['reviewed_inherited_executables']}
    require(recorded==PINNED_INPUTS,'Inherited input ledger differs from reviewed pins')
    for name,expected in PINNED_INPUTS.items():
        require(hashlib.sha256((HERE/name).read_bytes()).hexdigest()==expected,'Inherited input byte binding failed: '+name)
    return {'verified':True,'hardcoded_and_ledger_bound_sha256':PINNED_INPUTS}

def validate_transform(parent,source,recipe):
    names={v['name']:i for i,v in enumerate(parent['variables'])}
    v=lambda s:names[s]
    small=['choose0','crt.range.index'];big=['crt.range.'+s for s in ['a','b','c','d','derived_label_sum']]
    four=recipe['strategy']=='four';absorbed=recipe['strategy']=='three_with_digit'
    groups=[('t0',small),('t',big)] if four else [('t',small+big)]
    groups += [('y',['crt.range.S','crt.range.Sp']),('x',['crt.range.u','crt.range.vq'])]
    den={'t0':v('pow3.output'),'t':v('mul.422'),'y':v('pow4.output'),'x':v('pow5.output')}
    rows={r['label']:r for r in parent['residuals']};variables=deepcopy(parent['variables']);removed=set();replace={}
    for label,req in groups:
        slack=v(req[0]+'.modular_rslack');variables[slack]['name']='pooled_digits.'+label+'.slack'
        terms=[[-1,[]],[1,[den[label]]],[-1,[slack]]]
        for s in req:
            old=rows[s+'.remainder_bound'];remainder=v(s+'.modular_remainder');private=v(s+'.modular_rslack')
            actual_den=den['t0'] if s in small else den[label]
            require(check.collect(old['terms'])==check.collect([[-1,[]],[1,[actual_den]],[-1,[remainder]],[-1,[private]]]),'Unexpected old bound')
            factors=[v('pow2.output'),remainder] if not four and s in small else [remainder]
            terms.append([-1,factors]);removed.add(s+'.remainder_bound')
        if absorbed and label=='t':terms.append([-1,[v('choose0.output'),den['t0']]])
        replace[req[0]+'.remainder_bound']={'label':'pooled_digits.'+label,'terms':check.collect(terms)}
    if absorbed:
        removed.add('choose0.digit_bound')
        require(check.collect(rows['choose0.digit_bound']['terms'])==check.collect([[-1,[]],[1,[v('pow2.output')]],[-1,[v('choose0.output')]],[-1,[v('choose0.modular_oslack')]]]),'Unexpected output bound')
    # The adjacent denominator is literally the retained product q*D0.
    expected=check.collect([[1,[den['t']]],[-1,[v('pow2.output'),den['t0']]]])
    require(any(check.collect(r['terms'])==expected for r in parent['residuals']),'D1=qD0 identity missing')
    newrows=[replace.get(r['label'],r) for r in parent['residuals'] if r['label'] not in removed or r['label'] in replace]
    used=sorted({i for r in newrows for c,m in r['terms'] for i in m});rename={v:i for i,v in enumerate(used)}
    expectedrows=[{'label':r['label'],'terms':[[c,[rename[i] for i in m]] for c,m in r['terms']]} for r in newrows]
    order=recipe['row_order'];require(sorted(order)==list(range(len(newrows))),'Bad row permutation')
    require(source['residuals']==[expectedrows[i] for i in order],'Changed raw system')
    require(source['variables']==[variables[i] for i in used],'Changed variable list')
    require(source['domain']==parent['domain']=='nonnegative integers','Domain altered')
    return {'old_rows':len(parent['residuals']),'new_rows':len(newrows),'old_variables':len(parent['variables']),'new_variables':len(used),'pooled_groups':len(groups),'exact_digit_bound_absorbed':absorbed,'all_unchanged_rows_compared':True}

def rejected(fn,label):
    try:fn()
    except (ValueError,KeyError,IndexError,TypeError):return label
    raise ValueError('Accepted corruption: '+label)

def verify(rebuild=False):
    authentication=authenticate_inputs()
    global check, affine_check
    import check
    import affine_check
    parent=read(HERE/'source/equation.json');metadata=read(HERE/'source/semantic.json')
    affine,cert=affine_check.verify(metadata,parent)
    affine['negative_controls_rejected']=affine_check.negative_controls(metadata,parent,cert)
    results=[];catalog=read(HERE/'ENDPOINTS.json')
    for recipe in read(HERE/'PROFILE_RECIPES.json'):
        folder=HERE/'endpoints'/recipe['name'];source=read(folder/'source/equation.json');target=read(folder/'natural/equation.json');elimination=read(folder/'natural/elimination_certificate.json');poly=read(folder/'natural/expanded_polynomial.json')
        transformed=validate_transform(parent,source,recipe)
        result,expanded=check.verify(source,target,elimination)
        require(poly['terms']==expanded and poly['variables']==result['variables'] and poly['domain']=='nonnegative integers','Wrong polynomial')
        require(result==next(x['metrics'] for x in catalog if x['name']==recipe['name']),'Catalog metrics mismatch')
        affine_check.validate_quadratic_equation(target,'target')
        changed=deepcopy(source);i=next(i for i,r in enumerate(changed['residuals']) if r['label'].startswith('pooled_digits.'));changed['residuals'][i]['terms'][0][0]+=1
        controls=[rejected(lambda:validate_transform(parent,changed,recipe),'altered_pool_coefficient')]
        badorder=deepcopy(recipe);badorder['row_order'][0]=badorder['row_order'][1]
        controls.append(rejected(lambda:validate_transform(parent,source,badorder),'nonpermutation'))
        badcert=deepcopy(elimination);badcert['steps'][0]['restoration'][0][0]+=1
        controls.append(rejected(lambda:check.verify(source,target,badcert),'altered_restoration'))
        wrong=deepcopy(poly);wrong['terms'][0][0]+=1
        controls.append(rejected(lambda:require(wrong['terms']==expanded,'wrong expansion'),'altered_collected_coefficient'))
        results.append({'name':recipe['name'],'transformation':transformed,'metrics':result,'negative_controls_rejected':controls})
    reconstruction=[]
    if rebuild:
        with tempfile.TemporaryDirectory() as temp:
            out=Path(temp)/'rebuilt';command=[sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])+[str(HERE/'reproduce.py'),'--output',str(out)]
            process=subprocess.run(command,capture_output=True,text=True,check=True)
            for recipe in read(HERE/'PROFILE_RECIPES.json'):
                for n in ['source/equation.json','source/transformation.json','natural/equation.json','natural/elimination_certificate.json','natural/expanded_polynomial.json']:
                    require((out/recipe['name']/n).read_bytes()==(HERE/'endpoints'/recipe['name']/n).read_bytes(),'Nonreproducible bytes '+recipe['name']+'/'+n)
                    reconstruction.append(recipe['name']+'/'+n)
    return {'verified':True,'optimized':bool(sys.flags.optimize),'authenticated_inputs':authentication,'parent_affine_export':affine,'endpoints':results,'byte_identical_reconstructed_files':reconstruction}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--rebuild',action='store_true');p.add_argument('--output',type=Path);a=p.parse_args();r=verify(a.rebuild)
    if a.output:a.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))
