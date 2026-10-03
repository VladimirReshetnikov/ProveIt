#!/usr/bin/env python3
"""Pinned, portable bounded independent membrane checks; no archive mutation.
Usage: python review_membrane_reports_2a8a.py UNIVERSAL_ROOT MOTIF_ROOT [--authors] [--output FILE]
The roots are extracted release directories, not ZIP paths. Author replay uses private copies.
"""
import argparse, copy, hashlib, importlib.util, itertools, json, os, random
import shutil, subprocess, sys, tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
sys.dont_write_bytecode = True
if not __debug__:
    raise RuntimeError('This research checker requires Python assertions; omit -O')
PINS = {'universal': {'MANIFEST.json': '5d888ed88f2e6d322ab89c4f8c379d73c6dfd0f2db79d202c4add6224956a8d8', 'README.md': '2bfeb22e5223de05760e372fe93de2c87e3f009909b4c8fbb634ecd95cd0dbfb', 'article/membrane_frontend.tex': 'e726bd6e77cf9f9e2a03d4d42069ad7179c3298b7587b6c928cfa5e31a828dba', 'direct/MANIFEST.json': 'f627280060c9cf35bd0fdb2490b7f211b2a199c20da744e6930b9fb9ab5d4180', 'direct/PROOF.md': '1535607bebd0b2b19d004ad068e21a11e82d1d8014d406365911d52abdabdeac', 'direct/README.md': 'c716cbe17c77713251031baadbcb65b8b85051e129a59aa0c4bdda354fb175ba', 'direct/build_direct.py': '457a67e2b6e61b91dabba45a6709d9ece9351165b49587ac505808ca5cb295f5', 'direct/build_quadratic.py': 'db1242f104bd1dd134dcb804a850adf666f0ca048295782eb93f83417efa4876', 'direct/load_input.py': '2f1e5f49f6f949e19056fc96d8ca7c44b54c683909a49b12ea098600a8e83fff', 'direct/make_accepting_witness.py': '124c13f3a715ed68198f97e7859c4c35544c13868cdf60c1812a1b683475ff35', 'direct/quadratic_core.py': 'a14ab87fea4ec8c2d9441dc35768a2972cb52b7627e59423a99844c49e706124', 'direct/source/WATERFALL-FRONTEND-PROOF.md': 'f04ff59532792396513f0141c2782958516477e9ac0f33e0678c2d794f6c7da7', 'direct/verify_accepting_quadratic.py': '6410a038486fd8c30037282ea04db1a13402536d8151566535cdd6f7f7a7e96d', 'direct/verify_direct.py': '59ab01c44ad3a237776642cca4359a808e367b959e52954731c9e4a02f3cd5de', 'direct/verify_membrane.py': '4fe115c22b2916b17f2d95a0ee0744a685ddcedc4da0c991bed1b02085a02dd1', 'direct/virtual3.json': '24c771db50dc621068e470227802c2710a4531ce2e7ad3703a5cdb6b0543bbcf', 'packet/MANIFEST.json': '3d54dc2f9a9426ee1502b108677dc735da2a44089fa7770f70507581e19c2325', 'packet/PROOF.md': 'be43b604667570aad004d78324f312d61b6b2c38c33be14844814b283608af6e', 'packet/README.md': '1b1527cfbccb50ad71bb1bba6cd8a66fb0ce9af8e6de38f2667cfcf3a1a6bb23', 'packet/build_frontend.py': 'b5e46ed6b5b6e1daab5a71f169d28b4892bca419f957943365e4916950d5c1bb', 'packet/literal2.json': '85e16b44828f2f3d4ad6d0805dcc9e9922893a6d286874f2018d6a33af864b00', 'packet/load_input.py': 'bde5fab60276744777bd4f975735f2bea0828563064e963c07df3f8fc23f5690', 'packet/quadratic_outcome.py': '648033cbc595b0e77ca56a5e09b1dc171056153fb0de77e9f83ad74b902c4d86', 'packet/replay_example.py': '02aff748c2bea8d0438bbdba0a12c07c3b8d2900a27f46998bebdbb25e9357c3', 'packet/source/WATERFALL-FRONTEND-PROOF.md': 'f04ff59532792396513f0141c2782958516477e9ac0f33e0678c2d794f6c7da7', 'packet/verify_density.py': '9a98b4a0d1fb989ccfed6240e9673a74cace3a120c0c4afc82cd280a1e753cbc', 'packet/verify_frontend.py': 'eccbd28b106d808bd5b6cc300ec68887c85b382599e2f22d8131abb9c704ae60', 'packet/verify_membrane.py': '9804ca38f2bed97230e098006fc3a19ee5caa533b58050392c62bd271498c58f', 'packet/verify_quadratic.py': '2f190de7bdcb466c434f4d1be50f875d226267c941432bb6bb4ac70dc9f37dd2', 'packet/virtual3.json': '24c771db50dc621068e470227802c2710a4531ce2e7ad3703a5cdb6b0543bbcf', 'reproduce.py': '510fcb892c9a21730626e2cd04294feb50d7a558c362b5b899c41beaaf838643'}, 'motif': {'MANIFEST.json': 'a322c91a128325553aead8b927c3db89b8d4de17b4db63c90cf20df64dc71987', 'README.md': '0988e2b387059f5d07204473191c208dc52266c7138c3e884d1610f6238e0b79', 'RELEASE_NOTES.md': '5df43ef8bd96d6753d25919388837eea6c6419c0b1c136562a836be8967f6117', 'article/membrane_motifs.tex': '3d8f41cc0fa443a02ab5cdada43f21abdd90b4b0e50cc41f3d2f4892224f0844', 'replay/contextual_copy_polynomials.json': 'b9186d5830f973858616e9126f5c941bb6a1f216f80a4f4cad9d931dc7f800e0', 'replay/contextual_copy_quartic.json': '386f3273c01ca2f7bf9a43df8c961f53f7773bf494214b3a8b681d43c098ed7f', 'replay/examples.json': '7e7e73e8594af5aef198c6df4943e2b741b2442b47536fc89b13fea3d7b266f9', 'replay/export_sos.py': 'cb749d41dedfcb211ae3f704a0b200a6a88bcab0e9081f345946efaef7e3131d', 'replay/focused_tests.py': '91fac87d62224e07a7dc08e481a13012a5508af054ff6a8f318cdee4712645e5', 'replay/motif_compiler.py': '90e7b7e18bc6e24918dbb26c6c21d6f18c23e5b9adb5756557aec7d25d3354e2', 'replay/regression_extensions.py': 'd035b6f91ac2c29b5404a47f8802b544d5559d5eddc164e99ab43877fb5f39a6', 'replay/replay_tests.py': 'c725c6432b89da61f2a1e2b4420a9ffb42fdb7a8f77fee2eb6ea2334f194794b', 'replay/run_all.py': 'df980619aa5bf03934c551dbe42587b6f5d5daeacaf7dfcded9ace07b59adc9f', 'replay/verify_saved_examples.py': 'b9610921ff953de9ffa51d9c5aa65ce68f77b30711b653a9198d7fcd318360d0'}}


def digest(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);sys.modules[name]=mod;spec.loader.exec_module(mod)
    return mod

def affine_value(row,packet,w,params):
    value=row['constant']
    value+=sum(c*sum(k*w.get(i,0) for i,k in packet['linear_forms'][f]) for f,c in row['forms'])
    value+=sum(c*w.get(i,0) for i,c in row['variables'])
    value+=sum(c*params[p] for p,c in row['parameters'])
    return value

def emitted_value(packet,w,params):
    return sum(affine_value(z['affine'],packet,w,params)**2 for z in packet['affine_squares'])+sum(affine_value(z['left'],packet,w,params)*affine_value(z['right'],packet,w,params) for z in packet['quadratic_products'])

def counter_manual(table,T,w,initial,target):
    B=len(table['branches']);d=table['register_count'];nb=d*B-table['sub_count'];stride=B+nb
    value=0;last=table['entry'];previous=list(initial)
    for t in range(T):
        ee=[w.get(t*stride+r,0) for r in range(B)];E=sum(ee);old=[0]*d;new=[0]*d;q=n=0;base=t*stride+B
        for r,z in enumerate(table['branches']):
            s=0
            for i in range(d):
                x=0
                if not(z['guard']=='zero' and z['register']==i):x=w.get(base,0);base+=1
                old[i]+=x+ee[r]*int(z['guard']=='positive' and z['register']==i)
                new[i]+=x+ee[r]*int(z['guard'] is None and z['register']==i);s+=x
            q+=ee[r]*z['source'];n+=ee[r]*z['target'];value+=(E-ee[r])*(ee[r]+s)
        value+=(E-1)**2+(q-last)**2+sum((x-y)**2 for x,y in zip(old,previous))
        last=n;previous=new
    return value+(last-target)**2

def quadratic_checks(root):
    counts=Counter();modules=[load(root/'direct/quadratic_core.py','membrane_qdirect'),load(root/'packet/quadratic_outcome.py','membrane_qprime')]
    toy={'registers':['X'],'entry':'s','rows':{'s':['SUB',0,'s','HALT']}}
    for mod in modules:
        tab=mod.semantic_table(toy)
        # Every natural tuple in [0,2]^(3T), not merely canonical witnesses or coordinate mutations.
        for T in (0,1,2,3):
            packet=mod.compile_schema(tab,T,initial=['n']);found={n:[] for n in range(3)}
            for values in itertools.product(range(3),repeat=3*T):
                w=dict(enumerate(values))
                for n in range(3):
                    actual=emitted_value(packet,w,{'n':n})
                    assert actual==counter_manual(tab,T,w,[n],tab['halt'])>=0
                    if actual==0:found[n].append(values)
                    counts['exhaustive_natural_tuples']+=1
            for n in range(3):
                assert len(found[n])==int(T==n+1)
                if found[n]:
                    canonical,*_=mod.witness_for_trace(tab,T,[n])
                    assert found[n][0]==tuple(canonical.get(i,0) for i in range(3*T))
                counts['empty_or_singleton_fibers']+=1
        packet=mod.compile_schema(tab,1,initial=['n'])
        for values in itertools.product([Fraction(i,2) for i in range(5)],repeat=3):
            for n in range(3):
                result=emitted_value(packet,dict(enumerate(values)),{'n':n})
                assert result>=0 and (result!=0 or (n==0 and values==(0,1,0)))
                counts['nonnegative_rational_tuples']+=1
        for bad in ({-1:0},{3:1},{0:True},{0:0.5},{0:-1}):
            try:mod.evaluate(packet,bad,{'n':0})
            except ValueError:counts['domain_rejections']+=1
            else:raise AssertionError('bad natural witness accepted')
        for bad in (True,0.5,-1):
            try:mod.compile_schema(tab,bad)
            except ValueError:counts['domain_rejections']+=1
            else:raise AssertionError('bad horizon accepted')
    rng=random.Random(1984)
    for relative,filename,mod in [('direct','virtual3.json',modules[0]),('packet','literal2.json',modules[1])]:
        program=json.loads((root/relative/filename).read_text());table=mod.semantic_table(program)
        d=len(program['registers']);I=sum(z[0]=='ADD' for z in program['rows'].values());S=len(program['rows'])-I;B=I+2*S
        for T in (0,1,2):
            initial=list(range(d));packet=mod.compile_schema(table,T,initial=initial)
            assert packet['ledger']=={'natural_witnesses':((d+1)*B-S)*T,'affine_squares':(d+2)*T+1,'quadratic_products':B*T,'degree_at_most':2}
            for terms in packet['linear_forms'].values():assert all(type(i)is int and type(c)is int for i,c in terms)
            for signed in (False,True):
                w={i:rng.randrange(-2 if signed else 0,4) for i in range(packet['variables']['count'])}
                expected=counter_manual(table,T,w,initial,table['halt'])
                assert emitted_value(packet,w,{})==expected
                if not signed:assert mod.evaluate(packet,w,{})==expected>=0
                counts['full_actual_source_offzero_identities']+=1
            counts['full_actual_source_ledgers']+=1
    return dict(counts)

def motif_manual(packet,w):
    sc=packet['schema'];cs=sc['configs'];ts=sc['transitions'];rules=packet['rules'];d=packet['alphabet_size'];K=len(cs)
    X=lambda i,a:w[f'x:{i}:{a}'];C=lambda i,k:1+w[f'c:{i}:{k}'] if k in cs[i]['children'] else 0
    M=lambda j,k:1+w[f'm:{j}:{k}'];F=lambda j,i:w[f'f:{j}:{i}'];O=lambda j,a:w[f'o:{j}:{a}'];out={}
    for j,t in enumerate(ts):
        s=t['source'];label=cs[s]['label'];r=rules[t['mode']] if t['mode']>=0 else None
        branches=t['targets'];zeros=set()
        for z in rules:
            allowed=z['label']==label and not(z['kind']=='divide' and z['elementary'] and cs[s]['children'])
            if allowed and (z['kind']=='evolve' or (r is None and z['kind'] in ('out','divide','dissolve') and not(label=='skin' and z['kind'] in ('divide','dissolve')))):zeros.add(z['a'])
        for k in t['children']:
            if ts[k]['mode']<0:zeros.update(z['a'] for z in rules if z['label']==cs[ts[k]['source']]['label'] and z['kind']=='in')
        if zeros:out[f'maximal:{j}']=sum(w[f'u:{j}:{a}'] for a in zeros)
        for i in range(K):
            g=sum(M(j,k)*F(k,i) for k in t['children'])
            out[f'source:{j}:{i}']=C(s,i)-sum(M(j,k) for k in t['children'] if ts[k]['source']==i)
            out[f'forest:{j}:{i}']=F(j,i)-(g if r and r['kind']=='dissolve' else branches.count(i))
            for b,q in enumerate(branches):out[f'targetchild:{j}:{b}:{i}']=C(q,i)-g
        for a in range(d):
            ev=[(ri,z) for ri,z in enumerate(rules) if z['kind']=='evolve' and z['label']==label]
            demand=sum(M(j,k) for k in t['children'] if ts[k]['mode']>=0 and rules[ts[k]['mode']]['kind']=='in' and rules[ts[k]['mode']]['a']==a)
            local=int(bool(r and r['kind']!='in' and r['a']==a));u=w[f'u:{j}:{a}'];y=w[f'y:{j}:{a}']
            out[f'resource:{j}:{a}']=u+sum(w[f'e:{j}:{ri}'] for ri,z in ev if z['a']==a)+local+demand-X(s,a)
            out[f'updated:{j}:{a}']=y-u-sum(w[f'e:{j}:{ri}']*z['out'][a] for ri,z in ev)-(r['out'][a] if r and r['kind']=='in' else 0)-sum(M(j,k)*O(k,a) for k in t['children'])
            out[f'upward:{j}:{a}']=O(j,a)-(y+r['out'][a] if r and r['kind']=='dissolve' else r['out'][a] if r and r['kind']=='out' else 0)
            for b,q in enumerate(branches):out[f'targetobject:{j}:{b}:{a}']=X(q,a)-y-((r['out'] if b==0 else r['other'])[a] if r and r['kind']=='divide' else 0)
    return out

def motif_checks(root):
    mod=load(root/'replay/motif_compiler.py','membrane_motif_independent');stats=Counter();rng=random.Random(701)
    data=json.loads((root/'replay/examples.json').read_text());packets=[p for p in data.values() if isinstance(p,dict) and 'witness' in p]+list(data['same_mass_different_successor'].values())
    for packet in packets:
        rules=[mod.Rule(**r) for r in packet['rules']];eq,names=mod.compile_schema(packet['schema'],rules,packet['alphabet_size']);sc=packet['schema'];d=packet['alphabet_size'];K=len(sc['configs']);J=len(sc['transitions'])
        A=sum(len(c['children']) for c in sc['configs']);E=sum(len(t['children']) for t in sc['transitions']);B=sum(n.startswith('e:') for n in names);L=sum(len(t['targets']) for t in sc['transitions']);Z=sum(n.startswith('maximal:') for n,p in eq)
        assert len(names)==d*K+A+E+B+3*d*J+K*J and len(eq)==(3*d+2*K)*J+(d+K)*L+Z
        bound=max(2,max((max(r.out) for r in rules if r.kind=='evolve'),default=0),1+max((len(t['children']) for t in sc['transitions']),default=0))
        assert all(p.degree<=2 and all(type(c)is int and abs(c)<=bound for c in p.t.values()) for n,p in eq)
        assert set(names)==set(packet['witness']) and all(type(v)is int and v>=0 for v in packet['witness'].values())
        for iteration in range(13):
            w=packet['witness'] if iteration==0 else {n:rng.randrange(-3 if iteration%2 else 0,5) for n in names}
            actual={n:p.evaluate(w) for n,p in eq};expected=motif_manual(packet,w)
            assert actual==expected
            if iteration==0:assert not any(actual.values())
            stats['complete_residual_identities']+=1;stats['scalar_residuals_compared']+=len(eq)
        for name in names:
            if name.startswith(('u:','y:','o:','f:')):
                w=dict(packet['witness']);w[name]+=1;assert any(p.evaluate(w) for n,p in eq)
                stats['derived_coordinate_mutations_rejected']+=1
        stats['schema_ledgers_and_heights']+=1
    # Independent flat-tree old-object/slot oracle: all parent and two child payloads 0..2,
    # optional evolution at parent and children, all idle/in/out/dissolve/divide modes.
    for parent_evolution,child_evolution in itertools.product((False,True),repeat=2):
        rules=[mod.Rule(k,'h',0,(1,),(1,) if k=='divide' else ()) for k in ('in','out','dissolve','divide')]
        pe=len(rules)
        if parent_evolution:rules.append(mod.Rule('evolve','skin',0,(2,)))
        ce=len(rules)
        if child_evolution:rules.append(mod.Rule('evolve','h',0,(2,)))
        for P,a,b in itertools.product(range(3),repeat=3):
            for ep in range(P+1) if parent_evolution else (0,):
                for ea in range(a+1) if child_evolution else (0,):
                    for eb in range(b+1) if child_evolution else (0,):
                        for ma,mb in itertools.product(range(-1,4),repeat=2):
                            modes=(ma,mb);old=(a,b);ev=(ea,eb)
                            remp=P-ep-sum(x==0 for x in modes);rem=[x-e-int(m in (1,2,3)) for x,e,m in zip(old,ev,modes)]
                            legal=min(remp,*rem)>=0
                            if legal:
                                legal=not(parent_evolution and remp) and all(not(child_evolution and x) and not(m==-1 and x) for x,m in zip(rem,modes)) and not(remp and -1 in modes)
                            children=tuple(mod.Plan('h',(x,),evolution=((ce,e),) if child_evolution else (),mode=m) for x,e,m in zip(old,ev,modes))
                            plan=mod.Plan('skin',(P,),children,evolution=((pe,ep),) if parent_evolution else ())
                            try:forest,up,records=mod.expanded_oracle(plan,rules);accepted=True
                            except ValueError:accepted=False
                            assert accepted==legal,(P,a,b,ep,ea,eb,ma,mb,parent_evolution,child_evolution)
                            stats['independent_old_resource_and_maximality_cases']+=1
                            if legal:
                                yparent=remp+2*ep;expected=[]
                                for x,e,m,left in zip(old,ev,modes,rem):
                                    y=left+2*e+int(m==0)
                                    if m==2:yparent+=y+1
                                    else:
                                        expected.extend([y+1,y+1] if m==3 else [y]);yparent+=int(m==1)
                                assert len(forest)==1 and forest[0].x==(yparent,) and sorted(c.x[0] for c in forest[0].children)==sorted(expected) and up==(0,)
                                stats['independent_concrete_updates']+=1
    return dict(stats)

def author_checks(universal,motif):
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0');out={}
    with tempfile.TemporaryDirectory(prefix='membrane-independent-replay-') as tmp:
        tmp=Path(tmp);u=tmp/'universal';m=tmp/'motif'
        shutil.copytree(universal,u,ignore=shutil.ignore_patterns('__pycache__','*.pyc'));shutil.copytree(motif,m,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        p=subprocess.run([sys.executable,str(u/'reproduce.py'),'--receipt',str(tmp/'universal_receipt.json')],capture_output=True,text=True,env=env,timeout=300)
        if p.returncode:raise RuntimeError(p.stdout+p.stderr)
        out['universal']=json.loads((tmp/'universal_receipt.json').read_text())
        p=subprocess.run([sys.executable,str(m/'replay/run_all.py')],capture_output=True,text=True,env=env,timeout=300)
        if p.returncode:raise RuntimeError(p.stdout+p.stderr)
        files=['replay_receipt.json','focused_receipt.json','saved_example_receipt.json','regression_extensions_receipt.json','quartic_receipt.json','examples.json','contextual_copy_polynomials.json','contextual_copy_quartic.json']
        for name in files:assert (m/'replay'/name).read_bytes()==(motif/'replay'/name).read_bytes(),name
        out['motif']={'status':'passed','exact_regenerated_files':{name:digest(m/'replay'/name) for name in files},'checks':{name:json.loads((m/'replay'/name).read_text()) for name in files[:5]},'nonsemantic_metadata_omitted':'run_receipt.json timestamp, interpreter/platform and subprocess timing fields'}
    return out

def run(universal_root,motif_root,*,authors=False):
    roots={'universal':Path(universal_root).resolve(),'motif':Path(motif_root).resolve()}
    for label,entries in PINS.items():
        for relative,expected in entries.items():
            if digest(roots[label]/relative)!=expected:raise ValueError('source hash mismatch: '+label+'/'+relative)
    out={'status':'passed','source_pins':PINS,'quadratic':quadratic_checks(roots['universal']),'motif':motif_checks(roots['motif']),'scope':'Full proof/source human review plus bounded independent exact checks; no formal proof or fixed-arity unbounded-time claim.'}
    if authors:out['author_replay']=author_checks(roots['universal'],roots['motif'])
    return out

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('universal_root',type=Path);p.add_argument('motif_root',type=Path);p.add_argument('--authors',action='store_true');p.add_argument('--output',type=Path);a=p.parse_args()
    result=run(a.universal_root,a.motif_root,authors=a.authors);text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(text)
    else:print(text,end='')
