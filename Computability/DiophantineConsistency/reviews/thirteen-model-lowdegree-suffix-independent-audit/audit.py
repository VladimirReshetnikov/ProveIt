#!/usr/bin/env python3
"""Audit the paired four-module later-source endpoint suffix without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/thirteen-model-lowdegree-suffix';SOURCE=BASE/'Lean/DiophantineConsistency';OUT=Path('/tmp/ipra-thirteen-lowdegree-pair-01');PARENT=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');AUDIT=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit'
RECEIPT='2ca8a5e4d7f417b5c6e3a0f00bba71f529e98af2497e089f024a2743e52c5f2c';ANCHOR='6f8dd13085';NAMES=('ModelThirteenForms','ModelThirteenStrong','ModelThirteenSquares','ModelThirteenChecks');SHAS=('98d9dcc48895ffe026c029b2496a61a35b66bca2f7b2fd1b31b8acf43acbfb6f','f68b89af4d639362b5cbff423277f683fd5ff04518678c5b40deff5d436b5897','203ef326964cfc8f7546cc6e13e4e6c4def5d6d0f6027241f7b960adc7ca6700','95d60407a62036e7996fc583353758e9d23f305201e702dd7e81b2a4e2c29667');REPORTS=[f'DiophantineConsistency.ModelThirteenStrong.{kind}_equivalence{n}' for n in (73,74,72) for kind in ('native','standard','reference')]+[f'DiophantineConsistency.ModelThirteenSquares.{kind}_equivalence{n}' for n in (77,76,75,84) for kind in ('native','standard','reference')]+[f'DiophantineConsistency.ModelThirteenForms.{kind}_equivalence{n}' for n in (70,71) for kind in ('native','standard','reference')]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    prefix=PKG.relative_to(ROOT).as_posix()+'/';names=subprocess.run(['git','ls-tree','-r','--name-only','e4b90853ef','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines();need(len(names)==12,'packet inventory')
    for name in names:
        p=ROOT/name;b=subprocess.run(['git','show','e4b90853ef:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==sha(p),'committed evidence '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes());need(obs['session']==56787 and obs['actual_exit_code']==0 and obs['receipt_sha256']==RECEIPT and obs['stdout']=='PASS_PAIRED_THIRTEEN_LOWDEGREE_SUFFIX '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes());need(r['status']=='PASS_PAIRED_THIRTEEN_LOWDEGREE_SUFFIX' and r['source_anchor']==ANCHOR and len(r['rows'])==8 and json.loads((OUT/'progress.json').read_bytes())==r['rows'],'rows')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed '+path)
    need(sha(PKG/'replay.py')==r['driver_sha256'],'driver hash')
    for name,h in zip(NAMES,SHAS):
        p=SOURCE/(name+'.lean');b=subprocess.run(['git','show',ANCHOR+':'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p)==sha(OUT/'src/DiophantineConsistency'/(name+'.lean'))==h,'anchored source '+name)
    for module,numbers in [('ModelThirteenForms',(70,71)),('ModelThirteenStrong',(73,74,72)),('ModelThirteenSquares',(77,76,75,84))]:
        text=(SOURCE/(module+'.lean')).read_text()
        for n in numbers:
            for kind in ('native','standard','reference'):
                name=f'{kind}_equivalence{n}';hit=re.search(r'theorem\s+'+name+r'\s*:\s*(.*?)\s*:=',text,re.S);need(hit is not None,'missing theorem '+name)
                actual=re.sub(r'\s+','',hit.group(1));e=f'(positiveShift(expressionAt{n}CurrentWindowCarry2011.ports))'
                if kind=='native':expected='nativeTheory⊢IPRAExpressionNative.nativeNoZero'+e+'🡘∼mappedNativeRefutationembedding'
                elif kind=='standard':expected='IPRAStandardTheory.standardTheory⊢IPRAExpressionNative.nativeNoZero'+e+'🡘∼mappedNativeRefutationembedding'
                else:expected='IPRAEqualityOnlyReference.referenceTheory⊢IPRAOrderErasure.erase(IPRAExpressionNative.nativeNoZero'+e+')🡘∼IPRAOrderErasure.erase(mappedNativeRefutationembedding)'
                need(actual==expected,'exact statement '+module+'.'+name)
    import os
    for key,v in r['direct_guards'].items():
        p=Path(key)
        if v is None:need(not os.path.lexists(p),'unexpected companion '+key)
        else:need(p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'companion '+key)
    results=[]
    for si,side in enumerate(('author','peer')):
        lib=OUT/side/'lib';base=PARENT/side/'lib';pfiles={p.relative_to(base) for p in base.rglob('*.olean')};files={p.relative_to(lib) for p in lib.rglob('*.olean')};extra={Path('DiophantineConsistency')/(n+'.olean') for n in NAMES}
        need(files==pfiles|extra and not(pfiles&extra),'overlay inventory '+side)
        for rel in pfiles:need((lib/rel).is_symlink() and (lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'parent overlay '+str(rel))
        warnings=[]
        for ix,name in enumerate(NAMES):
            row=r['rows'][4*si+ix];src=OUT/'src/DiophantineConsistency'/(name+'.lean');obj=lib/'DiophantineConsistency'/(name+'.olean');log=OUT/side/(name+'.log');dep='ModelThirteenCarrier' if ix==0 else NAMES[ix-1]
            need(row['side']==side and row['module']==name and row['exit']==row['deps_exit']==0 and row['stop_reason'] is None,'recorded child '+name)
            need(sha(src)==row['source_sha256']==SHAS[ix] and obj.is_file() and not obj.is_symlink() and sha(obj)==row['object_sha256'],'source/object '+name)
            need(Path(row['log'])==log and sha(log)==sha(PKG/'logs'/(side+'-'+name+'.txt'))==row['log_sha256'],'log '+name)
            cmd=row['command'];need(cmd[1:4]==['-M4000','-j1','-DElab.async=false'] and cmd[4]=='--root='+str(OUT/'src') and cmd[-3:]==[str(src),'-o',str(obj)],'command '+name)
            deps={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency'/(dep+'.olean'))};need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct deps '+name)
            text=log.read_text();need(not re.search(r'(?m)^.*error:|\bsorryAx\b|\bsorry\b',text),'admission '+name)
            found=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M);need([list(x) for x in found]==row['axiom_reports'],'report parse '+name)
            if name=='ModelThirteenChecks':need([x[0] for x in found]==REPORTS and all({y.strip() for y in a.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,a in found),'27 exact reports')
            else:need(not found,'unexpected reports '+name)
            warnings.extend((name,line.split('warning:',1)[1].strip()) for line in text.splitlines() if 'warning:' in line)
        need(len(warnings)==6 and sum('deprecated' in x[1] for x in warnings)==3 and sum('unused' in x[1] or 'not explicitly referenced' in x[1] for x in warnings)==3,'warning classes')
        results.append({'side':side,'rows':4,'parent_project_objects':len(pfiles),'warnings':warnings,'axiom_reports':27})
    for i in range(4):need(all(r['rows'][i][k]==r['rows'][i+4][k] for k in ('source_sha256','object_sha256','log_sha256')),'sibling hashes')
    parent=json.loads((AUDIT/'CHECK.json').read_bytes());need(r['parent_audit']==parent and sha(AUDIT/'CHECK.json')=='50c18ab38d6393cf784e658b5626bb6ec3cb490dc1652f5b5dcfa2b1adca1cce','parent receipt')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,timeout=900);need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==parent,'parent audit rerun')
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_LOWDEGREE_SUFFIX_AUDIT','source_commit':'e4b90853ef','author_receipt_sha256':RECEIPT,'source_anchor':ANCHOR,'recorded_outer_session':56787,'recorded_outer_exit':0,'parent_audit_rerun_exit':p.returncode,'direct_guard_paths':len(r['direct_guards']),'exact_statement_count':27,'exact_axiom_names':REPORTS,'runs':results,'scope':'Compiled source-expression endpoint suffix only; external graph bindings, exact degree/operation counts, translated-consistency variants and PDF presentation remain separate.'},indent=2))
if __name__=='__main__':main()
