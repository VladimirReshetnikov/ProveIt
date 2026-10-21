"""Check the pure-reuse receipt against its two independently reviewed packets.

This binds saved records/archives only, never imports archived code or inspects
live objects. The predecessor readers retain the deeper kernel-run audits.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,tarfile,re
sha=lambda b:hashlib.sha256(b).hexdigest()
BAD={'.olean','.ilean','.o','.so','.a','.vo','.vos','.vok','.glob','.pyc','.pyo'}

def load(root,ref):
    p=PurePosixPath(ref['repository_relative_directory']);assert not p.is_absolute()and '..'not in p.parts
    packet=root/str(p);files={n:(packet/n).read_bytes()for n in ref['files']}
    assert all(sha(b)==ref['files'][n]for n,b in files.items())
    index=json.loads(files['index.json']);data={}
    with tarfile.open(packet/'execution.tar.gz','r:gz')as t:
        for e in t:
            p=PurePosixPath(e.name);assert e.isfile()and not p.is_absolute()and '..'not in p.parts and not set(p.suffixes)&BAD and e.name not in data
            b=t.extractfile(e).read();assert index[e.name]=={'sha256':sha(b),'bytes':len(b)};data[e.name]=b
    assert data.keys()==index.keys()
    return packet,files,data

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output',type=Path,required=True);a=p.parse_args();assert not a.output.exists()
    r=json.loads((a.packet/'result.json').read_text());assert r['status']=='PASS_LIVE_PURE_REUSE_LEGACY_CONTINUITY'
    assert(r['primary_modules'],r['legacy_only_modules'],r['union_modules'],r['fresh_legacy_modules'])==(187,15,202,0)
    assert not r['new_legacy_audit_executed']and r['all202_provider_objects_and_selected_logs_rehashed_after_historical_audit']and r['toolchain_unchanged']
    assert sha((a.packet/'review.py').read_bytes())==r['reviewer_sha256']
    _,pf,pm=load(a.repo,r['references']['phase6_primary']);_,lf,lm=load(a.repo,r['references']['phase5_legacy'])
    J=lambda d,n:json.loads(d[n]);pr=J(pm,'execution/result.json');old=J(lm,'execution/result.json')
    assert sha(pm['execution/result.json'])==r['primary_result_sha256']and sha(lm['execution/result.json'])==r['old_legacy_result_sha256']
    assert sha(pf['live-review.json'])==r['primary_live_review_sha256']
    assert pr['status']==old['status']=='PASS'and pr['primary_project_modules']==187 and old['project_modules']==199
    done=J(pm,'execution/completed.json');legacy=J(lm,'execution/completed.json');pmod={e['module']:e for e in J(pm,'execution/inventory.json')['modules']};lmod={e['module']:e for e in J(lm,'execution/inventory.json')['modules']}
    extra=set(lmod)-set(pmod);assert len(extra)==15 and{e['module']for e in r['legacy_bindings']}==extra
    allrec={**done,**{m:legacy[m]for m in extra}};allmod={**pmod,**{m:lmod[m]for m in extra}};assert len(allrec)==len(allmod)==202
    for b in r['legacy_bindings']:
        m=b['module'];oldrow=legacy[m];assert b['imports']==lmod[m]['imports']and b['source_sha256']==lmod[m]['source_sha256']
        for k in ('source_sha256','object_sha256','log_sha256','dependencies'):assert b[k]==oldrow[k]
        assert b['dependencies']=={d:allrec[d]['object_sha256']for d in b['imports']if d in allrec}
    h=r['historical_audit'];assert h['new_execution']is False
    for field in ('source_sha256','log_sha256','object_sha256'):assert h[field]==old['audit'][field]
    text=lm['execution/audit/compiler.log'].decode();named=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",text)
    assert[list(x)for x in named]==h['reports']
    assert[n for n,_ in named]==['SetTheory.BusyBeaver.ZFC.LegacyAudit.'+n for n in ('root222','root219','rootDom','rootPerm','offset_checker')]
    src=lm['execution/audit/LegacyAudit.lean'];assert sha(src)==h['source_sha256']and sha(lm['execution/audit/compiler.log'])==h['log_sha256']
    imports=[v for l in src.decode().splitlines()if l.startswith('import ')for v in l[7:].split()];assert imports==h['direct_imports']
    reachable=set()
    def visit(m):
        if m=='Init'or m in reachable:return
        reachable.add(m)
        for d in allmod[m]['imports']:visit(d)
    for m in imports:visit(m)
    assert len(reachable)==45 and set(h['unchanged_transitive_project_provider_hashes'])==reachable
    for m,pin in h['unchanged_transitive_project_provider_hashes'].items():assert allrec[m]['object_sha256']==legacy[m]['object_sha256']==pin and allmod[m]==lmod[m]
    result={'status':'PASS_SAVED_PURE_REUSE_BINDINGS','receipt_sha256':sha((a.packet/'result.json').read_bytes()),'primary_modules':187,'retained_legacy_modules':15,'union_modules':202,'fresh_legacy_modules':0,'historical_audit_transitive_project_providers':45,'new_compiler_or_audit_execution':False,'live_objects_checked':False,'scope':'Saved continuity bindings to two exact independently reviewed packet archives; historical audit source/report and all45 provider hashes unchanged. No deep predecessor validator or proof compiler is invoked here.'}
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
