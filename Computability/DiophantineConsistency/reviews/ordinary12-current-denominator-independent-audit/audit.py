#!/usr/bin/env python3
"""Read-only audit of the coherent 12-suffix paired composition."""
import ast
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-current-denominator-composition'
HERE=Path(__file__).resolve().parent
MONITOR=BASE/'reviews/ordinary12-rss-retry-independent-audit'
PARENT=BASE/'reviews/ordinary12-coexistence-pair-independent-audit'
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
SNAP=Path('/tmp/ipra-ordinary12-coexistence-source-03')
OUT=Path('/tmp/ipra-freej-current-denominator-rebuild-04')
RECEIPT='a9517710d23a1576f04610ef00f3e16038086eed2956fddc2cd0cf76f006ef7b'
MANIFEST='9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded'
DRIVER='2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8'
PARENT_RECEIPT='5f1fc7a6f519088588ed568e3266da6d109490d556d459a7949d257cbb1bc11d'
MONITOR_RECEIPT='d242ed0f7cbe0e9b56330f993cd2bf7cc5da61c92aefb6e39fd34a0247c22cdf'
REPORTS=['FreeJCurrentDenominator.denominator_shape','FreeJCurrentDenominator.denominator_eval',
         'FreeJCurrentDenominator.auxiliary_with_nonzero_denominator']


def need(ok,msg):
    if not ok:raise ValueError(msg)


def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    rel=PKG.relative_to(ROOT).as_posix()
    author_tree=subprocess.run(['git','ls-tree','-r','--name-only','d40b6397f5','--',rel],cwd=ROOT,capture_output=True,text=True,check=True).stdout.splitlines()
    diff=subprocess.run(['git','diff','--exit-code','d40b6397f5','--',rel],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    need(len(author_tree)==48 and diff.returncode==0,'committed author packet drift')
    obs=json.loads((PKG/'evidence/terminal.json').read_bytes());r=json.loads((PKG/'evidence/receipt.json').read_bytes())
    need(obs['status']=='OBSERVED_PAIRED_TERMINAL' and obs['session_id']==52014 and obs['wrapper_actual_exit']==0 and
         obs['receipt_sha256']==RECEIPT and obs['driver_sha256']==DRIVER and
         obs['wrapper_stdout_last_line']=='PASS_PAIRED_CURRENT_DENOMINATOR_COMPOSITION '+RECEIPT,'outer observation')
    need(digest(PKG/'evidence/receipt.json')==digest(OUT/'receipt.json')==RECEIPT and
         r['status']=='PASS_PAIRED_CURRENT_DENOMINATOR_COMPOSITION' and len(r['runs'])==24,'paired receipt')
    need(digest(PKG/'replay.py')==digest(MONITOR/'driver-2c8.py')==DRIVER,'reviewed driver bytes')
    ma=json.loads((MONITOR/'CHECK.json').read_bytes());mt=json.loads((MONITOR/'terminal-observation.json').read_bytes())
    need(digest(MONITOR/'CHECK.json')==MONITOR_RECEIPT and mt['audit_observed_exit_code']==0 and mt['receipt_sha256']==MONITOR_RECEIPT and
         ma['status']=='PASS_INDEPENDENT_BOUNDED_RSS_RETRY_REVIEW','independent monitor review')
    pa=json.loads((PARENT/'CHECK.json').read_bytes());pt=json.loads((PARENT/'terminal-observation.json').read_bytes())
    need(digest(PARENT/'CHECK.json')==PARENT_RECEIPT and pt['audit_observed_exit_code']==0 and pt['receipt_sha256']==PARENT_RECEIPT and
         pa['status']=='PASS_INDEPENDENT_70_SOURCE_COEXISTENCE_ARTIFACT_AUDIT','independent parent review')
    # At this post-run instant both manifest files and their declared source
    # bytes agree. This does not authenticate the driver's earlier read.
    repo_manifest=BASE/'research/ordinary12-ipra-bridge/difference-ring-build-plan/coherent-replay/source-freeze-evidence-03/manifest.json'
    need(digest(repo_manifest)==digest(SNAP/'manifest.json')==MANIFEST==pa['source_manifest_sha256'],'post-run manifest')
    manifest=json.loads(repo_manifest.read_bytes());names=manifest['order'];need(len(names)==70 and len(set(names))==70,'parent source count')
    for name in names:
        source=manifest['sources'][name];need(digest(SNAP/source['snapshot_path'])==digest(ROOT/source['workspace_path'])==source['sha256'],'post-run parent source '+name)
    # Read the exact reviewed driver's source pins without executing it.
    tree=ast.parse((PKG/'replay.py').read_bytes());items=[n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='SOURCES' for t in n.targets)]
    need(len(items)==1,'driver sources declaration');suffix=ast.literal_eval(items[0].value);need(len(suffix)==12,'suffix count')
    for rel,h,_ in suffix:need(digest(BASE/'research/ordinary12-ipra-bridge'/rel)==h,'post-run suffix source '+rel)
    cmp=BASE/'research/fresh-project-closure/compare.py'
    p=subprocess.run([sys.executable,'-I','-S','-B',str(cmp),str(PAIR/'author/child-output/state.json'),str(PAIR/'peer/child-output/state.json')],cwd=ROOT,capture_output=True,text=True,timeout=120)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==r['parent_comparison'],'fresh parent comparison')
    package='/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean';summaries=[];normalized=[]
    for side,offset in (('author',0),('peer',12)):
        lib=OUT/side/'lib';parentlib=PAIR/side/'child-output/lib';parentstate=json.loads((PAIR/side/'child-output/state.json').read_bytes())
        parentrows={x['module']:x for x in parentstate['records']};need(set(parentrows)==set(names),'parent records')
        expected_inventory=set()
        for name in names:
            local=lib/Path(*name.split('.')).with_suffix('.olean');original=parentlib/Path(*name.split('.')).with_suffix('.olean')
            need(local.is_symlink() and local.resolve()==original.resolve() and digest(local)==parentrows[name]['object_sha256'],'parent object link '+name)
            expected_inventory.add(local)
        available=set(names);rows=[];peaks=[]
        for i,(rel,h,count) in enumerate(suffix):
            item=r['runs'][offset+i];module='DiophantineConsistency.'+Path(rel).stem
            src=OUT/side/'src/DiophantineConsistency'/Path(rel).name;obj=lib/'DiophantineConsistency'/(Path(rel).stem+'.olean')
            need(item['label']==side and item['module']==module and item['exit']==item['deps_exit']==0 and item['stop_reason'] is None,'row exit '+module)
            need(digest(src)==item['source_sha256']==h and not obj.is_symlink() and digest(obj)==item['object_sha256'],'source/object '+module)
            need(item['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and item['command'][-1]==str(obj),'compiler command '+module)
            log=Path(item['log']);copy=PKG/'evidence'/side/(Path(rel).stem+'.log')
            need(log==OUT/side/(Path(rel).stem+'.log') and digest(log)==item['log_sha256'] and log.read_bytes()==copy.read_bytes(),'compiler log '+module)
            text=log.read_text();need(not re.search(r'warning:|sorryAx|\bsorry\b|error:',text),'compiler diagnostics '+module)
            reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
            need(len(reports)==count and [v for _,v in reports]==item['axiom_reports'] and
                 all({x.strip() for x in vals.split(',')}<={'propext','Classical.choice','Quot.sound'} for _,vals in reports),'axiom reports '+module)
            if i==11:need([n for n,_ in reports]==REPORTS,'composition theorem reports')
            imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M)
            need(imports and all(x in available for x in imports),'declared source order '+module)
            deps={package}|{str(lib/Path(*name.split('.')).with_suffix('.olean')) for name in imports}
            need(set(item['deps_stdout'].splitlines())==deps,'exact direct imports '+module)
            for dep in imports:
                path=lib/Path(*dep.split('.')).with_suffix('.olean');need(path.is_file(),'direct dependency exists '+dep)
                if dep in parentrows:need(path.is_symlink() and digest(path)==parentrows[dep]['object_sha256'],'audited parent dependency '+dep)
                else:need(not path.is_symlink() and dep in available,'fresh suffix dependency '+dep)
            peak=item['peak_sampled_rss_bytes'];need(0<peak<=int(3.5*1024**3),'sampled peak '+module);peaks.append(peak)
            expected_inventory.add(obj);available.add(module)
            rows.append({'module':module,'source_sha256':h,'object_sha256':item['object_sha256'],'log_sha256':item['log_sha256'],'axiom_reports':item['axiom_reports']})
        actual={p for p in lib.rglob('*') if p.is_file() or p.is_symlink()}
        need(actual==expected_inventory,'parent plus suffix object inventory '+side)
        need({p.name for p in (PKG/'evidence'/side).glob('*.log')}=={Path(rel).stem+'.log' for rel,_,_ in suffix},'copied log inventory '+side)
        normalized.append(rows);summaries.append({'side':side,'parent_links':70,'suffix_rows':12,'compiler_exits':12,
            'dependency_exits':12,'maximum_sampled_leader_rss_bytes':max(peaks)})
    need(normalized[0]==normalized[1],'independent paired suffix match')
    rowdigest=hashlib.sha256(json.dumps(normalized[0],sort_keys=True,separators=(',',':')).encode()).hexdigest()
    head=subprocess.run(['git','rev-parse','HEAD'],cwd=ROOT,capture_output=True,text=True,check=True).stdout.strip()
    print(json.dumps({'status':'PASS_INDEPENDENT_CURRENT_DENOMINATOR_COMPOSITION_AUDIT',
      'proof_packet_commit':'6a852a749c','retained_logs_commit':'44b1d4fd2c','wording_commit':'d40b6397f5',
      'committed_author_files':len(author_tree),'author_receipt_sha256':RECEIPT,
      'recorded_wrapper_session':52014,'recorded_wrapper_exit':0,'driver_sha256':DRIVER,
      'monitor_review_sha256':MONITOR_RECEIPT,'parent_audit_sha256':PARENT_RECEIPT,'parent_comparator_rerun_exit':p.returncode,
      'runs':summaries,'matched_suffix_rows':12,'matched_row_digest':rowdigest,'post_run_manifest_sha256':MANIFEST,
      'post_run_70_parent_and_12_suffix_source_hashes_match':True,'post_run_observed_utc':datetime.now(timezone.utc).isoformat(),
      'post_run_observed_head':head,'endpoint_reports':REPORTS,
      'scope':'Read-only artifact audit, not Lean rerun. The live driver did not pin manifest bytes at read; post-run checks do not exclude transient drift. Shared package-transitive/dynamic ancestry, Foundation outer exit, resource quotas, integrality, calibration and iPRA remain outside scope.'},indent=2))


if __name__=='__main__':main()
