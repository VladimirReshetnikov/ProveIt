#!/usr/bin/env python3
"""Read-only audit of both auxiliary-seed suffix chains; no Lean invocation."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-auxiliary-seed'
PARENT=BASE/'reviews/thirteen-model-strong-seed-independent-audit'
STRONG=Path('/tmp/ipra-thirteen-strong-seed-pair-01')
OUT=Path('/tmp/ipra-thirteen-aux-seed-pair-01')
RECEIPT='3907252c1f418da6ab71b3321c0659312cef6072f3f2191a45cd893ad52505b0'
PARENT_RECEIPT='5f57f5bbb21646000f020480c2d87749e464361453be34107e530420ca9d5362'
SRC={'ArithmeticPellSquaredSeed':'cb9ebc4a3e3477a1eb672d9ed4665107b4ea5d33e650c9d1a0d3889ce7dfeb05',
     'ArithmeticPellAuxiliarySeed':'c20a64d1587b74dc7f18c208ba6f96052cbcfbf29da8c0e2567551055501f773',
     'ModelBAuxiliary':'b0dcb4f10d58737d380219b1347d5785be38fceea495a68d703541d282d13f78'}
OBJ={'ArithmeticPellSquaredSeed':'aa69e9d3f843badf0877227010161177ad130427e23757163d2b61ec700c8f12',
     'ArithmeticPellAuxiliarySeed':'19b12451dacc6a515a082869a6ff5667153d8392678b8deeed678fa7d0a49ee4',
     'ModelBAuxiliary':'1cd597b9ca5da02b163056bb1d0874a0ff1deda2f6e8ca72b6ffe2658cf8ebfa'}


def need(ok,msg):
    if not ok:raise ValueError(msg)


def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def coord(a,t):
    x,y=1,0;delta=(a+1)*(a+3)
    for _ in range(t):x,y=(a+2)*x+delta*y,x+(a+2)*y
    return x,y


def main():
    files={'ModelBAuxiliary':PKG/'ModelBAuxiliary.lean',
           'ArithmeticPellSquaredSeed':BASE/'Lean/DiophantineConsistency/ArithmeticPellSquaredSeed.lean',
           'ArithmeticPellAuxiliarySeed':BASE/'Lean/DiophantineConsistency/ArithmeticPellAuxiliarySeed.lean'}
    for name,path in files.items():
        data=subprocess.run(['git','show','d636a93093:'+path.relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(hashlib.sha256(data).hexdigest()==digest(path)==SRC[name],'source pin '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes());r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(obs['session_id']==70281 and obs['outer_exit_code']==0 and obs['receipt_sha256']==RECEIPT and
         obs['stdout']=='PASS_PAIRED_THIRTEEN_AUXILIARY_SEED '+RECEIPT and
         digest(PKG/'replay-receipt.json')==digest(OUT/'receipt.json')==RECEIPT,'recorded outer exit and receipt')
    need(r['status']=='PASS_PAIRED_THIRTEEN_AUXILIARY_SEED' and len(r['runs'])==2,'paired status')
    parent=json.loads((PARENT/'CHECK.json').read_bytes());pt=json.loads((PARENT/'terminal-observation.json').read_bytes())
    need(digest(PARENT/'CHECK.json')==PARENT_RECEIPT and pt['audit_observed_exit_code']==0 and pt['receipt_sha256']==PARENT_RECEIPT and
         parent['status']=='PASS_INDEPENDENT_THIRTEEN_MODEL_STRONG_SEED_AUDIT','parent independent audit')
    for path,h in r['fixed_inputs_sha256'].items():need(digest(path)==h,'fixed input '+path)
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],cwd=ROOT,capture_output=True,text=True,timeout=180)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==r['parent_audit'],'fresh read-only parent audit')
    summaries=[]
    for row,side in zip(r['runs'],('author','peer')):
        need(row['label']==side and len(row['modules'])==3,'side modules')
        run=OUT/side;project=run/'lib/DiophantineConsistency';prior=STRONG/side/'lib/DiophantineConsistency'
        links=row['parent_links_sha256'];need(len(links)==66,'parent links count')
        need(set(links)=={str(project/p.name) for p in prior.glob('*.olean')},'parent link coverage')
        for link,h in links.items():
            q=Path(link);need(q.is_symlink() and q.resolve()==(prior/q.name).resolve() and digest(q)==h,'parent link '+link)
        need((run/'lib/BusyBeaver').is_symlink() and
             (run/'lib/BusyBeaver').resolve()==(STRONG/side/'lib/BusyBeaver').resolve(),'BusyBeaver link')
        for item,name in zip(row['modules'],('ArithmeticPellSquaredSeed','ArithmeticPellAuxiliarySeed','ModelBAuxiliary')):
            src=run/'src/DiophantineConsistency'/(name+'.lean');obj=project/(name+'.olean')
            need(item['name']==name and item['exit']==item['deps_exit']==0 and not item['stderr'],'child exit '+side+' '+name)
            need(digest(src)==item['source_sha256']==SRC[name] and not obj.is_symlink() and digest(obj)==item['object_sha256']==OBJ[name],'source/object '+name)
            need(item['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and item['command'][-1]==str(obj),'bounded command '+name)
            init='/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean'
            if name=='ArithmeticPellSquaredSeed':deps={init,str(project/'ArithmeticPellPeriodicity.olean')}
            elif name=='ArithmeticPellAuxiliarySeed':deps={init,str(project/'ArithmeticPellSquaredSeed.olean'),str(project/'ArithmeticPellHalfIndex.olean')}
            else:deps={init,str(project/'ModelBSeed.olean'),str(project/'ArithmeticPellAuxiliarySeed.olean')}
            need(set(item['deps_stdout'].splitlines())==deps and all(Path(d).is_file() for d in deps),'direct imports '+name)
            if name=='ModelBAuxiliary':
                need(item['stdout']=="'ModelBAuxiliary.auxiliary_seed_with_multiplier' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and
                     item['axiom_reports']==['propext, Classical.choice, Quot.sound'],'theorem axiom report')
            else:need(not item['stdout'] and not item['axiom_reports'],'unexpected intermediate diagnostics')
        summaries.append({'side':side,'parent_links':len(links),'objects':[OBJ[x] for x in SRC],
                          'recorded_compiler_exits':[0,0,0],'recorded_dependency_exits':[0,0,0]})

    # Six ordinary finite constructions; they supplement the arbitrary-model
    # theorem and do not establish any signed carrier or graph equivalence.
    samples=[]
    for a in range(3):
      R=3;c=coord(a,R)[1];delta=(a+1)*(a+3)
      for b in (1,2):
        N=b*c*c;x,y=1,0
        for t in range(1,min(N*N,100000)+1):
            x,y=((a+2)*x+delta*y)%N,(x+(a+2)*y)%N
            if y==0:break
        else:raise ValueError('finite seed search')
        f,ordinary_y=coord(a,t);i=ordinary_y//N;I=delta*b*i*c*c
        ax,aux_y=coord(I-2,R);u,rem=divmod(ax,I)
        T,remT=divmod(u+c+f*f*R,f*f*c)
        need(R%4==3 and b>0 and min(c,f,i,I,u,aux_y,T)>0 and rem==remT==0 and
             f*f==1+delta*(b*i*c*c)**2 and (u+c)%(f*f)==0 and (u+R)%c==0 and
             u==abs(f*f*c*T-(f*f*R+c)) and I*I*u*u+aux_y*aux_y==1+I*I*aux_y*aux_y,'finite auxiliary case')
        samples.append({'a':a,'R':R,'b':b,'strong_index':t})
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_MODEL_AUXILIARY_AUDIT','source_commit':'d636a93093',
      'recorded_outer_exit':obs['outer_exit_code'],'recorded_outer_session':obs['session_id'],'author_receipt_sha256':RECEIPT,
      'parent_audit_sha256':PARENT_RECEIPT,'read_only_parent_audit_exit':p.returncode,'runs':summaries,'finite_samples':samples,
      'scope':'Read-only paired suffix artifact audit and finite standard examples; no Lean rerun, signed carrier, fixed-port calibration, 69-op converse or iPRA theorem.'},indent=2))


if __name__=='__main__':main()
