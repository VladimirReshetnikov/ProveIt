#!/usr/bin/env python3
"""Rebuild the selected 478-integer quartic using only local, pinned inputs."""
import sys
sys.dont_write_bytecode=True
import argparse,json,tempfile
from pathlib import Path
import terminal_elimination as E
from transform import transform,typed_budget,hash_obj
from translate_coordinates import translate

HERE=Path(__file__).resolve().parent

def generate(out):
    old=json.loads((HERE/'source/parent.json').read_text())
    domain=json.loads((HERE/'source/domain.json').read_text())
    source,cert=transform(old,frame=True,signed_comparison=True,joint_anchor=True)
    budget=typed_budget(source,domain,cert)
    cert['pre_budget_target_sha256']=cert['target_sha256'];cert['target_sha256']=hash_obj(source)
    target,projection,metrics=E.optimize(source,max_support=16)
    replay=E.verify(source,target,projection)
    shifts={i:-1 for i,v in enumerate(target['variables'])if v['name'].startswith('crt.encoded')or v['name']in('t0','M0')or v['name'].endswith('minus1')}
    centered=translate(target,shifts);expanded=E.expand(centered)
    measurements={'variables':len(centered['variables']),'rows':len(centered['residuals']),'degree':max(len(m)for c,m in expanded['terms']),'monomials':len(expanded['terms']),'height':max(abs(c)for c,m in expanded['terms']),'row_height':max(abs(c)for r in centered['residuals']for c,m in r['terms'])}
    translation={'source_sha256':hash_obj(target),'target_sha256':hash_obj(centered),'shifts':[[i,s]for i,s in sorted(shifts.items())],'convention':'old = new + shift'}
    result={'fused_source.json':source,'fusion_certificate.json':cert,'budget_certificate.json':budget,'uncentered_equation.json':target,'projection_certificate.json':projection,'translation_certificate.json':translation,'equation.json':centered,'expanded_polynomial.json':expanded,'METRICS.json':measurements,'REPLAY.json':replay}
    out.mkdir(parents=True,exist_ok=True)
    for name,obj in result.items():(out/name).write_bytes(E.canonical_bytes(obj))
    return list(result)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');ap.add_argument('--output',type=Path);args=ap.parse_args()
    if args.check:
        with tempfile.TemporaryDirectory(prefix='conzfc-direct-rebuild-')as d:
            out=Path(d);names=generate(out)
            for n in names:
                if (out/n).read_bytes()!=(HERE/n).read_bytes():raise ValueError('rebuild differs: '+n)
            print(json.dumps({'status':'PASS','byte_exact_files':names}))
    else:
        out=args.output or HERE/'rebuilt';names=generate(out);print(json.dumps({'status':'PASS','output':str(out),'files':names}))

if __name__=='__main__':main()
