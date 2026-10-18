#!/usr/bin/env python3
"""Recheck pair merges under inherited interval and recurrent tape resources.

Fixtures are finite representatives of the older interval invariant. They use
the real 246 bootstrap's minimum header distance and homogeneous spare count.
They are not claims that each represented configuration occurs from blank.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--metadata', type=Path, required=True)
    ap.add_argument('--table', type=Path, default=Path(__file__).with_name('zfc_prefix246_old.tm'))
    ap.add_argument('--literal-helper', type=Path, required=True)
    ap.add_argument('--output', type=Path, default=Path(__file__).with_name('resource-merge-cases.txt'))
    args=ap.parse_args()
    spec=importlib.util.spec_from_file_location('literal_instructions',args.literal_helper)
    lit=importlib.util.module_from_spec(spec);spec.loader.exec_module(lit)
    table_path=args.table
    table=lit.read_table(table_path)
    metadata=json.loads(args.metadata.read_text())
    assert len(metadata)==8385
    lines=[str(len(table))]
    for (q,b),(w,d,t) in sorted(table.items()):
        lines.append(f'{q} {b} {w} {d} {t}')
    lines.append(str(len(metadata)))
    for fixture in metadata:
        pc,kind,r=fixture['pc'],fixture['instruction'],fixture['logical_register']
        regs=fixture['physical_values']
        spares=[1]*167
        initial=lit.paint(pc,181,regs,spares,0)
        expected=lit.expected(pc,kind,r,regs,spares,0,181)
        head=0 if expected is None else expected[0]
        target=[] if expected is None else sorted(expected[1])
        source=sorted(initial)
        assert min(source)>=-1 and max(source)<1984
        lines.append(' '.join(map(str,[int(kind=='CH'),head,len(source),*source,len(target),*target])))
    args.output.write_text('\n'.join(lines)+'\n')
    result={'cases':len(metadata),'spares':{'count':167,'all_values':1},'header_distance':181,
            'scope':__doc__,'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                for p in (args.metadata,args.literal_helper,table_path)}}
    args.output.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
