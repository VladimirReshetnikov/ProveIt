#!/usr/bin/env python3
"""Emit a reproducible comparison family, before monic elimination."""
from build_pool import ROOT,build,save,analyze
import json

PARTITIONS={
 'P208':[[0,1,2],[3,4]],
 'P209':[[0],[1,2],[3,4]],
 'P210':[[0],[1],[2],[3,4]],
 'P211':[[0],[1],[2],[3],[4]],
}
def main():
    result={}
    for name,partition in PARTITIONS.items():
        data,certificate,_=build(partition)
        save(ROOT/'equations/partitions'/f'{name}.json',data)
        save(ROOT/'equations/partitions'/f'{name}_certificate.json',certificate)
        metrics=analyze(data)
        save(ROOT/'equations/partitions'/f'{name}_metrics.json',metrics)
        result[name]=metrics
    data,certificate,_=build(PARTITIONS['P210'],unweighted_groups=[[3,4]])
    save(ROOT/'equations/partitions/P210_consecutive.json',data)
    save(ROOT/'equations/partitions/P210_consecutive_certificate.json',certificate)
    result['P210_consecutive']=analyze(data)
    save(ROOT/'equations/partitions/P210_consecutive_metrics.json',result['P210_consecutive'])
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
