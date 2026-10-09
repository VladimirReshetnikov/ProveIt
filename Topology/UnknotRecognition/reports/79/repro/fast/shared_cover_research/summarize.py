"""Derive the compact benchmark table from the retained paired raw results."""
import json
from pathlib import Path


def summarize(directory):
    records = []
    for name, kind in (('exhaustion', 'exhaustion'), ('descent', 'first_descent')):
        data = json.loads((directory/(name+'.json')).read_text())
        for case in data['cases']:
            old, new = case['restart_stats'], case['shared_stats']
            times = case['median_seconds'][kind]
            records.append(dict(experiment=kind, tetrahedra=case['tetrahedra'],
                gadgets=case['gadget_count'], cover_regions=new['regions_indexed'],
                restart_frames=old['nodes'], shared_frames=new['nodes'],
                restart_work=old['work'], shared_work=new['work'],
                restart_seconds=times['restart'], shared_seconds=times['shared'],
                median_speed_ratio=times['restart']/times['shared'],
                geometric_endpoints=case['geometric_endpoint_count']))
    return dict(source_files=['exhaustion.json', 'descent.json'], repeats=3, records=records)


if __name__ == '__main__':
    directory = Path(__file__).resolve().parent/'results'
    destination = directory/'summary.json'
    destination.write_text(json.dumps(summarize(directory), indent=2)+'\n')
    print(destination)
