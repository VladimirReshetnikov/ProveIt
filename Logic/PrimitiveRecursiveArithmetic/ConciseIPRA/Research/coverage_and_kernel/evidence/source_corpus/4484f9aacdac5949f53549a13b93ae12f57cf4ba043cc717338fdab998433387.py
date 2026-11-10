"""Count inference nodes in the delivered ordinary JSON proof trees."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def nodes(value):
    if isinstance(value, dict):
        return int('rule' in value) + sum(nodes(child) for child in value.values())
    if isinstance(value, list):
        return sum(nodes(child) for child in value)
    return 0


def main():
    rows = json.loads((ROOT / 'cases.json').read_text())
    counted = {row['name']: nodes(json.loads((ROOT / row['file']).read_text())['proof'])
               for row in rows if row['expected']}
    selected = ('derived_successor_congruence', 'derived_seed_congruence_with_parameter',
                'derived_update_congruence_with_parameters')
    if any(counted[name] != 57 for name in selected):
        raise SystemExit('Unexpected numerical congruence proof shape')
    if counted['reflexivity_symbolic'] != 3:
        raise SystemExit('Unexpected reflexivity proof shape')
    (ROOT / 'node_counts.json').write_text(json.dumps(counted, indent=2) + '\n')
    print(json.dumps(counted, indent=2))


if __name__ == '__main__':
    main()
