"""Repeat the original-standard Euler audit with rank-reduced LPs and replay caches.

The retained prior audit is unchanged. This wrapper uses the same independent
finite oracle and diagram cases, but pins the current basis/replay package.
"""
from unittest.mock import patch
from euler_tree_research import audit
from .replay_benchmark import source_hashes


def main():
    with patch.object(audit, 'source_hashes', source_hashes):
        audit.main()


if __name__ == '__main__':
    main()
