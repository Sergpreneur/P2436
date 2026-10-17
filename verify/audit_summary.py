#!/usr/bin/env python3
"""Audits the *recorded* run summary, NOT a substitute for rerunning source."""
import json
import sys
from pathlib import Path
from verify_witness import check_pair, PAIRS

def audit(path):
    d = json.loads(Path(path).read_text())
    B=1<<31
    assert d['inclusive_bound']==B, 'wrong inclusive bound'
    assert d['generated_count']==B, 'wrong generation count'
    assert d['partition_count']==256
    assert len(d['partition_counts'])==256
    assert all(n>0 for n in d['partition_counts'])
    assert sum(d['partition_counts'])==B
    assert d['collision_key_count']==3
    assert len(d['collision_keys'])==3
    assert len(set(d['collision_keys']))==3
    assert len(d['pairs'])==3
    pairs=[tuple(p) for p in d['pairs']]
    assert pairs==sorted(pairs,key=lambda p:p[1])
    assert pairs==PAIRS
    for a,b in pairs:check_pair(a,b)
    print('PASS: full-range metadata and three exact witnesses')
    print('NOTE: audit_summary.py checks metadata only; rerun C++ to re-establish completeness.')

if __name__=='__main__':
    audit(sys.argv[1] if len(sys.argv)>1 else 'results/full_run_summary.json')
