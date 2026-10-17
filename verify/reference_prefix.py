#!/usr/bin/env python3
"""Naive exact reference prefix search for modest bounds; no false negatives."""
import argparse
from verify_witness import mulX

def reference_scan(bound):
    states={}  # exact full 61-bit keys
    s=1
    matches=[]
    for b in range(1,bound+1):
        s=mulX(s)
        a=states.get(s^1)
        if a is not None and 0<a<b:
            matches.append((a,b))
        states[s]=b
    return matches,s

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--bound',type=int,default=2000000)
    p.add_argument('--summary')
    args=p.parse_args()
    if not 2<=args.bound<=10000000:
        p.error('reference scan is RAM-intensive; restrict to <=10 million')
    sol,last=reference_scan(args.bound)
    print('bound=',args.bound,'solutions=',sol,'last_state=',last)
    if args.summary:
        import json
        d=json.load(open(args.summary))
        assert d['inclusive_bound']==args.bound
        assert d['last_state']==last
        assert [list(p) for p in sol]==d['pairs']
        print('PASS: exact independent dictionary comparison')
