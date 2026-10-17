#!/usr/bin/env python3
"""Standalone polynomial arithmetic over GF(2), no Lean or sympy required."""
import argparse
import json
from pathlib import Path

F = (1<<61) | (1<<45) | (1<<32) | (1<<2) | 1
MASK=(1<<61)-1
TAP=(1<<45)|(1<<32)|(1<<2)|1
PAIRS=[(301682885,848144186),(452471585,1293170928),(603365770,1696288372)]

def reduce_poly(n):
    while n.bit_length()>61:
        n ^= F << (n.bit_length()-62)
    return n

def mul(a,b):
    p=0
    while b:
        if b&1: p ^= a
        a<<=1
        b>>=1
    return reduce_poly(p)

def powx(n):
    result,base=1,2
    while n:
        if n&1: result=mul(result,base)
        base=mul(base,base)
        n>>=1
    return result

def mulX(s):
    return ((s<<1)&MASK) ^ (TAP if s>>60 else 0)

def check_pair(a,b):
    assert 0<a<b<=1<<31
    x=powx(a)
    y=powx(b)
    assert x^y==1, (a,b,hex(x),hex(y))
    return x,y

def test_small(bmax=3000):
    s=1
    seen={}
    solutions=[]
    for b in range(1,bmax+1):
        s=mulX(s)
        assert s==powx(b)
        if (s^1) in seen and seen[s^1]<b:
            solutions.append((seen[s^1],b))
        seen[s]=b
    return solutions

if __name__ == '__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--summary',type=Path)
    ap.add_argument('--small-test',type=int,default=3000)
    args=ap.parse_args()
    for a,b in PAIRS:
        x,y=check_pair(a,b)
        print(f'PASS {a=} {b=} remainders={x:#x} and {y:#x}')
    sol=test_small(args.small_test)
    print(f'PASS independent LFSR against polynomial remainders through exponent {args.small_test}; hits={sol}')
    if args.summary:
        d=json.loads(args.summary.read_text())
        assert d['generated_count']==d['inclusive_bound']
        assert sum(d['partition_counts'])==d['inclusive_bound']
        assert len(d['partition_counts'])==256
        assert len(d['pairs'])==d['collision_key_count']
        for a,b in d['pairs']: check_pair(a,b)
        print('PASS summary consistency and every candidate')
