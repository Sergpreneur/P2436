#!/usr/bin/env python3
"""Exact Rabin and Lucas-Lehmer checks for the degree-61 primitive modulus."""
from verify_witness import F, reduce_poly, mul, powx

def gcd(a,b):
    while b:
        r=a
        db=b.bit_length()-1
        while r and r.bit_length()-1 >= db:
            r ^= b << (r.bit_length()-1-db)
        a,b=b,r
    return a

def run():
    q=2
    for _ in range(61):
        q=mul(q,q)
    assert q == 2, f'Frobenius mismatch: {q:#x}'
    assert gcd(F, 0b110) == 1, 'gcd(f,x^2+x) != 1'
    # A polynomial of prime degree 61 is irreducible if these two tests hold.
    n=(1<<61)-1
    s=4
    for i in range(59):
        s=(s*s-2)%n
    assert s==0, 'Lucas-Lehmer residue is nonzero'
    assert powx(n)==1
    print('PASS: Rabin prime-degree irreducibility test')
    print('PASS: Lucas-Lehmer for Mersenne prime 2^61-1')
    print('PASS: multiplicative order of x modulo f is 2^61-1')

if __name__ == '__main__':run()
