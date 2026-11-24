"""Exact upper bounds under the counterfactual r <= 20; no orbit search.
Run: python3 cycle-certificate.py  (no dependencies, no floating point).
See the accompanying cycle-rank.pdf for the definitions and proof.
"""
from fractions import Fraction as F
from math import prod

P = (5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79)
Q = 2**71

def last_true(test):  # monotone, true at zero
    lo, hi = 0, 1
    while test(hi): hi *= 2
    while hi-lo > 1:
        mid = (lo+hi)//2
        if test(mid): lo = mid
        else: hi = mid
    return lo

# Five-state budget with the least mod-3 pivot unweighted; s=3/8.
assert (3*Q+1)**5 < 2**8 * Q**5 and (3*Q+1)*100 < 2*151*Q
T = 10000
K = [last_true(lambda k: k**8 <= T**8*p**3) for p in P[1:]]
U = (10**100 * prod(P[1:])**15 * 7**27
     * prod(((3**d-2**d)*F(151,100)**(d-1))**(15*(5-d)) for d in (3,4))
     * prod((1+F(4*T,k))**100 for k in K))
cap = 3_140_000_000_000
assert U < cap**100   # n^100 <= U

# Distinct projected divisors. c[s] counts exponent tuples of rounded cost s.
x = F(33,32)
w = [last_true(lambda k: x**k <= p) for p in P]
L = last_true(lambda k: x**k <= Q)
c = [1]+[0]*L
for k in w:
    for j in range(k,L+1): c[j] += c[j-k]
# Horner numerator for sum_{j<=L} c[j]*(32/33)^j over common denom 33^L.
z, power = 0, 1
for ci in reversed(c):
    z = z*32 + ci*power
    power *= 33
S = F(sum(c),Q) + prod(1/(1-x**(-k)) for k in w) - F(z,33**L)

# Rational intervals for log(a) via t=(a-1)/(a+1), atanh series.
def logs(t):
    K = 64
    lo = 2*sum(t**(2*i+1)/(2*i+1) for i in range(K))
    return lo, lo + 2*t**(2*K+1)/((2*K+1)*(1-t*t))
lo2, hi2 = logs(F(1,3))
lo3, hi3 = logs(F(1,2))
eta = F(7,10**13)
assert 0 < S < 3*lo2*eta  # 0 < E-n*log_2(3) < eta

# Columns (a,b) below slope theta, (u,v) above; unit determinant.
a,b = 1_193_652_440_098, 753_110_839_881
u,v = 3_798_934_114_911, 2_396_860_564_955
assert b*u-a*v == 1 and b+v > cap
assert a < b*lo3/hi2 and u-v*hi3/lo2 > eta
print('rank<=20: n <',cap,'and 0 < E - n*log_2(3) < 7e-13; incompatible.')
