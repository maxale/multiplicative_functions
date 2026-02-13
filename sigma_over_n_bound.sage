############################################## Bounding sigma(x)/x using Robin's theorem

'''
Since function robin_bound(x) is nondecreasing,
if sigma(x)/x > robin_bound(U), then x > U.
'''


def robin_bound(n):
    '''
    Nondecreasing upper bound for sigma(x)/x per https://mathworld.wolfram.com/RobinsTheorem.html
    '''
    if n<1: return 0

    # Note that max(sigma(x)/x for x in (1..5600)) = 403/105 < 3.8381 < robin_bound(5601)
    if n<=5600: return 3.8381 
    # return (exp(euler_gamma)*log(log(n))).n() 
    return 1.781072418*log(log(RDF(n)))          # exp(euler_gamma) < 1.781072418


############################################## Bounding using A023199

'''
* A023199 = a(n) is the least k with sigma(k) >= n*k.
Typically we want to say that if sigma(x)/x is large, then so is x.
Namely, if sigma(x)/x >= n, then x >= A023199_term[n].

A023199_term = [-1, 1, 6, 120, 27720, 122522400, 130429015516800, 1970992304700453905270400, 1897544233056092162003806758651798777216000, 4368924363354820808981210203132513655327781713900627249499856876120704000]

This works only for integer n, and so is retired in favor of robin_bound().
'''


######################################################################## Bounding tau(n)

'''
Q1: Suppose that n <= U, what is upper bound for tau(n)?
Q2: Suppose tau(n) is given what is lower bound for bigomega(n)?

A1: Find the smallest term t >= n in
    A002182 Highly composite numbers: numbers n where d(n), the number of divisors of n (A000005), increases to a record.
then tau(n) <= tau(t).

A2: tau(n) = p1^e1 ... pk^ek, then bigomega(n) >= e1*(p1-1) + ... + ek*(pk-1).

We also need:
'''

def a005179_atmost(n,U):
    '''
    Tests if A005179(n), smallest number with exactly n divisors, is <= U.
    '''

    def mult_factors(n, sum_bound = oo, low_d = 2):
        if n==1: return [tuple()]
        c = []
        for d in divisors(n):
            if d-1 > sum_bound: break
            if d >= low_d:
                c.extend( (d, )+a for a in mult_factors(n//d, sum_bound - d + 1, d) )
        return c

    if n==1: return 1 <= U
    l2 = U.exact_log(2)
    if max(prime_factors(n))-1 > l2: return False            # shortcut
    return any( prod(nth_prime(i)**(j-1) for i, j in enumerate(reversed(d), 1)) <= U for d in mult_factors(n, l2) )
