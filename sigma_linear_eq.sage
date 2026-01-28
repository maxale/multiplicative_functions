__version__ = 20260127

__doc__ = f'''
Solve linear equations in sigma(n) and n.
Version {__version__} by Max Alekseyev <maxal@gwu.edu>

Implementation of the algorithm proposed in the paper:
* M. A. Alekseyev. "Computing bounded solutions to linear Diophantine equations with the sum of divisors", 2026.
  arXiv:2601.17832 [math.NT] https://arxiv.org/abs/2601.17832

Brief history:
* 20260127: Minor bugfix; OEIS A391617 (abundance=54) included in the references
* 20260124: First public release
'''

print(f'sigma_linear_eq.sage ver. {__version__}\n\tSage ver. {sage.version.version}')

load('par_setup.sage')
# for robin_bound()
load('sigma_over_n_bound.sage')

import itertools
import functools
import time
from collections import deque

proof.arithmetic(False)

# to support case b=0; https://raw.githubusercontent.com/maxale/gpscripts/refs/heads/main/invphi.gp
gp.read("invphi.gp")

####################################### Reference sequences

refs_ac = {         # any b
    (1, 2): 'A045768',
    (1, -2): 'A056006',
    (1, 4): 'A045769',
    (1, 6): 'A088834',
    (1, 8): 'A045770',
    #    (1, 12): 'A076496',   # excluded since OEIS is flooded with small terms
}

refs_a1b2 = {           # a=1, b=2
    -2: 'A191363',
    2: 'A088831',
    4: 'A088832',
    -4: 'A125246',
    -6: 'A141548',
    6: 'A087167',
    -8: 'A125247',
    8: 'A088833',
    -10: 'A101223',
    10: 'A223609',
    -12: 'A141549',
    # 12: 'A141545',    # excluded since OEIS is flooded with small terms
    14: 'A141546',
    -14: 'A141550',
    16: 'A141547',
    -16: 'A125248',
    -18: 'A223608',
    18: 'A223610',
    -20: 'A223607',
    20: 'A223611',
    22: 'A223612',
    -22: 'A223606',
    24: 'A223613',
    -24: 'A385255',
    26: 'A275701',
    -26: 'A275702',
    -28: 'A392382',
    28: 'A392383',
    -30: 'A389700',
    30: 'A389701',
    32: 'A175989',
    -32: 'A387352',
    -42: 'A175730',
    54: 'A391617',
    -54: 'A101259',
    64: 'A275996',
    -64: 'A275997',
    -90: 'A389702',
    90: 'A389703',
    128: 'A292626',
}

refs_a1_ratio_cb = {    # a=1, key = c/b
    -1: 'A055708',
    -2: 'A298563',
    2: 'A067702',
    3: 'A274551',
    -3: 'A274552',
    4: 'A274553',
    -4: 'A274554',
    -5: 'A274556',
    6: 'A274557',
    -6: 'A274558',
    7: 'A274559',
    -7: 'A274560',
    8: 'A274561',
    -8: 'A274562',
    9: 'A274563',
    -9: 'A274564',
    10: 'A274565',
    -10: 'A274566',
}

################################################### Main function res_solve_sigma_abc()

def res_solve_sigma_abc(a, b, c, U, refs=True, strict=True, squarefree=False, 
                    coprime_to=1, even_only=False,  seeds=None, seeds_only=False, 
                    omega=None, bigomega=None, numdiv=0, f_proc=lambda x: [x], verbose=1):
    '''
    Solve `a`*sigma(n) = `b`*n + `c` for positive integers `n` <= `U`.
    * `refs=True' recognizes and refers to other sequences in OEIS; `refs='Axxxxxx'` refers to any but Axxxxxx sequence;
    * 'strict=False' allows to return solutions above `U` when such are found
    * 'squarefree=True' solves in squarefree numbers only
    * 'coprime_to=m' compute only solutions coprime to m
    * 'even_only=True' compute only even solutions
    * `seeds=` if specified, uses them instead of computing seeds
    * `seeds_only=True` - returns seeds rather than solutions
    * 'omega=w' or `omega=(w_L, w_U)` compute only solutions with omega(n) = w or w_L <= omega(n) <= w_U
    * 'bigomega=W' or `bigomega=(W_L, W_U)` compute only solutions with bigomega(n) = W or W_L <= bigomega(n) <= W_U
    * `numdiv=` restricts solutions to have `numdiv` divisors; extraneous solutions may still be reported (to be fixed in proc())
    * `f_proc=` solution processing function, which returns an iterable over processed solutions ([] if there are none)
    * `verbose=` 0, 1, or 2 - verbosity level
    '''


    def reduce_abc(t, initial=False):          # also depends on U
        a, b, c, M, mp, aux = t 

        aux = dict(aux)                         # making aux independent of the input 
        omg_lb, omg_ub = aux.get('omega',(0,oo))
        Omg_lb, Omg_ub = aux.get('bigomega',(0,oo))
        omg_ub = min(omg_ub, Omg_ub)
        Omg_lb = max(Omg_lb, omg_lb)

        while True:
            g = gcd(a,c)
            h = gcd(b,g)
            a//=h; b//=h; c//=h; g//=h

            #print('Current:', (a,b,c,M), g)

            if g==1:
                break

            # g must divide n
            if gcd(M,g)>1:
                return None
            f = factor(g)
            if (squarefree and max(k for _,k in f)>1) or min(p for p,_ in f)<mp:
                return None

            if squarefree:
                a //= g
                a *= sigma(g)
                c //= g
                M *= g
                #print('Updated:', (a,b,c,M))
                if 'omega' in aux:
                    aux['omega'] = (omg_lb - len(f), omg_ub - len(f))
                if 'bigomega' in aux:
                    aux['omega'] = (Omg_lb - len(f), Omg_ub - len(f))
            else:
                # if g is not unitary, we cannot do much
                break

        # for prime p, a*sigma(p) - b*p - c = (a-b)*p + (a-c)
        if a==b==c:
            if (Omg_lb <= 1 <= omg_ub):
                print(f'WARNING: {t} is skipped; solutions are given by {str(M)+" * " if M>1 else ""}p for any prime p{" > "+str(mp-1) if mp>2 else ""}{"" if M==1 or max(prime_factors(M))<mp else " not from "+str(prime_factors(M))}.')
            return None

        # for n >= 2 and a>=b,  c = a*sigma(n) - b*n >= a*(n+1) - b*n = (a-b)*n + a >= 3*a - 2*b
        if a >= b and a!=b+c and c < 3*a-2*b:
            return None

        if refs:
            if a==1 and b==2 and refs_a1b2.get(c,refs)!=refs:
                M_ = M//coprime_to
                print(f'WARNING: {t} is skipped; solutions are given by {str(M_)+" * " if M_>1 else ""}terms of {refs_a1b2[c]}{"" if M==1 else " and coprime to "+" * ".join(map(str,prime_factors(M)))}.')
                return None
            if b!=1 and refs_ac.get((a,c),refs)!=refs:
                M_ = M//coprime_to
                print(f'WARNING: {t} is skipped; solutions are given by {str(M_)+" * " if M_>1 else ""}terms of {refs_ac[(a,c)]} with ratio {b}{"" if M==1 else " and coprime to "+" * ".join(map(str,prime_factors(M)))}.')
                return None

        if M*mp > U and a != b+c:       # when M*mp > U, the only possible solution is 1.
            return None

        if initial:
            # this may bear an unnecessary overhead, so we enable it only for initial abc
            assert a > 0    # just in case
            if c >= 0 and b/a + c/a/U  > robin_bound(U/M):
                return None
            if c < 0 and a!=b+c and b/a + c/a/mp > robin_bound(U/M):    # we admit a possibility of solution = 1
                return None

        return (a,b,c,M,mp,aux) if M <= U and gcd(a,b)==1 else None

    def succ(tup):
        # Note that here we look only for solutions with bigomega(n) >= 3 and omega(n) >= 2; the other cases are addressed in proc()

        if verbose >= 2:
            print('Succ:',tup)

        a, b, c, M, min_prime, aux = tup
        res = []

        if (a - b)*min_prime^3 >= max(0,c):       # no need to deep down
            # If a-b > 0, we have c = a*s(n) - b*n > (a - b)*n >= (a - b)*min_prime^3
            return res

        # lower and upper bounds for omega and bigomega
        omg_lb, omg_ub = aux.get('omega', (2,oo))     # we look for a solution with at least 2 primes; other cases are process in proc()
        omg_lb = max(omg_lb, 2)

        Omg_lb, Omg_ub = aux.get('bigomega', (3,oo))     # we look for a solution with at bigomega >= 3; other cases are process in proc()
        Omg_lb = max(Omg_lb, 3)

        # print('succ Omega:', Omg_lb, Omg_ub)

        numdiv_ = aux.get('numdiv',0)
        if numdiv_:
            if numdiv_ < 6 or is_pseudoprime(numdiv_):
                return res
            f = factor(numdiv_)
            Omg_lb = max(Omg_lb, sum(k*(p-1) for p,k in f))
            omg_ub = min(omg_ub, sum(k for _,k in f))

        Omg_lb = max(Omg_lb, omg_lb)
        omg_ub = min(omg_ub, Omg_ub)
        if omg_ub < omg_lb or Omg_ub < Omg_lb: return res

        UM = U//M

        aux_ = dict(aux)
        if aux:
            if 'omega' in aux_:                             # if we have bounds for omega
                aux_['omega'] = (omg_lb-1, omg_ub-1)        # successors will have cofactors with omega decreased by 1
            # 'bigomega' in aux_ is updated later as the prime exponent becomes known

        odd_sigma = (a%2 and (b+c)%2) or numdiv_%2      # True means "if n is odd, then sigma(n) is odd and n is a square"
        '''
            When odd_sigma=True, we surely have odd sigma(n) if at least one of the following conditions holds:
            * min_prime > 2; or
            * b is even; or
            * numdiv_ is odd.
            Furthermore, min_prime > 2 implies that n is an odd square.
            If min_prime = 2, n may be a square, or twice a square, or just an even non-square (when b is odd).
        '''

        if odd_sigma and min_prime>2:           # implying that n is a square
            if Omg_lb%2 or Omg_lb < omg_lb*2:
                # if n is odd, each odd prime must come in even power  ==>  bigomega(n) is even, and we can round Omg_lb up to an even number
                Omg_lb = max(Omg_lb + Omg_lb%2, omg_lb*2)
                aux_['bigomega'] = None              # just to make sure 'bigomega' is present in aux_; value will be overwritten later
            if Omg_ub < oo:
                Omg_ub -= Omg_ub%2
                if Omg_ub//2 < omg_ub:
                    omg_ub = Omg_ub//2
                    aux_['omega'] = (omg_lb-1, omg_ub-1)        # update/add 'omega' to aux_ with better bounds
            if omg_lb > omg_ub or Omg_lb > Omg_ub: return res

        g = gcd(a,c)
        if g>1 and (not odd_sigma or min_prime>2 or b%2==0 or numdiv_%2):
            # if odd_sigma=True here, then n is square or twice a square.

            if g > UM: return res

            # reduce_abc guarantees that gcd(b,g)==1, gcd(g,M) == 1, and min(prime_factors(g)) >= min_prime
            # hence, g divides a solution
            assert gcd(g,M) == 1

            G = factor(g)
            assert min(p for p,_ in G) >= min_prime

            if odd_sigma:
                # round up suitable prime exponents to even
                G *= type(G)( (p,int(e%2 and (p>2 or numdiv_%2))) for p,e in G )
                g = G.value()
                if g > UM: return res

            if omg_lb < len(G):
                omg_lb = len(G)
                if omg_lb > omg_ub: return res
                aux_['omega'] = (omg_lb-1, omg_ub-1)
                Omg_lb = max(Omg_lb, omg_lb)

            if Omg_lb < (E:=sum(e for _,e in G)):
                Omg_lb = E
                if Omg_lb > Omg_ub: return res

            p,e = max( G, key=lambda z: z[0]^z[1] )

            # Note that p is not necessarily spf(n)

            p_exp = 2 if odd_sigma and (p>2 or numdiv_%2) else 1
            p_exp_max = 1 if squarefree else (UM//g).exact_log(p)+e             #  min( (UM//g).exact_log(p)+e, Omg_ub - (omg_lb-1)*p_exp ) ????????????
            if numdiv_ and p_exp_max >= numdiv_: p_exp_max = numdiv_ - 1

            for k in range(e, p_exp_max + 1, p_exp):
                if numdiv_%(k+1): continue

                q = p^k
                s_q = (q*p-1)//(p-1)        # = sigma(q)

                if odd_sigma and any(legendre_symbol(-b*c*p^(k%2),r)==-1 for r in prime_factors(s_q)): continue

                if 'bigomega' in aux_: 
                    aux_['bigomega'] = (Omg_lb-k, Omg_ub-k)
                    #print('\t',(p,k),aux_['bigomega'])
                if numdiv_: aux_['numdiv'] = numdiv_//(k+1)
                if (z := reduce_abc( (a*s_q, b*q, c, M*q, min_prime,aux_) )) is not None:
                    res.append(z)
                    #print('\tres1:',res)
            return res


        ########################################## Prime Wheel ADDED: 20251013

        def my_prime_gen(start_p=min_prime):
            p = next_prime(start_p-1)
            while True:
                if M%p: yield p
                p = next_prime(p)

        gen_next_prime = my_prime_gen()

        # we have sigma(n)/n <= n/phi(n) = prod_{p|n} p/(p-1).

        P = deque([next(gen_next_prime)])       # P is a wheel of consecutive primes
        prod_P = P[0]
        prod_pp1 = P[0]/(P[0]-1)

        while True:

            '''
                We assume that omega(n) = len(P).
                Then 
                (i) sigma(n)/n <= Prod_{p|n} p/(p-1) <= Prod_{p in P} p/(p-1) =: prod_pp1
                (ii) prod_P * P[0]^(Omg_lb - len(P)*p_exp) <= n <= UM, we exist the loop when lhs becomes > UM
                (iii) if c >= 0, then b + c/n >= b + c/UM;
                      if c < 0, then b + c/n >= b + c/prod_P
            '''

            p_exp = 2 if odd_sigma and (P[0]>2 or numdiv_%2) else 1
            o_exp = 2 if odd_sigma and (P[0]>2 or b%2==0 or numdiv_%2) else 1     # exponents for primes P[1:]

            if p_exp==2:
                if squarefree: return res               # wheel exit
                if P[0] == 3:    # make sure the following update is done only once (for efficiency) if it was not done before due to min_prime = 2
                    if Omg_lb%2 or Omg_lb < omg_lb*2:
                        # if n is odd, each odd prime must come in even power  ==>  bigomega(n) is even, and we can round Omg_lb up to an even number
                        Omg_lb = max(Omg_lb + Omg_lb%2, omg_lb*2)
                        aux_['bigomega'] = None              # just to make sure 'bigomega' is present in aux_; value will be overwritten later
                    if Omg_ub < oo:
                        Omg_ub -= Omg_ub%2
                        if Omg_ub//2 < omg_ub:
                            omg_ub = Omg_ub//2
                            aux_['omega'] = (omg_lb-1, omg_ub-1)        # update/add 'omega' to aux_ with better bounds
                    if omg_lb > omg_ub or Omg_lb > Omg_ub: return res

            # filling P
            while len(P) < omg_lb or a * prod_pp1 <= b + (c/UM if c >= 0 else c/prod_P^o_exp/P[0]^(Omg_lb - len(P)*o_exp)):
                if len(P) >= omg_ub: return res
                if p_exp + len(P)*o_exp > Omg_ub: return res        # wheel exit
                P.append( next(gen_next_prime) )
                if len(P) > omg_lb:
                    omg_lb = len(P)
                    if omg_lb > omg_ub: return res              # wheel exit
                    Omg_lb = max(Omg_lb, p_exp + (omg_lb-1) * o_exp)
                    if Omg_lb > Omg_ub: return res              # wheel exit
                    # we add 'omega' to aux_ unconditionally here, since it may save time in proc()
                    aux_['omega'] = (omg_lb-1, omg_ub-1)
                prod_P *= P[-1]
                if prod_P^o_exp * P[0]^(Omg_lb - len(P)*o_exp) > UM: return res         # wheel exit
                prod_pp1 *= P[-1]/(P[-1]-1)

            assert len(P) == omg_lb

            p = P.popleft()             # candidate for the smallest prime

            # assert len(P) == omg_lb - 1

            prod_pp1 /= p/(p-1)
            prod_P //= p

            p_ = p^p_exp        # = p or p^2
            p_exp_max = 1 if squarefree else min( (UM//prod_P^o_exp).exact_log(p), Omg_ub - (omg_lb-1)*o_exp )
            if numdiv_ and p_exp_max >= numdiv_: p_exp_max = numdiv_ - 1

            q = 1
            for q_exp in range(p_exp, p_exp_max + 1, p_exp):
                q *= p_
                if numdiv_%(q_exp+1): continue

                s_q = (q*p-1)//(p-1)        # = sigma(q)

                # if p>2 and odd_sigma (ie. p_exp==2), then for any prime divisor r | sigma(q), kronecker(-b*c*q,r) = kronecker(-b*c,r) != -1 
                # ADDED 20250829, corrected 20251013 (p>2 was missing!)
                # if p_exp==2 and any(legendre_symbol(-b*c,r)==-1 for r in prime_factors(s_q)): continue
                # CHANGED 20250120
                if odd_sigma and (p>2 or b%2==0 or numdiv_%2) and any(legendre_symbol(-b*c*p^(q_exp%2),r)==-1 for r in prime_factors(s_q)): continue

                if 'bigomega' in aux_:
                    aux_['bigomega'] = (Omg_lb-q_exp, Omg_ub-q_exp)
                    #print('\t',(p,q_exp),aux_['bigomega'])
                if numdiv_: aux_['numdiv'] = numdiv_//(q_exp+1)
                if (z := reduce_abc( (a*s_q, b*q, c, M*q, (P[0] if P else p+1), aux_) )) is None: continue

                prod_qq1 = prod_pp1 * s_q / q
                prod_Q = prod_P^p_exp * q
                r = P[-1] if P else p
                while a * prod_qq1 <= b + (c/UM if c >= 0 else c/prod_Q):
                    r = next_prime(r)
                    prod_Q *= r^p_exp
                    if prod_Q > UM: break
                    prod_qq1 *= r/(r-1)
                else:
                    res.append(z)
                    #print('\tres2:',res)

    ##################################################################

    sol = set()

    # transforming omega and bigomega into intervals
    if omega in ZZ:     omega = (omega,)*2
    if bigomega in ZZ:  bigomega = (bigomega,)*2

    f_proc_w = lambda x: (x_ for x_ in f_proc(x) if (omega is None or omega[0] <= len(factor(x_)) <= omega[1]) and (bigomega is None or bigomega[0] <= sum(k for _,k in factor(x_)) <= bigomega[1]))

    min_prime = 2

    # make sure coprime_to is squarefree
    coprime_to = ZZ(coprime_to).radical()

    # cancel small prime factors in favor of increasing min_prime
    for p in Primes():
        if coprime_to % p: break
        coprime_to //= p
        min_prime = p+1

    if seeds is None:
        '''
        if c==0 and (not squarefree):
            raise ValueError('c=0 is not well supported; use sigma_over_n_inverse.sage instead')
        '''

        # make sure a >= 0
        if a<0:
            a,b,c = -a,-b,-c

        if not seeds_only:
            if b==0:
                if c%a==0:
                    sol.update( s for S in map(f_proc_w,gp.invsigma(c//a).sage()) for s in S )
                return sol
            if a==0:
                if c%b==0 and 0 < (s:=-c//b) <= U and (not squarefree or is_squarefree(s)) and gcd(s,coprime_to)==1:
                    sol.update( f_proc_w(s) )
                return sol
            if c==0 and a>=b:
                # we have a*sigma(n) = b*n, that is, Prod_{p^k||n} (p^(k+1)-1)/(p-1)/p^k = b/a
                if a==b: sol.update( f_proc_w(1) )
                return sol

        if coprime_to > 1:
            # since M is multiplied by coprime_to, we do so for U
            if verbose >= 1:
                print(f'Searching via multiples of {coprime_to} upto {coprime_to} * {U} = {U*coprime_to}')
            U *= coprime_to

        if verbose >= 1:
            print('===========\t',a,b,c,U)


        aux = {}
        if omega is not None: aux['omega'] = omega
        if bigomega is not None: aux['bigomega'] = bigomega
        if numdiv: aux['numdiv'] = numdiv

        seeds = []
        if even_only:
            if min_prime <= 2 and coprime_to%2:
                aux_ = dict(aux)
                if omega is not None: aux['omega'] = (omega[0]-1, omega[1]-1)
                for k in range(1, (U//coprime_to).exact_log(2) +1):
                    if numdiv%(k+1): continue
                    if bigomega is not None: aux_['bigomega'] = (bigomega[0]-k, bigomega[1]-k)
                    if numdiv: aux_['numdiv'] = numdiv//(k+1)
                    if (z:=reduce_abc( (a*(2^(k+1)-1), b*2^k, c, coprime_to*2^k, 3, aux_), initial=True )) is not None:
                        seeds.append(z)
        elif (z:=reduce_abc( (a,b,c,coprime_to,min_prime,aux), initial=True )) is not None:
            seeds.append(z)

    if seeds_only:
        return seeds

    sol.update( t for s in seeds if s[0]==s[1]+s[2] for t in f_proc_w(s[3]//coprime_to) )

    if verbose >= 1:
        if sol: print(f'Initial solutions:', sol)
        print('Seeds:',len(seeds))

    if not seeds:
        return sorted(sol)

    # we extend each node of RES with 2 primes
    RES = RecursivelyEnumeratedSet(seeds=seeds, successors=succ, structure='forest')

    # does not depend on U when strict=False
    def proc(t):
        if verbose >= 2:
            print('Node:',t,flush=True)

        a, b, c, M, min_prime, aux = t
        res = set()

        '''
        # Solution x=1 is addressed in main procedure
        if a==b+c:
            res.add(M//coprime_to)
        '''

        if min_prime > U//M: return res

        omg_lb, omg_ub = aux.get('omega',(0,oo))
        Omg_lb, Omg_ub = aux.get('bigomega',(0,oo))
        omg_ub = min(omg_ub, Omg_ub)
        Omg_lb = max(Omg_lb, omg_lb)

        #print('omega:', omg_lb, omg_ub)
        #print('Omega:', Omg_lb, Omg_ub)

        numdiv_ = aux.get('numdiv',0)

        # CASE (I): complementing with a prime power
        if not (omg_lb <= 1 <= omg_ub): pass
        elif a==c:
            # Note that a = b = c is impossible as it's addressed in reduce_abc()
            # ((a-b)*p+b)*p^(k-1) = a, which implies k > 1; also, since gcd(a,b,c)=gcd(a,b)=1, we have k_ := k-1 = valuation(a,p)
            for p,k_ in factor(a):
                k = k_ + 1
                if not (Omg_lb <= k <= Omg_ub): continue
                if p>=min_prime and M%p and ((a-b)*p+b)*p^k_ == a and (numdiv_==0 or numdiv_==k+1):               # BUG fixed 2025-05-27
                    res.update( f_proc(M//coprime_to*p^k) )
        else:
            # ((a-b)*p+b)*p^k = (p-1)*c + a, that is A*p^k = C
            for p in prime_factors(a-c):
                if p<min_prime or M%p==0: continue
                A = (a-b)*p + b
                C = (p-1)*c + a
                if A==0:
                    if C==0:
                        print(f'WARNING: Solution {M//coprime_to}*{p}^k for any k >= 1.')
                elif C and C%A==0:
                    C //= A
                    k = valuation(C,p)
                    if C == p^k and (numdiv_==0 or numdiv_==k+1) and (Omg_lb <= k <= Omg_ub):
                        res.update( f_proc(M//coprime_to*C) )
                        if verbose >= 2:
                            print(f'{t} Case I solution {p}^{valuation(C,p)} -> {M//coprime_to*C}',flush=True)

        ## CASE (II): complementing with p*q for distinct primes p,q.
        if (numdiv_ and numdiv_!=4) or not (Omg_lb <= 2 <= omg_ub):     # note that omg_lb <= Omg_lb and omg_ub <= Omg_ub
            pass        # tau(p*q) = 4 != numdiv_ ==> no solutions
        elif a==b:
            assert a==1
            # we have p+q = c-1
            if (c-1)%2:             # c-1 is odd; thus c-1 = 2 + (c-3)
                if 2>=min_prime and M%2 and is_pseudoprime(c-3) and M%(c-3):
                    res.update( f_proc(M//coprime_to*2*(c-3)) )
            else:                   # c-1 is even sum of two odd primes
                s = c-1
                B = (s-1)//2
                # We have p*(s-p) <= U//M, that is p^2 - s*p + U//M >= 0
                if strict and (D:=s^2-4*(U//M)) >= 0: B = min(B, (s-D.isqrt())//2)
                for p in prime_range( min_prime, B+1 ):
                    if M%p and M%(q:=s-p) and is_pseudoprime(q):
                        res.update( f_proc(M//coprime_to*p*q) )
                        if verbose >= 2:
                            print(f'{t} Case II solution {(p,q)} -> {M//coprime_to*p*q}', flush=True)
        else:
            # Here we solve ((b-a)p-a)*((b-a)q-a) = a*(b+c) - b*c
            A = b - a
            B = -a
            C = a*(b+c) - b*c
            if A < 0:   A,B = -A,-B

            # Here we solve (A*p + B) * (A*q + B) = C, where A > 0 and thus the l.h.s. is an increasing function for large enough p
            if C==0:
                if B%A==0 and is_pseudoprime(p:=-B//A) and M%p and p>=min_prime:
                    print(f'WARNING: Solution {M//coprime_to*p}*p for any prime p not in {prime_divisors(M*p)}.')
            elif (mAB := (A*min_prime + B < 0)) or (A*min_prime + B)^2 < C:  #or not strict:
                for d in divisors(C):
                    if d*d >= C:
                        break
                    if (d-B)%A==0 and is_pseudoprime(p:=(d-B)//A) and M%p and is_pseudoprime(q:=(C//d-B)//A) and M%q and min(p,q)>=min_prime:
                        res.update( f_proc(M//coprime_to*p*q) )
                    if mAB and (-d-B)%A==0 and is_pseudoprime(p:=(-d-B)//A) and M%p and is_pseudoprime(q:=(-C//d-B)//A) and M%q and min(p,q)>=min_prime:
                        res.update( f_proc(M//coprime_to*p*q) )

        if verbose >= 1 and res:
            print(f'Solutions for {t}:', sorted(res), flush=True)
        return res

    sol.update( RES.map_reduce(proc, set.union, set()) )

    if not strict:
        return sorted(sol)
    if verbose >= 1:
        sol_ = sorted(s for s in sol if s>U//coprime_to)
        if sol_:
            print('Some large solutions:', sol_)
    return sorted(s for s in sol if s<=U//coprime_to)
