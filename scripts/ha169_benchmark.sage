import os
import time
os.environ["SAGE_NUM_THREADS"] = '4'

print(f'Using {os.environ["SAGE_NUM_THREADS"]} threads')

proof.arithmetic(False)    # speeds up dealing with primes

from collections import deque
from sage.parallel.map_reduce import RESetParallelIterator

def min_sigma_below(sigma_L, B, just_any=False):
    '''
        Returns smallest `n` with sigma(`n`) >= `sigma_L` and `n` <= `B` if it exists; otherwise +oo.
        `just_any=True` drops minimality of `n` and aborts computation as soon as any `n` < `B` is found.
    '''

    def succ(tup):
        sigma_L, num, minp = tup      # note that minp is prime
        children = []
        if sigma_L == 1: return children

        # for n >= sigma_L-1 > 1, we have sigma(n) >= sigma_L, but n cannot have prime divisors less than minp
        m = B//num
        if sigma_L - 1 < m:
            m_ = next_prime(sigma_L-2) if sigma_L - 1 > minp else minp
            if num*m_ < B:
                if just_any: return [(1, num*m_, minp)]            # num*m_ < B is any solution we look for
                m = m_

        # we have sigma_L/m <= sigma(n)/n <= n/phi(n) = prod_{p|n} p/(p-1).
        P = deque([minp])      # P is a wheel of consecutive primes

        prod_P = P[0]
        prod_pp1 = P[0]/(P[0]-1)
        s_over_n_L = sigma_L / m

        while True:
            # rolling the wheel
            while not P or prod_pp1 < s_over_n_L:
                P.append( next_prime(P[-1] if P else p) )
                prod_P *= P[-1]
                if prod_P > m: return children
                prod_pp1 *= P[-1]/(P[-1]-1)

            p = P.popleft()
            prod_pp1 /= p/(p-1)
            prod_P //= p

            p_ = P[0] if P else next_prime(p)

            for k in range(1, floor(log(m,p))+1):
                spk = (p^(k+1) - 1) // (p - 1)          # = sigma(p^k)
                children.append( (ceil(sigma_L/spk), num*p^k, p_) )
                if spk >= sigma_L: break

    res = RecursivelyEnumeratedSet(seeds=[(sigma_L, 1, 2)], successors=succ, structure='forest', post_process=lambda tup: tup[1] if tup[0]==1 else None)

    if just_any:
        m = oo
        it = RESetParallelIterator(forest = res)
        for m in it:
            if m < B:
                it.abort()
                it.finish()
                break
        return m

    return res.map_reduce(lambda t: t, min, oo)


def is_highly_abundant(L):
    m = min_sigma_below(sigma(L), L, just_any=True)
    if m < L:
        print('Witness:', factor(m))
    return m == L

start_time = time.time()
print("started at", start_time)
print( 'L169 is HA:', is_highly_abundant(lcm(1..169)) )
end_time = time.time()
print("ended at", end_time)

print("done")
print(end_time - start_time)
