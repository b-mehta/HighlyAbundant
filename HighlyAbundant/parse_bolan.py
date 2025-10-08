import math
from collections import Counter

def floor_log(n, b):
    res = math.floor(math.log(n, b))
    return res + 1 if b**(res+1) <= n else res - 1 if b**res > n else res

all_primes = set()

ladder = []

with open("HighlyAbundant/bolanLadder.txt", "r") as file:
    lines = file.readlines()
    for i in lines:
        a, b, c = i.split(";")
        [l, u] = eval(a)

        if l <= 257:
            continue

        adds = Counter(eval(b))
        subs = Counter(eval(c))

        ladder.append((l, u, subs, adds))

for (i, (l, u, subs, adds)) in enumerate(ladder[:100]):
    bad = []
    for (p, k) in adds.items():
        if p > u: continue
        inc = floor_log(l, p)
        inc2 = floor_log(u, p)
        if inc != inc2:
            if ladder[i+1][0] <= p ** inc2 + 1:
                pass
            else:
                bad.append(p)
        # adds[p] += inc
        # subs[p] += inc

    print(l, u)
    if len(bad) > 1:
        print(bad)
    adds = sorted(adds.items())
    subs = sorted(subs.items())

#     print(f"""\
# lemma not_HA_block_{l} : ∀ i ∈ Finset.Icc {l} {u}, ¬ IsHighlyAbundant (lcmRange i) :=
#   prove_not_HA'
#     {subs}
#     {adds}
# """)



