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

        if l == 256:
            continue

        muls = eval(b)
        divs = eval(c)

        mulsl = []
        for (p, k) in sorted(muls.items()):
            i = floor_log(u, p)
            mulsl.append((p, k, i))
        divsl = sorted([i for i,j in divs.items()])

        ladder.append((l, u, muls, divs))

        print(f"""\
def data_{l} : ProofData where
  lo := {l}
  hi := {u}
  muls := {mulsl}
  divs := {divsl}

theorem not_HA_block_{l} :
  ∀ i ∈ Finset.Icc {l} {u}, ¬ IsHighlyAbundant (lcmRange i) := data_{l}.not_HA'
        """)




# def data_727 : ProofData where
#   lo := 727
#   hi := 786
#   muls := [(2, 1, 9), (11, 1, 2), (29, 1, 1), (787, 1, 0)]
#   divs := [691, 727]
