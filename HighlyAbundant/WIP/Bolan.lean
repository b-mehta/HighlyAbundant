import HighlyAbundant.Basic

-- small progress towards Bolan's approach to showing the conjecture holds at certain places
section bolan

def score (num denom m : ℕ) : ℚ := (σ₁ m) ^ num / m ^ denom
def score_calc (num denom p k : ℕ) : ℚ :=
  (p ^ (k + 1) - 1) ^ num / ((p - 1) ^ num * p ^ (denom * k))

lemma score_prime_pow (num denom p k : ℕ) (hp : p.Prime) :
    score num denom (p ^ k) = score_calc num denom p k := by
  have : 2 ≤ p := hp.two_le
  rw [score, sigma_one_apply_prime_pow' hp, score_calc,
    Nat.cast_div (Nat.sub_one_dvd_pow_sub_one _ _), Nat.cast_sub, Nat.cast_sub (by cutsat),
    Nat.cast_one, div_pow, div_div, Nat.cast_pow, Nat.cast_pow, pow_mul']
  · apply Nat.pow_pos
    grind
  · simp only [ne_eq, Rat.natCast_eq_zero]
    cutsat

-- this is a more restricted list than on MO, it's generated instead by running his code
def ranges : List (ℕ × (ℕ × ℕ)) :=
  [(2, (5, 10)), (3, (3, 6)), (5, (2, 4)), (7, (2, 3)), (11, (1, 2)), (13, (1, 2)),
   (17, (1, 1)), (19, (1, 1)), (23, (1, 1)), (29, (1, 1)), (31, (1, 1)), (37, (1, 1)),
   (41, (1, 1)), (43, (1, 1)), (47, (0, 1)), (53, (0, 1)), (59, (0, 1)), (61, (0, 1)),
   (67, (0, 1)), (71, (0, 1)), (73, (0, 1)), (79, (0, 1)), (83, (0, 1)), (89, (0, 1))]

-- compute the list of primes which fall in the given ranges, up to a maximum
-- this evaluates reasonably fast, but reduces too slow to be useful without further optimisation
def takePrimes (max : ℕ) : List (ℕ × (ℕ × ℕ)) → List ℕ
  | [] => [1]
  | (p, l, u) :: xs => do
    let t ← takePrimes max xs
    let i ← (List.range' l (u - l + 1)).reverse
    let n := p ^ i * t
    if n ≤ max then return n else failure

end bolan
