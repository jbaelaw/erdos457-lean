module

public import Erdos684Lean.Asymptotics

/-!
# Counting the primes in `(M, K]`

`#{M < p ≤ K} ≤ θ(K) / log M`.
-/

@[expose] public section

open Finset Real Filter Topology
open scoped Chebyshev
open Nat (primesLE)

namespace Erdos684

variable (P : Params)

/-- Chebyshev's bound `θ(x) ≤ x log 4` (Mathlib), in the form `#{M < p ≤ K} ≤ θ(K)/log M`. -/
theorem card_PMK_le (M : ℕ) (hM : 1 < M) :
    ((PMK P M).card : ℝ) ≤ θ (Kof P M) / Real.log M := by
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast hM)
  rw [le_div_iff₀ hlogM, Chebyshev.theta_eq_sum_primesLE_log]
  have h1 : (PMK P M).card • Real.log M ≤ ∑ p ∈ PMK P M, Real.log p := by
    apply Finset.card_nsmul_le_sum
    intro p hp
    simp only [PMK, Finset.mem_filter] at hp
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) (by exact_mod_cast hp.2.le)
  rw [nsmul_eq_mul] at h1
  refine h1.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p hp _
  exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)

end Erdos684
