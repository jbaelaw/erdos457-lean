module

public import Mathlib

/-!
# Definitions shared with the Erdős 684 development

The parameters and scales of the product-cell code (J. H. Bae, arXiv:2604.23784):

* `Params` — the parameter `c > 0`;
* the scales `A = c log M / log log M`, `K = ⌊A M⌋`, `h = ⌊M / (20 log A)⌋`, `L = lcm(1..M)`;
* the integers `n_t = t L - h - 1`;
* the product-cell code `j ↦ (⌊[jL]_p / h⌋)_{M < p ≤ K}` and its codeword count `CM`.
-/

@[expose] public section

open Finset Real Filter Topology
open scoped Chebyshev
open Nat (primesLE)

namespace Erdos684

/-! ## Parameters and scales -/

/-- The parameter of the scales: a positive real `c` (the constant in `A = c log M / log log M`). -/
structure Params where
  c : ℝ
  c_pos : 0 < c

variable (P : Params)

/-- `A = c log M / log log M` — paper (13). -/
noncomputable def A (M : ℕ) : ℝ := P.c * Real.log M / Real.log (Real.log M)

/-- `K = ⌊A M⌋` — paper (13). -/
noncomputable def Kof (M : ℕ) : ℕ := ⌊A P M * M⌋₊

/-- `h = ⌊M / (20 log A)⌋` — paper (13). -/
noncomputable def hof (M : ℕ) : ℕ := ⌊(M : ℝ) / (20 * Real.log (A P M))⌋₊

/-- `L = lcm(1, …, M)` — paper (13). -/
def Lof (M : ℕ) : ℕ := Nat.lcmUpto M

/-- `n_t = tL - h - 1` — paper (22). -/
noncomputable def nOf (M t : ℕ) : ℕ := t * Lof M - hof P M - 1

/-- The primes in `(M, K]`. -/
noncomputable def PMK (M : ℕ) : Finset ℕ := (primesLE (Kof P M)).filter (fun p => M < p)

/-! ## The product-cell code -/

/-- The product-cell code — paper (15): `j ↦ (⌊[jL]_p / h⌋)_{M < p ≤ K}`. -/
noncomputable def code (M j : ℕ) : PMK P M → ℕ := fun p => (j * Lof M % (p : ℕ)) / hof P M

/-- The finite set of possible codewords. -/
noncomputable def codeSet (M : ℕ) : Finset (PMK P M → ℕ) :=
  Fintype.piFinset (fun p : PMK P M => range ((p : ℕ) / hof P M + 1))

/-- `C_M = ∏_{M<p≤K} (⌊p/h⌋ + 1) ≥ ∏ ⌈p/h⌉` — paper (16). -/
noncomputable def CM (M : ℕ) : ℕ := ∏ p ∈ PMK P M, (p / hof P M + 1)

end Erdos684
