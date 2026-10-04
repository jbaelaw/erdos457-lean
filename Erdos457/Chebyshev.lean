module

public import Mathlib

/-!
# Chebyshev's elementary bound `liminf θ(x)/x ≤ 1`

For every `δ > 0` we have `θ(n) ≤ (1 + δ) n` for infinitely many `n`.  The proof uses only
Legendre's formula and Chebyshev's bound `θ(x) ≤ x log 4`:

* `sum_log_div_le` (Mertens' upper bound): `S(N) = Σ_{p ≤ N} log p / p ≤ log N + log 4`;
* partial summation: `S(N+1) - θ(N+1)/(N+1) = S(N) - θ(N)/N + θ(N)/(N(N+1))`;
* if `θ(n) > (1 + δ) n` for all large `n`, then `S(N) ≥ (1 + δ) log N - O(1)`, a contradiction.

This is the only arithmetic input of the main theorem besides Chebyshev's upper bounds.
-/

@[expose] public section

open Finset Real Filter
open scoped Chebyshev Nat
open Nat (primesLE)

namespace Erdos457

/-- `S(N) = Σ_{p ≤ N} log p / p`. -/
noncomputable def S (N : ℕ) : ℝ := ∑ p ∈ primesLE N, Real.log p / p

/-- Legendre: `⌊n/p⌋ ≤ ν_p(n!)`. -/
theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n !).factorization p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp,
    padicValNat_factorial (b := n + 1) (Nat.lt_succ_of_le (Nat.log_le_self p n))]
  have h1 : (1 : ℕ) ∈ Finset.Ico 1 (n + 1) := Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
  have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
  simpa using this

/-- `Σ_{p ≤ n} ⌊n/p⌋ log p ≤ log n!`. -/
theorem sum_div_mul_log_le (n : ℕ) :
    ∑ p ∈ primesLE n, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n ! : ℕ) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  calc ∑ p ∈ primesLE n, ((n / p : ℕ) : ℝ) * Real.log p
      ≤ ∑ p ∈ primesLE n, ((n !).factorization p : ℝ) * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg p)
        exact_mod_cast div_le_factorization_factorial (Nat.prime_of_mem_primesLE hp) n
    _ ≤ ∑ p ∈ (n !).primeFactors, ((n !).factorization p : ℝ) * Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have hpp := Nat.prime_of_mem_primesLE hp
          rw [Nat.mem_primeFactors]
          exact ⟨hpp, (Nat.Prime.dvd_factorial hpp).2 (Nat.mem_primesLE.1 hp).1,
            Nat.factorial_ne_zero n⟩
        · intro p _ _
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

/-- Mertens' upper bound: `Σ_{p ≤ N} log p / p ≤ log N + log 4`. -/
theorem sum_log_div_le {N : ℕ} (hN : 1 ≤ N) : S N ≤ Real.log N + Real.log 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) * S N ≤ ∑ p ∈ primesLE N, (((N / p : ℕ) : ℝ) + 1) * Real.log p := by
    rw [S, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
    have hfl : (N : ℝ) / p ≤ ((N / p : ℕ) : ℝ) + 1 := by
      rw [← Nat.floor_div_eq_div (K := ℝ)]
      exact (Nat.lt_floor_add_one _).le
    calc (N : ℝ) * (Real.log p / p) = (N : ℝ) / p * Real.log p := by ring
      _ ≤ (((N / p : ℕ) : ℝ) + 1) * Real.log p :=
        mul_le_mul_of_nonneg_right hfl (Real.log_natCast_nonneg p)
  have h2 : ∑ p ∈ primesLE N, (((N / p : ℕ) : ℝ) + 1) * Real.log p =
      ∑ p ∈ primesLE N, ((N / p : ℕ) : ℝ) * Real.log p + θ (N : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have h3 : Real.log (N ! : ℕ) ≤ N * Real.log N := by
    have hf : ((N ! : ℕ) : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
    calc Real.log (N ! : ℕ) ≤ Real.log ((N : ℝ) ^ N) :=
          Real.log_le_log (by exact_mod_cast Nat.factorial_pos N) hf
      _ = N * Real.log N := Real.log_pow N _
  have h4 := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) hN0.le
  have h5 := sum_div_mul_log_le N
  have : (N : ℝ) * S N ≤ N * (Real.log N + Real.log 4) := by
    rw [h2] at h1
    nlinarith
  exact le_of_mul_le_mul_left this hN0

/-- `U(N) = S(N) - θ(N)/N`. -/
noncomputable def U (N : ℕ) : ℝ := S N - θ (N : ℝ) / N

theorem S_succ (N : ℕ) :
    S (N + 1) = S N + (θ ((N + 1 : ℕ) : ℝ) - θ (N : ℝ)) / (N + 1 : ℕ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log, S, S,
    Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert (Nat.notMem_primesLE N), Finset.sum_insert (Nat.notMem_primesLE N)]
    ring
  · simp

/-- Partial summation: `U(N+1) = U(N) + θ(N)/(N(N+1))` for `N ≥ 1`. -/
theorem U_succ {N : ℕ} (hN : 1 ≤ N) :
    U (N + 1) = U N + θ (N : ℝ) / (N * (N + 1)) := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  rw [U, U, S_succ]
  push_cast
  field_simp
  ring

/-- **Chebyshev.**  For every `δ > 0`, `θ(n) ≤ (1 + δ) n` for infinitely many `n`. -/
theorem frequently_theta_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ᶠ n : ℕ in atTop, θ (n : ℝ) ≤ (1 + δ) * n := by
  rw [Filter.frequently_atTop]
  intro n₀
  by_contra! h
  set m := n₀ + 1 with hm
  -- `U` grows like `(1 + δ) log N`
  have key : ∀ N : ℕ, m ≤ N →
      U m + (1 + δ) * (Real.log (N + 1) - Real.log (m + 1)) ≤ U N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
      have hN1 : 1 ≤ N := by omega
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
      have hθ : (1 + δ) * N < θ (N : ℝ) := h N (by omega)
      have hstep : (1 + δ) / (N + 1) ≤ θ (N : ℝ) / (N * (N + 1)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hlog : Real.log ((N : ℝ) + 1 + 1) - Real.log (N + 1) ≤ 1 / (N + 1) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have := Real.log_le_sub_one_of_pos (x := ((N : ℝ) + 1 + 1) / (N + 1)) (by positivity)
        have he : ((N : ℝ) + 1 + 1) / (N + 1) - 1 = 1 / (N + 1) := by
          field_simp
          ring
        linarith
      rw [U_succ hN1]
      push_cast
      have h1 : (1 + δ) * (Real.log ((N : ℝ) + 1 + 1) - Real.log (N + 1)) ≤
          (1 + δ) / (N + 1) := by
        calc (1 + δ) * (Real.log ((N : ℝ) + 1 + 1) - Real.log (N + 1))
            ≤ (1 + δ) * (1 / (N + 1)) := mul_le_mul_of_nonneg_left hlog (by linarith)
          _ = (1 + δ) / (N + 1) := by ring
      nlinarith
  -- `S(N) ≥ U(N)` and Mertens
  set C : ℝ := Real.log 4 + (1 + δ) * Real.log ((m : ℝ) + 1) - U m with hC
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN1, hN2⟩ :=
    ((hlogN.eventually_gt_atTop (C / δ)).and (eventually_ge_atTop m)).exists
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hk := key N hN2
  have hSU : U N ≤ S N := by
    have : 0 ≤ θ (N : ℝ) / N := div_nonneg (Chebyshev.theta_nonneg _) hNpos.le
    rw [U]
    linarith
  have hS := sum_log_div_le (N := N) (by omega)
  have hlogle : Real.log N ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hNpos (by linarith)
  have hCδ : C < δ * Real.log N := by
    rw [div_lt_iff₀ hδ] at hN1
    linarith
  nlinarith

end Erdos457
