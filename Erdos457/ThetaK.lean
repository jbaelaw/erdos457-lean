module

public import Erdos457.Chebyshev
public import Erdos684Lean.Asymptotics

/-!
# `θ(K) ≤ (1 + δ) K` for infinitely many scales `M`

The scale `K = ⌊A M⌋`, `A = c log M / log log M`, grows by a factor `1 + O(1/M)` from `M` to
`M + 1`.  Taking `M` maximal with `K(M) ≤ x` for the `x` of `Erdos457.frequently_theta_le`
transfers Chebyshev's bound from `x` to `K(M)`.
-/

@[expose] public section

open Finset Real Filter Topology
open scoped Chebyshev

namespace Erdos457

open Erdos684

/-- `1 < log M` for `M ≥ 3`. -/
theorem one_lt_log_of_three_le {M : ℕ} (hM : 3 ≤ M) : 1 < Real.log M := by
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith [Real.exp_one_lt_d9]

/-- `0 ≤ A(M)` for `M ≥ 3`. -/
theorem A_nonneg (P : Params) {M : ℕ} (hM : 3 ≤ M) : 0 ≤ A P M := by
  have h1 := one_lt_log_of_three_le hM
  have h2 : 0 < Real.log (Real.log M) := Real.log_pos h1
  unfold A
  have := P.c_pos
  positivity

/-- `A(M+1) ≤ A(M) (1 + 1/M)` for `M ≥ 3`. -/
theorem A_succ_le (P : Params) {M : ℕ} (hM : 3 ≤ M) : A P (M + 1) ≤ A P M * (1 + 1 / M) := by
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlogM := one_lt_log_of_three_le hM
  have hll : 0 < Real.log (Real.log M) := Real.log_pos hlogM
  have hlogM1 : Real.log M ≤ Real.log ((M : ℝ) + 1) := Real.log_le_log hM0 (by linarith)
  have hll' : Real.log (Real.log M) ≤ Real.log (Real.log ((M : ℝ) + 1)) :=
    Real.log_le_log (by linarith) hlogM1
  have hlog1 : Real.log ((M : ℝ) + 1) ≤ Real.log M * (1 + 1 / M) := by
    have h := Real.log_le_sub_one_of_pos (x := ((M : ℝ) + 1) / M) (by positivity)
    rw [Real.log_div (by positivity) hM0.ne'] at h
    have he : ((M : ℝ) + 1) / M - 1 = 1 / M := by
      field_simp
      ring
    have hge : 1 / (M : ℝ) ≤ Real.log M * (1 / M) := by
      have : (0 : ℝ) < 1 / M := by positivity
      nlinarith
    nlinarith
  have hc := P.c_pos
  have hnum : 0 ≤ P.c * Real.log ((M : ℝ) + 1) :=
    mul_nonneg hc.le (Real.log_nonneg (by linarith))
  calc A P (M + 1) = P.c * Real.log ((M : ℝ) + 1) / Real.log (Real.log ((M : ℝ) + 1)) := by
        simp [A]
    _ ≤ P.c * Real.log ((M : ℝ) + 1) / Real.log (Real.log M) :=
        div_le_div_of_nonneg_left hnum hll hll'
    _ ≤ P.c * (Real.log M * (1 + 1 / M)) / Real.log (Real.log M) := by
        apply div_le_div_of_nonneg_right _ hll.le
        exact mul_le_mul_of_nonneg_left hlog1 hc.le
    _ = A P M * (1 + 1 / M) := by
        simp only [A]
        ring

/-- `K(M+1) ≤ K(M) (1 + 7/M)` for `M ≥ 3` with `M ≤ K(M)`. -/
theorem Kof_succ_le (P : Params) {M : ℕ} (hM : 3 ≤ M) (hMK : M ≤ Kof P M) :
    (Kof P (M + 1) : ℝ) ≤ Kof P M * (1 + 7 / M) := by
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  set u : ℝ := 1 / M with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by
    rw [hu, div_le_one hM0]
    linarith
  have hMu : (M : ℝ) * u = 1 := by
    rw [hu]
    field_simp
  have hA0 := A_nonneg P hM
  have hA1 := A_nonneg P (by omega : 3 ≤ M + 1)
  have hK1 : (Kof P (M + 1) : ℝ) ≤ A P (M + 1) * ((M : ℝ) + 1) := by
    have := Kof_le P (M + 1) hA1
    push_cast at this
    exact this
  have hAs := A_succ_le P hM
  have hgt := Kof_gt P M
  have hK0 : (0 : ℝ) ≤ Kof P M := Nat.cast_nonneg _
  have hMK' : (M : ℝ) ≤ Kof P M := by exact_mod_cast hMK
  have hKu : (Kof P M : ℝ) + 1 ≤ Kof P M * (1 + u) := by
    have : (1 : ℝ) ≤ Kof P M * u := by
      calc (1 : ℝ) = M * u := hMu.symm
        _ ≤ Kof P M * u := mul_le_mul_of_nonneg_right hMK' hu0.le
    linarith
  have hM1 : (M : ℝ) + 1 = M * (1 + u) := by
    rw [mul_add, hMu, mul_one]
  have hcube : (1 + u) ^ 3 ≤ 1 + 7 * u := by
    have h2 : u ^ 2 ≤ u := by nlinarith
    have h3 : u ^ 3 ≤ u := by nlinarith
    have he : (1 + u) ^ 3 = 1 + 3 * u + 3 * u ^ 2 + u ^ 3 := by ring
    linarith
  calc (Kof P (M + 1) : ℝ) ≤ A P (M + 1) * ((M : ℝ) + 1) := hK1
    _ ≤ A P M * (1 + u) * (M * (1 + u)) := by
        rw [hM1]
        exact mul_le_mul_of_nonneg_right hAs (by positivity)
    _ = A P M * M * (1 + u) ^ 2 := by ring
    _ ≤ ((Kof P M : ℝ) + 1) * (1 + u) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ Kof P M * (1 + u) * (1 + u) ^ 2 := mul_le_mul_of_nonneg_right hKu (by positivity)
    _ = Kof P M * (1 + u) ^ 3 := by ring
    _ ≤ Kof P M * (1 + 7 * u) := mul_le_mul_of_nonneg_left hcube hK0
    _ = Kof P M * (1 + 7 / M) := by rw [hu]; ring

/-- For `0 < δ ≤ 1`, `θ(K) ≤ (1 + δ) K` for infinitely many `M`. -/
theorem frequently_theta_Kof_le (P : Params) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ᶠ M : ℕ in atTop, θ (Kof P M : ℝ) ≤ (1 + δ) * Kof P M := by
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.1 (eventually_M_lt_Kof P)
  set m₀ : ℕ := max (max N M₁) (max 3 ⌈28 / δ⌉₊) with hm₀
  have hNm : N ≤ m₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM₁m : M₁ ≤ m₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have h3m : 3 ≤ m₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hcm : ⌈28 / δ⌉₊ ≤ m₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨x, hx, hθx⟩ :=
    Filter.frequently_atTop.1 (frequently_theta_le (δ := δ / 2) (by positivity)) (Kof P m₀)
  have hm₀K : m₀ < Kof P m₀ := hM₁ m₀ hM₁m
  have hm₀x : m₀ ≤ x := by omega
  set M := Nat.findGreatest (fun m => Kof P m ≤ x) x with hMdef
  have hMge : m₀ ≤ M := Nat.le_findGreatest hm₀x hx
  have hKM : Kof P M ≤ x := Nat.findGreatest_spec (P := fun m => Kof P m ≤ x) hm₀x hx
  have hKM1 : x < Kof P (M + 1) := by
    by_cases hle : M + 1 ≤ x
    · have := Nat.findGreatest_is_greatest (P := fun m => Kof P m ≤ x) (Nat.lt_succ_self _) hle
      simpa using this
    · have h1 := hM₁ (M + 1) (by omega)
      omega
  refine ⟨M, by omega, ?_⟩
  have hM3 : 3 ≤ M := by omega
  have hMK : M ≤ Kof P M := (hM₁ M (by omega)).le
  have hratio := Kof_succ_le P hM3 hMK
  have hM0 : (0 : ℝ) < M := by
    have : (3 : ℝ) ≤ M := by exact_mod_cast hM3
    linarith
  have hMR : 28 / δ ≤ (M : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈28 / δ⌉₊ ≤ M by omega))
  have h7 : 7 / (M : ℝ) ≤ δ / 4 := by
    rw [div_le_iff₀ hM0]
    rw [div_le_iff₀ hδ] at hMR
    linarith
  have hK0 : (0 : ℝ) ≤ Kof P M := Nat.cast_nonneg _
  have hq : 0 ≤ δ / 4 - δ ^ 2 / 8 := by nlinarith
  calc θ (Kof P M : ℝ) ≤ θ (x : ℝ) := Chebyshev.theta_mono (by exact_mod_cast hKM)
    _ ≤ (1 + δ / 2) * x := hθx
    _ ≤ (1 + δ / 2) * Kof P (M + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast hKM1.le
    _ ≤ (1 + δ / 2) * (Kof P M * (1 + 7 / M)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ (1 + δ / 2) * (Kof P M * (1 + δ / 4)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) hK0
    _ ≤ (1 + δ) * Kof P M := by nlinarith [mul_nonneg hK0 hq]

end Erdos457
