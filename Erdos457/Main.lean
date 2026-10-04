module

public import Erdos457.Basic
public import Erdos684Lean.Anchor
public import Erdos684Lean.Code
public import Erdos684Lean.Entropy
public import Erdos457.ThetaK

/-!
# Erdős Problem 457 with the sharp constant

For every `ε > 0` there are infinitely many `n` with
`q(n, log n) ≥ (1 - ε) log n · log log n / log log log n`.

The construction is the product-cell code of the Erdős 684 development (`Erdos684Lean`):
`n = t L_M - h - 1`, where `t` is an anchored difference inside a code fibre.  Since only primes
matter here (no prime-power tail), the multiplier range can be taken as small as
`e^{M} < t ≤ e^{(c+2)M}`, and the constant tends to `1` as `c → ∞`.

No prime number theorem is used: the entropy bound needs `θ(K) ≤ (1 + δ) K` only at the scales
`M` that are actually used, and Chebyshev's elementary `liminf θ(x)/x ≤ 1` supplies infinitely
many of them (`Erdos457.frequently_theta_Kof_le`).  Elsewhere only Chebyshev's bounds
`ψ(x) ≤ (log 4 + 4) x` and `2^M ≤ (M + 1) lcm(1, …, M)` (Mathlib) are used.
-/

@[expose] public section

open Finset Real Filter Topology
open scoped Chebyshev

namespace Erdos457

open Erdos684

/-- The parameter `c` of the scales. -/
noncomputable def params (c : ℝ) (hc : 0 < c) : Params where
  c := c
  c_pos := hc

/-- The pool size `J = ⌊e^{(c+2)M}⌋`. -/
noncomputable def pool (c : ℝ) (M : ℕ) : ℕ := ⌊Real.exp ((c + 2) * M)⌋₊

/-- The forbidden small differences `{1, …, ⌊e^M⌋}`. -/
noncomputable def forb (M : ℕ) : Finset ℕ := Finset.Icc 1 ⌊Real.exp (M : ℝ)⌋₊

/-- The anchor condition `C_M (|F| + 1) < J + 1`. -/
theorem eventually_anchor (c : ℝ) (hc : 0 < c) :
    ∀ᶠ M : ℕ in atTop,
      θ (Kof (params c hc) M : ℝ) ≤ (1 + 1 / 2 / (4 * c)) * Kof (params c hc) M →
        CM (params c hc) M * ((forb M).card + 1) < pool c M + 1 := by
  filter_upwards [log_CM_le (params c hc) (1 / 2) (by norm_num), eventually_ge_atTop 3]
    with M hCM hM3 hθ
  replace hCM := hCM hθ
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hCMpos : (0 : ℝ) < CM (params c hc) M := by
    have : 0 < CM (params c hc) M := Finset.prod_pos fun p _ => Nat.succ_pos _
    exact_mod_cast this
  have hCMle : (CM (params c hc) M : ℝ) ≤ Real.exp ((c + 1 / 2) * M) := by
    rw [← Real.exp_log hCMpos]
    exact Real.exp_le_exp.2 hCM
  have hFcard : ((forb M).card : ℝ) ≤ Real.exp (M : ℝ) := by
    have : (forb M).card = ⌊Real.exp (M : ℝ)⌋₊ := by simp [forb]
    rw [this]
    exact Nat.floor_le (Real.exp_pos _).le
  have hexpM : 1 ≤ Real.exp (M : ℝ) := Real.one_le_exp (by positivity)
  have hE : Real.exp ((c + 1 / 2) * M) * Real.exp (M : ℝ) = Real.exp ((c + 3 / 2) * M) := by
    rw [← Real.exp_add]; ring_nf
  have hE' : Real.exp ((c + 3 / 2) * M) * Real.exp ((M : ℝ) / 2) = Real.exp ((c + 2) * M) := by
    rw [← Real.exp_add]; ring_nf
  have hE1 : 0 < Real.exp ((c + 3 / 2) * M) := Real.exp_pos _
  have hhalf : (5 : ℝ) / 2 ≤ Real.exp ((M : ℝ) / 2) := by
    have := Real.add_one_le_exp ((M : ℝ) / 2)
    linarith
  have hlhs : (CM (params c hc) M : ℝ) * ((forb M).card + 1) ≤
      2 * Real.exp ((c + 3 / 2) * M) := by
    calc (CM (params c hc) M : ℝ) * ((forb M).card + 1)
        ≤ Real.exp ((c + 1 / 2) * M) * (2 * Real.exp (M : ℝ)) :=
          mul_le_mul hCMle (by linarith) (by positivity) (by positivity)
      _ = 2 * Real.exp ((c + 3 / 2) * M) := by rw [← hE]; ring
  have hrhs : Real.exp ((c + 2) * M) < pool c M + 1 := Nat.lt_floor_add_one _
  have hmid : 2 * Real.exp ((c + 3 / 2) * M) < Real.exp ((c + 2) * M) := by
    rw [← hE']
    nlinarith
  have : (CM (params c hc) M : ℝ) * ((forb M).card + 1) < pool c M + 1 := by linarith
  exact_mod_cast this

/-- `n_t = tL - h - 1` in `ℝ`, and `n_t ≥ tL/2` (from the Erdős 684 development). -/
theorem nOf_cast_bounds (P : Params) {M t : ℕ} (ht : 1 ≤ t) (hL : 2 * (hof P M + 1) ≤ Lof M) :
    (nOf P M t : ℝ) = t * Lof M - (hof P M + 1) ∧ (t : ℝ) * Lof M / 2 ≤ nOf P M t := by
  have hh1 : hof P M + 1 ≤ t * Lof M := by
    calc hof P M + 1 ≤ Lof M := by omega
      _ ≤ t * Lof M := Nat.le_mul_of_pos_left _ ht
  have hn : (nOf P M t : ℝ) = t * Lof M - (hof P M + 1) := by
    unfold nOf
    rw [Nat.sub_sub, Nat.cast_sub hh1]
    push_cast
    ring
  refine ⟨hn, ?_⟩
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hLR : (2 : ℝ) * (hof P M + 1) ≤ Lof M := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < Lof M := by exact_mod_cast Lof_pos M
  have h1 : (1 : ℝ) * Lof M ≤ t * Lof M := mul_le_mul_of_nonneg_right htR hLpos.le
  rw [hn]
  linarith

/-- `log t + log L - log 2 ≤ log n_t ≤ log t + log L`. -/
theorem log_nOf_bounds (P : Params) {M t : ℕ} (ht : 1 ≤ t) (hL : 2 * (hof P M + 1) ≤ Lof M) :
    Real.log t + Real.log (Lof M) - Real.log 2 ≤ Real.log (nOf P M t) ∧
      Real.log (nOf P M t) ≤ Real.log t + Real.log (Lof M) := by
  obtain ⟨hn, hlow⟩ := nOf_cast_bounds P ht hL
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hLpos : (0 : ℝ) < Lof M := by exact_mod_cast Lof_pos M
  have hh0 : (0 : ℝ) ≤ hof P M + 1 := by positivity
  have htL : (0 : ℝ) < t * Lof M / 2 := by positivity
  have hnpos : (0 : ℝ) < nOf P M t := lt_of_lt_of_le htL hlow
  constructor
  · calc Real.log t + Real.log (Lof M) - Real.log 2 = Real.log (t * Lof M / 2) := by
          rw [Real.log_div (by positivity) (by norm_num), Real.log_mul htR.ne' hLpos.ne']
      _ ≤ Real.log (nOf P M t) := Real.log_le_log htL hlow
  · calc Real.log (nOf P M t) ≤ Real.log (t * Lof M) :=
          Real.log_le_log hnpos (by rw [hn]; linarith)
      _ = Real.log t + Real.log (Lof M) := Real.log_mul htR.ne' hLpos.ne'

/-- Every prime `p ≤ K` divides the block `(n+1)⋯(n+2h)` of `n = tL - h - 1`, as soon as
`‖tL‖_p < h` for all primes `M < p ≤ K`. -/
theorem block_cover (P : Params) {M t : ℕ} (hh : 0 < hof P M) (h2h : 2 * hof P M < M)
    (hht : hof P M + 1 ≤ t * Lof M)
    (hcell : ∀ p ∈ PMK P M, t * Lof M % p < hof P M ∨ p - hof P M < t * Lof M % p) :
    ∀ p, p.Prime → p ≤ Kof P M →
      p ∣ ∏ i ∈ Finset.Icc 1 (2 * hof P M), (nOf P M t + i) := by
  intro p hp hpK
  unfold nOf
  rcases le_or_gt p M with hpM | hpM
  · -- `p ≤ M`: `p ∣ L ∣ tL = n + h + 1`
    have hpL : p ∣ Lof M := dvd_Lof hp.pos hpM
    exact dvd_block_of_dvd hh hht (dvd_mul_of_dvd_right hpL t)
  · -- `M < p ≤ K`: the fold
    have hmem : p ∈ PMK P M := by
      simp only [PMK, Finset.mem_filter]
      exact ⟨Nat.mem_primesLE.2 ⟨hpK, hp⟩, hpM⟩
    exact dvd_block_of_near hh (by omega) hht (hcell p hmem)

/-- Chebyshev's constant in `ψ(x) ≤ C₁ x` (Mathlib `Chebyshev.psi_le_const_mul_self`). -/
noncomputable def C1 : ℝ := Real.log 4 + 4

theorem C1_pos : 0 < C1 := by
  unfold C1
  have : 0 < Real.log 4 := Real.log_pos (by norm_num)
  linarith

/-- `(M + 1)² ≤ 2^M` for `M ≥ 6`. -/
theorem sq_succ_le_two_pow {M : ℕ} (hM : 6 ≤ M) : (M + 1) ^ 2 ≤ 2 ^ M := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    calc (M + 1 + 1) ^ 2 ≤ 2 * (M + 1) ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ M := by omega
      _ = 2 ^ (M + 1) := by ring

/-- `M + 1 ≤ lcm(1, …, M)` for `M ≥ 6`. -/
theorem succ_le_Lof {M : ℕ} (hM : 6 ≤ M) : M + 1 ≤ Lof M := by
  have h1 := Chebyshev.two_pow_le_mul_lcmUpto M
  have h2 := sq_succ_le_two_pow hM
  have h3 : (M + 1) * (M + 1) ≤ (M + 1) * Lof M := by
    rw [← pow_two]
    exact h2.trans h1
  exact Nat.le_of_mul_le_mul_left h3 (Nat.succ_pos M)

/-- Fixed `c`: for all large `M` with `θ(K) ≤ (1 + 1/(8c)) K` there is `n` with
`M ≤ log n ≤ (c + 2 + C₁) M` and `K_M < q(n, log n)`. -/
theorem prop_fixed (c : ℝ) (hc : 0 < c) :
    ∀ᶠ M : ℕ in atTop,
      θ (Kof (params c hc) M : ℝ) ≤ (1 + 1 / 2 / (4 * c)) * Kof (params c hc) M →
        ∃ n : ℕ, (M : ℝ) ≤ Real.log n ∧ Real.log n ≤ (c + 2 + C1) * M ∧
          Kof (params c hc) M < q n (Real.log n) := by
  set P := params c hc with hP
  have hPc : P.c = c := rfl
  filter_upwards [eventually_anchor c hc, eventually_two_hof_lt P, eventually_hof_pos P,
    eventually_ge_atTop 8] with M hanc h2h hh0 hM3 hθ
  replace hanc := hanc hθ
  have hMR : (8 : ℝ) ≤ M := by exact_mod_cast hM3
  have hMpos : (0 : ℝ) < M := by linarith
  have hLR : (0 : ℝ) < Lof M := by exact_mod_cast Lof_pos M
  have hψ2 : Real.log (Lof M) ≤ C1 * M := by
    rw [log_Lof]
    exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg M)
  have hLM1 : M + 1 ≤ Lof M := succ_le_Lof (by omega)
  have hLM : 2 * (hof P M + 1) ≤ Lof M := by omega
  have hlogL2 : Real.log 2 ≤ Real.log (Lof M) := by
    apply Real.log_le_log (by norm_num)
    have : (2 : ℕ) ≤ Lof M := by omega
    exact_mod_cast this
  -- the anchored pair
  obtain ⟨i, j, hij, hjJ, hcode, hnotF⟩ := anchor (pool c M) (code P M) (codeSet P M)
    (fun j _ => code_mem_codeSet P M j) (forb M) (by rw [card_codeSet]; exact hanc)
  set t := j - i with ht_def
  have ht1 : 1 ≤ t := by omega
  have htF : ⌊Real.exp (M : ℝ)⌋₊ < t := by
    by_contra hcon
    push Not at hcon
    exact hnotF (Finset.mem_Icc.2 ⟨ht1, hcon⟩)
  have htlow : Real.exp (M : ℝ) < t := by
    have := Nat.lt_floor_add_one (Real.exp (M : ℝ))
    have h2 : ((⌊Real.exp (M : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast htF
    push_cast at h2
    linarith
  have htJ : t ≤ pool c M := by omega
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have hlogt1 : (M : ℝ) < Real.log t := (Real.lt_log_iff_exp_lt htpos).2 htlow
  have hlogt2 : Real.log t ≤ (c + 2) * M := by
    calc Real.log t ≤ Real.log (Real.exp ((c + 2) * M)) :=
          Real.log_le_log htpos (le_trans (by exact_mod_cast htJ) (Nat.floor_le (Real.exp_pos _).le))
      _ = (c + 2) * M := Real.log_exp _
  -- the cells: `‖tL‖_p < h` for every prime `M < p ≤ K`
  have hcell : ∀ p ∈ PMK P M, t * Lof M % p < hof P M ∨ p - hof P M < t * Lof M % p := by
    intro p hp
    have hpM : M < p := (Finset.mem_filter.1 hp).2
    have hc' := congrFun hcode ⟨p, hp⟩
    simp only [code] at hc'
    exact equal_cell hh0 (by omega) hij hc'
  have hht : hof P M + 1 ≤ t * Lof M := by
    calc hof P M + 1 ≤ Lof M := by omega
      _ ≤ t * Lof M := Nat.le_mul_of_pos_left _ ht1
  have hcov := block_cover P hh0 h2h hht hcell
  -- the bounds on `log n`
  obtain ⟨hlo, hhi⟩ := log_nOf_bounds P ht1 hLM
  have hnlo : (M : ℝ) ≤ Real.log (nOf P M t) := by linarith
  have hnhi : Real.log (nOf P M t) ≤ (c + 2 + C1) * M := by linarith
  refine ⟨nOf P M t, hnlo, hnhi, ?_⟩
  -- `2h ≤ ⌊log n⌋`
  have h2hlog : 2 * hof P M ≤ ⌊Real.log (nOf P M t)⌋₊ := by
    apply Nat.le_floor
    have h1 : ((2 * hof P M : ℕ) : ℝ) < M := by exact_mod_cast h2h
    linarith
  apply lt_q_of_forall
  intro p hp hpK
  exact dvd_trans (hcov p hp hpK) (prod_Icc_dvd_prod_Icc _ h2hlog)

/-- The real-number estimate: with `X = log n`, `M ≤ X ≤ s M`, `a = κ s`, `b = log s` and
`c - a ≥ 1`, the quantity `κ X log X / log log X` is at most `c M log M / log log M - 1` once
`log M ≥ a b + 1` (the Erdős 684 development's `final_estimate`, with a general `κ ≥ 0`). -/
theorem final_estimate {κ s a b c M X : ℝ} (hκ : 0 ≤ κ) (hs1 : 1 ≤ s)
    (ha : a = κ * s) (hb : b = Real.log s) (hca : 1 ≤ c - a) (hM : 1 ≤ M)
    (hlogM : 1 ≤ Real.log M) (hllM : 1 ≤ Real.log (Real.log M))
    (hlogM' : a * b + 1 ≤ Real.log M) (hX1 : M ≤ X) (hX2 : X ≤ s * M) :
    κ * X * Real.log X / Real.log (Real.log X) ≤
      c * M * Real.log M / Real.log (Real.log M) - 1 := by
  have hMpos : 0 < M := by linarith
  have hXpos : 0 < X := by linarith
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; exact Real.log_nonneg hs1
  have hlogX1 : Real.log M ≤ Real.log X := Real.log_le_log hMpos hX1
  have hlogX2 : Real.log X ≤ b + Real.log M := by
    rw [hb, ← Real.log_mul (by linarith) hMpos.ne']
    exact Real.log_le_log hXpos hX2
  have hlogX_pos : 0 < Real.log X := by linarith
  have hlll : Real.log (Real.log M) ≤ Real.log (Real.log X) :=
    Real.log_le_log (by linarith) hlogX1
  have hllM_pos : 0 < Real.log (Real.log M) := by linarith
  have hratio : κ * X * Real.log X / Real.log (Real.log X) ≤
      a * M * (b + Real.log M) / Real.log (Real.log M) := by
    apply div_le_div₀ (mul_nonneg (mul_nonneg ha0 hMpos.le) (by linarith)) _ hllM_pos hlll
    rw [ha]
    calc κ * X * Real.log X
        ≤ κ * (s * M) * (b + Real.log M) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hX2 hκ) hlogX2 hlogX_pos.le
          positivity
      _ = κ * s * M * (b + Real.log M) := by ring
  have hbound : a * M * (b + Real.log M) / Real.log (Real.log M) ≤
      c * M * Real.log M / Real.log (Real.log M) - 1 := by
    have h1 : c * M * Real.log M / Real.log (Real.log M) - 1
        = (c * M * Real.log M - Real.log (Real.log M)) / Real.log (Real.log M) := by
      field_simp
    rw [h1, div_le_div_iff_of_pos_right hllM_pos]
    have hllM_le : Real.log (Real.log M) ≤ M := by
      have h1 := Real.log_le_sub_one_of_pos hMpos
      have h2 := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log M)
      linarith
    have h2 : M * (a * b + 1) ≤ M * Real.log M := mul_le_mul_of_nonneg_left hlogM' hMpos.le
    have h3 : (1 : ℝ) * (M * Real.log M) ≤ (c - a) * (M * Real.log M) :=
      mul_le_mul_of_nonneg_right hca (by positivity)
    linarith
  exact hratio.trans hbound

private theorem eventually_log_ge (c : ℝ) : ∀ᶠ n : ℕ in atTop, c ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c

private theorem eventually_loglog_ge (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c ≤ Real.log (Real.log n) :=
  (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop c

/-- The main theorem for `0 < ε ≤ 1/2`. -/
theorem main_aux (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ᶠ n : ℕ in atTop, (1 - ε) * Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n)) ≤ q n (Real.log n) := by
  have hC1 := C1_pos
  set c : ℝ := (3 + C1) / ε with hc_def
  have hc : 0 < c := by positivity
  have hεc : ε * c = 3 + C1 := by rw [hc_def]; field_simp
  have hc6 : 6 ≤ c := by
    rw [hc_def, le_div_iff₀ hε]
    nlinarith
  set P := params c hc with hP
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = c + 2 + C1 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (1 - ε) * s := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = Real.log s := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hκ : 0 ≤ 1 - ε := by linarith
  have hca : 1 ≤ c - a := by
    rw [ha, hs]
    nlinarith [mul_pos hε hC1]
  have hδ : 0 < 1 / 2 / (4 * c) := by positivity
  have hδ1 : 1 / 2 / (4 * c) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hall : ∃ᶠ M : ℕ in atTop,
      (∃ n : ℕ, (M : ℝ) ≤ Real.log n ∧ Real.log n ≤ (c + 2 + C1) * M ∧
        Kof P M < q n (Real.log n)) ∧
      1 ≤ Real.log M ∧ 1 ≤ Real.log (Real.log M) ∧ a * b + 1 ≤ Real.log M ∧ 1 ≤ M := by
    refine (frequently_theta_Kof_le P hδ hδ1).mp ?_
    filter_upwards [prop_fixed c hc, eventually_log_ge 1, eventually_loglog_ge 1,
      eventually_log_ge (a * b + 1), eventually_ge_atTop 1] with M h1 h2 h3 h4 h5 hθ
    exact ⟨h1 hθ, h2, h3, h4, h5⟩
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨M, hMN, ⟨n, hn1, hn2, hn3⟩, hlogM, hllM, hlogM', hM1⟩ :=
    Filter.frequently_atTop.1 hall N
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hMpos : (0 : ℝ) < M := by linarith
  have hX1 : (M : ℝ) ≤ Real.log n := hn1
  have hXpos : 0 < Real.log n := by linarith
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hXpos
      exact absurd hXpos (lt_irrefl 0)
    · exact_mod_cast h
  refine ⟨n, ?_, ?_⟩
  · have h1 : ((N : ℕ) : ℝ) + 1 ≤ n := by
      calc ((N : ℕ) : ℝ) + 1 ≤ (M : ℝ) + 1 := by
            have : ((N : ℕ) : ℝ) ≤ M := by exact_mod_cast hMN
            linarith
        _ ≤ Real.exp M := Real.add_one_le_exp _
        _ ≤ Real.exp (Real.log n) := Real.exp_le_exp.2 hX1
        _ = n := Real.exp_log hnpos
    have h2 : N + 1 ≤ n := by exact_mod_cast h1
    omega
  · have hX2 : Real.log n ≤ s * M := by rw [hs]; exact hn2
    have hest := final_estimate hκ hs1 ha hb hca hMR hlogM hllM hlogM' hX1 hX2
    have hAM : A P M * M = c * M * Real.log M / Real.log (Real.log M) := by
      have hPc : P.c = c := rfl
      unfold A; rw [hPc]; ring
    have hK : ((Kof P M : ℕ) : ℝ) < q n (Real.log n) := by exact_mod_cast hn3
    calc (1 - ε) * Real.log n * Real.log (Real.log n) / Real.log (Real.log (Real.log n))
        ≤ c * M * Real.log M / Real.log (Real.log M) - 1 := hest
      _ = A P M * M - 1 := by rw [hAM]
      _ ≤ Kof P M := (Kof_gt P _).le
      _ ≤ q n (Real.log n) := hK.le

/-- **Main theorem.**  For every `ε > 0` there are infinitely many `n` with
`q(n, log n) ≥ (1 - ε) log n · log log n / log log log n`. -/
theorem main_theorem (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, (1 - ε) * Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n)) ≤ q n (Real.log n) := by
  have hε' : 0 < min ε (1 / 2) := lt_min hε (by norm_num)
  have h := main_aux (min ε (1 / 2)) hε' (min_le_right _ _)
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 ≤ Real.log n * Real.log (Real.log n) / Real.log (Real.log (Real.log n)) := by
    filter_upwards [eventually_log_ge 0, eventually_loglog_ge 0,
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually_ge_atTop 0]
      with n h1 h2 h3
    exact div_nonneg (mul_nonneg h1 h2) h3
  refine (h.and_eventually hpos).mono ?_
  rintro n ⟨hn, hX⟩
  calc (1 - ε) * Real.log n * Real.log (Real.log n) / Real.log (Real.log (Real.log n))
      = (1 - ε) * (Real.log n * Real.log (Real.log n) / Real.log (Real.log (Real.log n))) := by
        ring
    _ ≤ (1 - min ε (1 / 2)) * (Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n))) := by
        apply mul_le_mul_of_nonneg_right _ hX
        linarith [min_le_left ε (1 / 2)]
    _ = (1 - min ε (1 / 2)) * Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n)) := by ring
    _ ≤ q n (Real.log n) := hn

/-- **Main theorem**, as a statement about an infinite set. -/
theorem erdos_457_sharp (ε : ℝ) (hε : 0 < ε) :
    {n : ℕ | (1 - ε) * Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n)) ≤ q n (Real.log n)}.Infinite :=
  Nat.frequently_atTop_iff_infinite.1 (main_theorem ε hε)

end Erdos457
