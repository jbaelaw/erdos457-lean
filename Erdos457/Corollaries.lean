module

public import Erdos457.Main

/-!
# Consequences of the sharp lower bound

* `erdos_457_qnk` — the variant `erdos_457.variants.qnk` of the Formal Conjectures project:
  `q(n, log n) ≥ (2 + ε) log n` for infinitely many `n` (with `ε = 1`).
* `limsup_ge_one` — the sharp constant in `limsup` form:
  `1 ≤ limsup q(n, log n) · log log log n / (log n · log log n)` in `ℝ≥0∞`.
-/

@[expose] public section

open Filter Topology Real
open scoped ENNReal

namespace Erdos457

/-- `y ≤ log log n / log log log n · ...`: the ratio `log log n / log log log n` tends to `∞`. -/
private theorem eventually_ratio_ge (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C ≤ Real.log (Real.log n) / Real.log (Real.log (Real.log n)) := by
  -- `y / log y → ∞` along `y = log log n → ∞`
  have hy : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun y : ℝ => y / Real.log y) atTop atTop := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    -- `h : Tendsto (fun x => log x ^ 1 / (1 * x + 0)) atTop (𝓝 0)`
    have h' : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using h
      · filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy1
        exact div_pos (Real.log_pos hy1) (by linarith)
    have := h'.inv_tendsto_nhdsGT_zero
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy1
    simp [inv_div]
  exact (hlim.comp hy).eventually_ge_atTop C

/-- **Formal Conjectures `erdos_457.variants.qnk`** (answer: true): there is `ε > 0` such that
`q(n, log n) ≥ (2 + ε) log n` for infinitely many `n`. -/
theorem erdos_457_qnk : ∃ ε > (0 : ℝ),
    {n : ℕ | (2 + ε) * Real.log n ≤ q n (Real.log n)}.Infinite := by
  refine ⟨1, one_pos, ?_⟩
  have h := main_theorem (1 / 2) (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop, 0 < Real.log n ∧ 0 < Real.log (Real.log (Real.log n)) ∧
      6 ≤ Real.log (Real.log n) / Real.log (Real.log (Real.log n)) := by
    filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually_gt_atTop 0,
      eventually_ratio_ge 6] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine Nat.frequently_atTop_iff_infinite.1 ((h.and_eventually hev).mono ?_)
  rintro n ⟨hn, hlog, hlll, hratio⟩
  calc (2 + 1) * Real.log n ≤ (1 - 1 / 2) * Real.log n *
        (Real.log (Real.log n) / Real.log (Real.log (Real.log n))) := by nlinarith
    _ = (1 - 1 / 2) * Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n)) := by ring
    _ ≤ q n (Real.log n) := hn

/-! ## The `limsup` form -/

/-- The normalized value `q(n, log n) · log log log n / (log n · log log n)` in `ℝ≥0∞`. -/
noncomputable def normQ (n : ℕ) : ℝ≥0∞ :=
  (q n (Real.log n) : ℝ≥0∞) *
    ENNReal.ofReal (Real.log (Real.log (Real.log n)) / (Real.log n * Real.log (Real.log n)))

/-- For every `0 < ε < 1`, `1 - ε ≤ limsup_n normQ n`. -/
theorem ofReal_le_limsup_normQ (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ENNReal.ofReal (1 - ε) ≤ limsup normQ atTop := by
  apply le_limsup_of_frequently_le'
  have hl : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hl
  have hlll : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log n))) atTop atTop :=
    Real.tendsto_log_atTop.comp hll
  have hev : ∀ᶠ n : ℕ in atTop, 0 < Real.log n ∧ 0 < Real.log (Real.log n) ∧
      0 < Real.log (Real.log (Real.log n)) :=
    (hl.eventually_gt_atTop 0).and ((hll.eventually_gt_atTop 0).and (hlll.eventually_gt_atTop 0))
  refine ((main_theorem ε hε).and_eventually hev).mono ?_
  rintro n ⟨hP, hl0, hll0, hlll0⟩
  set l := Real.log n with hl_def
  set ll := Real.log (Real.log n) with hll_def
  set lll := Real.log (Real.log (Real.log n)) with hlll_def
  have hpos : 0 < 1 - ε := by linarith
  set Y : ℝ := (1 - ε) * l * ll / lll with hY_def
  have hY : 0 < Y := by positivity
  have hY1 : ENNReal.ofReal Y ≤ (q n (Real.log n) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hP
  have hprod : Y * (lll / (l * ll)) = 1 - ε := by
    rw [hY_def]
    field_simp
  unfold normQ
  calc ENNReal.ofReal (1 - ε)
      = ENNReal.ofReal Y * ENNReal.ofReal (lll / (l * ll)) := by
        rw [← ENNReal.ofReal_mul hY.le, hprod]
    _ ≤ (q n (Real.log n) : ℝ≥0∞) * ENNReal.ofReal (lll / (l * ll)) := by gcongr

/-- **The sharp constant, `limsup` form**:
`limsup_{n→∞} q(n, log n) · log log log n / (log n · log log n) ≥ 1`. -/
theorem limsup_ge_one :
    (1 : ℝ≥0∞) ≤ limsup (fun n : ℕ => (q n (Real.log n) : ℝ≥0∞) *
      ENNReal.ofReal (Real.log (Real.log (Real.log n)) /
        (Real.log n * Real.log (Real.log n)))) atTop := by
  change (1 : ℝ≥0∞) ≤ limsup normQ atTop
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  set δ : ℝ := min (ε : ℝ) (1 / 2) with hδ_def
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδε : δ ≤ (ε : ℝ) := min_le_left _ _
  calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
    _ ≤ ENNReal.ofReal (1 - δ) + ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) ε.coe_nonneg]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (1 - δ) + ε := by rw [ENNReal.ofReal_coe_nnreal]
    _ ≤ limsup normQ atTop + ε := by
        have := ofReal_le_limsup_normQ δ hδ0 hδ1
        gcongr

end Erdos457
