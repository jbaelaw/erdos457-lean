module

public import Mathlib

/-!
# Erdős Problem 457: definitions and the covering criterion

`q n k` is the least prime that does not divide `∏_{1 ≤ i ≤ ⌊k⌋} (n + i)`.  The definition is the
one of the Formal Conjectures project (`FormalConjectures/ErdosProblems/457.lean`), with the
existence lemma (`Nat.exists_prime_not_dvd` there, absent from the pinned Mathlib) proved here as
`Erdos457.exists_prime_not_dvd`.
-/

@[expose] public section

open Finset

namespace Erdos457

/-- Every nonzero natural number has a prime non-divisor (the statement of Mathlib's later
`Nat.exists_prime_not_dvd`, used by the Formal Conjectures definition of `q`). -/
theorem exists_prime_not_dvd {n : ℕ} (hn : n ≠ 0) : ∃ p, p.Prime ∧ ¬p ∣ n := by
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
  exact ⟨p, hp, fun hdvd => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd; omega⟩

/-- Let `q(n, k)` denote the least prime which does not divide `∏_{1 ≤ i ≤ k} (n + i)`
(Formal Conjectures, `Erdos457.q`). -/
noncomputable abbrev q (n : ℕ) (k : ℝ) : ℕ :=
    Nat.find (exists_prime_not_dvd (n := ∏ i ∈ Finset.Icc 1 ⌊k⌋₊, (n + i))
      (Finset.prod_ne_zero_iff.2 fun a ha => by aesop))

/-- `K < q(n, k)` as soon as every prime `p ≤ K` divides the product. -/
theorem lt_q_of_forall {n K : ℕ} {k : ℝ}
    (h : ∀ p, p.Prime → p ≤ K → p ∣ ∏ i ∈ Finset.Icc 1 ⌊k⌋₊, (n + i)) : K < q n k := by
  rw [q, Nat.lt_find_iff]
  intro m hm hcon
  exact hcon.2 (h m hcon.1 hm)

/-- A product over a shorter initial block divides the product over a longer one. -/
theorem prod_Icc_dvd_prod_Icc (n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∏ i ∈ Finset.Icc 1 a, (n + i) ∣ ∏ i ∈ Finset.Icc 1 b, (n + i) :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.Icc_subset_Icc le_rfl hab)

/-- The affine fold (the Erdős 684 formalization's `Code.fold`, restated): if `‖tL‖_p < h` then
`p` divides one of `n + 2, …, n + 2h` for `n = tL - h - 1`. -/
theorem dvd_block_of_near {p h m : ℕ} (hh : 0 < h) (hp : 2 * h < p) (hm : h + 1 ≤ m)
    (hz : m % p < h ∨ p - h < m % p) :
    p ∣ ∏ i ∈ Finset.Icc 1 (2 * h), (m - h - 1 + i) := by
  have hp0 : 0 < p := by omega
  have hzlt := Nat.mod_lt m hp0
  obtain ⟨q', hq⟩ : ∃ q', m = p * q' + m % p := ⟨m / p, (Nat.div_add_mod _ _).symm⟩
  -- find `d ∈ [1, 2h-1]` with `(m - h - 1) % p = p - 1 - d`
  obtain ⟨d, hd1, hd2, hdmod⟩ : ∃ d, 1 ≤ d ∧ d ≤ 2 * h - 1 ∧ (m - h - 1) % p = p - 1 - d := by
    rcases hz with hlt | hgt
    · rcases q' with _ | q'
      · rw [Nat.mul_zero, Nat.zero_add] at hq
        omega
      · rw [Nat.mul_succ] at hq
        refine ⟨h - m % p, by omega, by omega, ?_⟩
        have e2 : m - h - 1 = p * q' + (p - 1 - (h - m % p)) := by omega
        rw [e2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    · refine ⟨p + h - m % p, by omega, by omega, ?_⟩
      have e2 : m - h - 1 = p * q' + (p - 1 - (p + h - m % p)) := by omega
      rw [e2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hmem : d + 1 ∈ Finset.Icc 1 (2 * h) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hdmod, Nat.mod_eq_of_lt (a := d + 1) (by omega)]
  have : p - 1 - d + (d + 1) = p := by omega
  rw [this, Nat.mod_self]

/-- A prime dividing `m` (with `h + 1 ≤ m`) divides the factor `m - h - 1 + (h + 1)` of the block. -/
theorem dvd_block_of_dvd {p h m : ℕ} (hh : 0 < h) (hm : h + 1 ≤ m) (hdvd : p ∣ m) :
    p ∣ ∏ i ∈ Finset.Icc 1 (2 * h), (m - h - 1 + i) := by
  have hmem : h + 1 ∈ Finset.Icc 1 (2 * h) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
  have : m - h - 1 + (h + 1) = m := by omega
  rw [this]
  exact hdvd

end Erdos457
