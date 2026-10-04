/-
Copyright (c) 2026 Ji Ho Bae. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ji Ho Bae
-/
module

public import Mathlib

/-!
# Erdős Problem 457: the sharp constant in the lower bound — statement of record

`q(n, k)` is the least prime that does not divide `∏_{1 ≤ i ≤ k} (n + i)`.  The definition below
is copied verbatim from the Formal Conjectures project (`FormalConjectures/ErdosProblems/457.lean`,
`Erdos457.q`).  The existence lemma it uses, `Nat.exists_prime_not_dvd`, is not in the pinned
Mathlib; it is stated and proved here under the same name (it is infrastructure, not a claim).

Compared declarations:
* `erdos_457_sharp` — for every `ε > 0`, `q(n, log n) ≥ (1 - ε) log n · log log n / log log log n`
  for infinitely many `n`;
* `limsup_ge_one` — `limsup_{n→∞} q(n, log n) · log log log n / (log n · log log n) ≥ 1`;
* `erdos_457_qnk` — the Formal Conjectures variant `erdos_457.variants.qnk` (answer: true).
-/

@[expose] public section

open Filter Topology Real
open scoped ENNReal

/-- Every nonzero natural number has a prime non-divisor (present in later Mathlib; stated and
proved here so that the Formal Conjectures definition of `q` compiles verbatim). -/
theorem Nat.exists_prime_not_dvd {n : ℕ} (hn : n ≠ 0) : ∃ p, p.Prime ∧ ¬p ∣ n :=
  (Nat.exists_infinite_primes (n + 1)).elim fun p h =>
    ⟨p, h.2, fun hdvd => Nat.not_succ_le_self n (h.1.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd))⟩

namespace Erdos457.Palomar

/-- Let `q(n, k)` denote the least prime which does not divide `∏_{1 ≤ i ≤ k} (n + i)`. -/
noncomputable abbrev q (n : ℕ) (k : ℝ) : ℕ :=
    Nat.find (Nat.exists_prime_not_dvd (n := ∏ i ∈ Finset.Icc 1 ⌊k⌋₊, (n + i))
      (Finset.prod_ne_zero_iff.2 fun a ha => by aesop))

/-- For every `ε > 0` there are infinitely many `n` with
`q(n, log n) ≥ (1 - ε) log n · log log n / log log log n`. -/
theorem erdos_457_sharp (ε : ℝ) (hε : 0 < ε) :
    {n : ℕ | (1 - ε) * Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n)) ≤ q n (Real.log n)}.Infinite := by
  sorry

/-- `limsup_{n→∞} q(n, log n) · log log log n / (log n · log log n) ≥ 1`, in `ℝ≥0∞`. -/
theorem limsup_ge_one :
    (1 : ℝ≥0∞) ≤ limsup (fun n : ℕ => (q n (Real.log n) : ℝ≥0∞) *
      ENNReal.ofReal (Real.log (Real.log (Real.log n)) /
        (Real.log n * Real.log (Real.log n)))) atTop := by
  sorry

/-- Formal Conjectures `erdos_457.variants.qnk`: there is `ε > 0` with
`q(n, log n) ≥ (2 + ε) log n` for infinitely many `n`. -/
theorem erdos_457_qnk : ∃ ε > (0 : ℝ),
    {n : ℕ | (2 + ε) * Real.log n ≤ q n (Real.log n)}.Infinite := by
  sorry

end Erdos457.Palomar
