/-
Copyright (c) 2026 Ji Ho Bae. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ji Ho Bae
-/
module

public import Erdos457

/-!
# Solutions to the Challenge

The declarations of `Challenge.lean`, proved.  `Nat.exists_prime_not_dvd` and `q` are repeated
verbatim; `q` is definitionally equal to the library's `Erdos457.q` (the two `Nat.find` calls have the
same predicate), and each theorem is a bridge to the library:

* `erdos_457_sharp` ← `Erdos457.erdos_457_sharp` (`Erdos457/Main.lean`)
* `limsup_ge_one`   ← `Erdos457.limsup_ge_one`   (`Erdos457/Corollaries.lean`)
* `erdos_457_qnk`   ← `Erdos457.erdos_457_qnk`   (`Erdos457/Corollaries.lean`)
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

theorem q_eq : q = Erdos457.q := rfl

theorem erdos_457_sharp (ε : ℝ) (hε : 0 < ε) :
    {n : ℕ | (1 - ε) * Real.log n * Real.log (Real.log n) /
        Real.log (Real.log (Real.log n)) ≤ q n (Real.log n)}.Infinite := by
  rw [q_eq]; exact Erdos457.erdos_457_sharp ε hε

theorem limsup_ge_one :
    (1 : ℝ≥0∞) ≤ limsup (fun n : ℕ => (q n (Real.log n) : ℝ≥0∞) *
      ENNReal.ofReal (Real.log (Real.log (Real.log n)) /
        (Real.log n * Real.log (Real.log n)))) atTop := by
  rw [q_eq]; exact Erdos457.limsup_ge_one

theorem erdos_457_qnk : ∃ ε > (0 : ℝ),
    {n : ℕ | (2 + ε) * Real.log n ≤ q n (Real.log n)}.Infinite := by
  rw [q_eq]; exact Erdos457.erdos_457_qnk

end Erdos457.Palomar

#print axioms Erdos457.Palomar.erdos_457_sharp
#print axioms Erdos457.Palomar.limsup_ge_one
#print axioms Erdos457.Palomar.erdos_457_qnk
