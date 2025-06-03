import Mathlib.Tactic

open Real



example {a b c : ℝ} : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · sorry
    · sorry
  · sorry

example {x y : ℝ} (h : x + y = 0) : -x = y := by
  rw [← neg_add_cancel_left x y, h, add_zero]

#check add_left_cancel
example (x y : ℤ) (h : (x - y) ^ 2 = 0) : x ^ 2 + y ^ 2 = 2 * x * y := by
  rw [← add_zero (2 * x * y), ← h]
  ring


/-
# 命名法
请为以下的定理起个好名字！
-/
-- add_lt_add_of_lt_of_le
example {a b c d : ℝ} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := by sorry

-- dvd_mul_of_dvd_left
#check dvd_mul_of_dvd_left
example {a b c : ℤ} (h : a ∣ b) : a ∣ b * c := by sorry

-- min_le_right
example {a b : ℝ} : min a b ≤ b := by sorry

-- le_trans
example {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by sorry

-- le_of_sub_nonneg
example {a b : ℝ} : 0 ≤ a - b → b ≤ a := by sorry

-- mem_iInter_iff
example {α : Type u} {ι : Sort v} {x : α} {s : ι → Set α} : x ∈ ⋂ i, s i ↔ ∀ (i : ι), x ∈ s i := by sorry

example {α : Type u} {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b := by sorry

/-
# suffices
-/
example (a b c d e : ℝ) (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  suffices h : exp (a + d) ≤ exp (a + e) from by
    linarith
  apply exp_le_exp.2
  linarith

example (a b : ℝ) : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  suffices h : a ^ 2 + b ^ 2 - a * b * 2 ≥ 0 from by
    linarith
  calc
    _ = (a - b) ^ 2 := by ring
    _ ≥ 0 := pow_two_nonneg (a - b)

/-
# refine
-/
example {p q r t w : Prop} (hp : p) (hq : q) (hr : r) (ht : t) (hw : w) : p ∧ q ∧ r ∧ t ∧ w := by
  refine ⟨hp, ⟨hq, ⟨hr, ⟨ht, hw⟩⟩⟩⟩

example {p q : Prop} (h : p → q) (h1 : q → p) : p ↔ q := by
  refine ⟨h, h1⟩

/-
# calc
-/
#check le_of_sub_nonneg
theorem Cauchy_Schwarz_Ineq (a b c d : ℝ) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  have h : 0 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 := by
    calc
      (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 = (a * d - b * c) ^ 2 := by ring
      _ ≥ 0 := pow_two_nonneg (a * d - b * c)
  linarith

/-
# 综合题
-/
open Nat in
example (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  let p := minFac (n ! + 1)
  have hpp : Nat.Prime p := by
    apply minFac_prime
    apply Nat.ne_of_gt
    apply succ_lt_succ
    apply factorial_pos _
  have hnp : n ≤ p := by
    by_contra hc
    push_neg at hc
    have h1 : p ∣ n ! := by
      simp only [p] at hc
      apply dvd_factorial (minFac_pos _)
      apply le_of_lt hc
    have h2 : p ∣ 1 := by
      apply (Nat.dvd_add_iff_right h1).2
      apply minFac_dvd _
    apply Nat.Prime.not_dvd_one hpp h2
  use p

example (m n : ℕ) (h : ¬m.Coprime n) (nezero : m ≠ 0 ∧ n ≠ 0) : m.primeFactors ∩ n.primeFactors ≠ ∅ := by
  suffices h' : ∃ p, p.Prime ∧ p ∣ n ∧ p ∣ m from by
    rcases h' with ⟨p, hp₁, hp₂, hp₃⟩
    rw [Finset.nonempty_iff_ne_empty.symm, Finset.Nonempty]
    use p
    simp [hp₁, hp₂, hp₃, nezero]
  use (m.gcd n).minFac
  rw [Nat.Coprime] at h
  constructor
  · exact Nat.minFac_prime h
  constructor
  · apply Nat.dvd_trans (b := m.gcd n)
    exact Nat.minFac_dvd (m.gcd n)
    exact Nat.gcd_dvd_right m n
  · apply Nat.dvd_trans (b := m.gcd n)
    exact Nat.minFac_dvd (m.gcd n)
    exact Nat.gcd_dvd_left m n

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply lt_of_le_of_ne
    · apply abs_nonneg
    intro h''
    apply abne
    apply eq_of_abs_sub_eq_zero h''.symm
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε := by
    apply hNb
    apply le_max_right
  have : |a - b| < |a - b|
  calc
    |a - b| = |(-(s N - a)) + (s N - b)| := by
      congr
      ring
    _ ≤ |(-(s N - a))| + |s N - b| := (abs_add _ _)
    _ = |s N - a| + |s N - b| := by rw [abs_neg]
    _ < ε + ε := (add_lt_add absa absb)
    _ = |a - b| := by norm_num [ε]

  exact lt_irrefl _ this
