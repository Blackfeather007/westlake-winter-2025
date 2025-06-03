import Mathlib.Tactic


/-
# 请为以下的example起一个合乎规范的名字：
-/
variable {α : Type}
example {a : ℝ} : a + 0 = 0 := by sorry

example {a b c : ℝ} : (a + b) * c = a * c + b * c := by sorry

example {a b : ℝ} : a / b = a * b⁻¹ := by sorry

example {a b c : ℤ} : a ∣ b - c → (a ∣ b ↔ a ∣ c) := by sorry

example (s t : Set α) (x : α) : x ∈ s → x ∈ s ∪ t := by sorry

example (s t : Set α) (x : α) : x ∈ s ∪ t → x ∈ s ∨ x ∈ t := by sorry

example {a : α} {p : α → Prop} : a ∈ {x | p x} ↔ p a := by sorry

example {x a : α} {s : Set α} : x ∈ insert a s → x = a ∨ x ∈ s := by sorry

example {x : α} {a b : Set α} : x ∈ a ∩ b → x ∈ a := by sorry

example {a b : ℝ} : a ≤ b ↔ a < b ∨ a = b := by sorry

example {a b : ℤ} : a ≤ b - 1 ↔ a < b := by sorry

example {a b c : ℝ} (bc : a + b ≤ a + c) : b ≤ c := by sorry

/-
# 请根据以下命名猜测并陈述出定理(你可以只在实数集上完成定理的陈述)
1. mul_add
2. add_sub_right_comm
3. le_of_lt_of_le
4. add_le_add
5. mem_union_of_mem_right
-/



/-
# suffices
-/

#check Nat.even_pow'
example (n : ℕ) : Odd (n ^ 2 + n + 1) := by sorry

example (n : ℕ) : Even ((n ^ 3 + 97 * n ^ 2 + 38 * n + 8) * (n ^ 2 + n)) := by sorry

example (s : Set ℕ) (h : {n | 3 ∣ n} ⊆ s) : ∃ x ∈ s, Even x := by sorry

/-
# refine
-/
example {p q : Prop} (h1 : p → q) (h2 : q → p) : p ↔ q := by sorry

example {p q r t : Prop} (h1 : q) (h2 : r) (h3 : t) : (((p ∨ q) ∧ r) ∨ p) ∧ t := by sorry

#check ne_of_lt
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by sorry


/-
# calc
-/

example (a b : ℝ) : - 2 * a * b ≤ a ^ 2 + b ^ 2 := by sorry

example (a b c : ℝ) : a * b + a * c + b * c ≤ a * a + b * b + c * c := by sorry

example {x y ε : ℝ} (epos : 0 < ε) (ele1 : ε ≤ 1) (xlt : |x| < ε) (ylt : |y| < ε) : |x * y| < ε := by sorry


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
