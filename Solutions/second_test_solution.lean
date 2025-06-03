import Mathlib.Tactic

/-
# 请为以下的example起一个合乎规范的名字：
-/
variable {α : Type}
example {a : ℝ} : a + 0 = a := by sorry
#check add_zero

example {a b c : ℝ} : (a + b) * c = a * c + b * c := by
  simp [add_mul]
#check add_mul

example {a b : ℝ} : a / b = a * b⁻¹ := by exact rfl
-- div_eq_mul_inv
#check div_eq_mul_inv

example {a b c : ℤ} : a ∣ b - c → (a ∣ b ↔ a ∣ c) := by
  exact fun a_1 => Int.dvd_iff_dvd_of_dvd_sub a_1
#check dvd_iff_dvd_of_dvd_sub

example (s t : Set α) (x : α) : x ∈ s → x ∈ s ∪ t := by
  exact fun a => Set.mem_union_left t a
#check Set.mem_union_left


example (s t : Set α) (x : α) : x ∈ s ∪ t → x ∈ s ∨ x ∈ t := by
  exact fun a => a
#check Set.mem_or_mem_of_mem_union

example {a : α} {p : α → Prop} : a ∈ {x | p x} ↔ p a := by
  exact Set.mem_setOf
#check Set.mem_setOf

example {x a : α} {s : Set α} : x ∈ insert a s → x = a ∨ x ∈ s := by exact fun a ↦ a
#check Set.mem_insert_iff

example {x : α} {a b : Set α} : x ∈ a ∩ b → x ∈ a := by  exact fun a_1 => Set.mem_of_mem_inter_left a_1
#check Set.mem_of_mem_inter_left

example {a b : ℝ} : a ≤ b ↔ a < b ∨ a = b := by
  exact le_iff_lt_or_eq
#check le_iff_lt_or_eq

example {a b : ℤ} : a ≤ b - 1 ↔ a < b := by
  exact Int.le_sub_one_iff
#check Int.le_sub_one_iff

example {a b c : ℝ} (bc : a + b ≤ a + c) : b ≤ c := by
  exact (add_le_add_iff_left a).mp bc
#check add_le_add_iff_left

/-
# 请根据以下命名猜测并陈述出定理
1. mul_add
2. add_sub_right_comm
3. le_of_lt_of_le
4. add_le_add
5. mem_union_of_mem_right
-/

/-直接#check它们就好，这些都是真的存在的定理-/

/-
# 练习
今天的练习不再给出所需要使用的定理，请根据所学的内容进行查询！
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


/-
# suffices
-/

#check Nat.even_pow'
example (n : ℕ) : Odd (n ^ 2 + n + 1) := by
  suffices h : Even (n ^ 2 + n) from by
    exact Even.add_one h
  apply Nat.even_add.mpr
  constructor
  · intro h
    apply (Nat.even_pow' ?_).1 h
    linarith
  intro h
  apply Nat.even_pow.mpr
  simpa

example (n : ℕ) : Even ((n ^ 3 + 97 * n ^ 2 + 38 * n + 8) * (n ^ 2 + n)) := by
  suffices h : Even (n ^ 2 + n) from by
    apply Even.mul_left h
  apply Nat.even_add.mpr
  constructor
  · intro h
    apply (Nat.even_pow' ?_).1 h
    linarith
  intro h
  apply Nat.even_pow.mpr
  simpa

example (s : Set ℕ) (h : {n | 3 ∣ n} ⊆ s) : ∃ x ∈ s, Even x := by
  suffices h' : ∃ x ∈ {n | 3 ∣ n}, Even x from by
    rcases h' with ⟨x, hx, x_even⟩
    use x
    exact ⟨h hx, x_even⟩
  use 6
  rw [Set.mem_setOf_eq]
  constructor
  · exact Nat.dvd_of_mod_eq_zero rfl
  · exact Nat.even_iff.mpr rfl

/-
# refine
-/
example {p q : Prop} (h1 : p → q) (h2 : q → p) : p ↔ q := by
  refine ⟨h1, h2⟩

example {p q r t : Prop} (h1 : q) (h2 : r) (h3 : t) : (((p ∨ q) ∧ r) ∨ p) ∧ t := by
  refine ⟨?_, h3⟩
  left
  refine ⟨by right; exact h1, h2⟩

#check ne_of_lt
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · intro h
    push_neg at h
    refine ⟨h.1, ?_⟩
    apply ne_of_lt
    exact h.2
  intro h
  refine ⟨h.1, ?_⟩
  push_neg
  apply lt_of_le_of_ne h.1 h.2


/-
# calc
-/

example (a b : ℝ) : - 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2 := by
    calc
        a ^ 2 + 2 * a * b + b ^ 2 = (a + b) ^ 2 := by ring
        _ ≥ 0 := pow_two_nonneg (a + b)
  calc
    - 2 * a * b = - 2 * a * b + 0 := by ring
    _ ≤ - 2 * a * b + (a ^ 2 + 2 * a * b + b ^ 2) := (add_le_add_iff_left (- 2 * a * b)).2 h
    _ = a ^ 2 + b ^ 2 := by ring

example (a b c : ℝ) : a * b + a * c + b * c ≤ a * a + b * b + c * c := by
  have h : a * a + b * b + c * c - (a * b + a * c + b * c) ≥ 0 := by
    calc
      _ = (1 / 2) * (2 * a * a + 2 * b * b + 2 * c * c - 2 * a * b - 2 * a * c - 2 * b * c) := by ring
      _ = (1 / 2) * ((a * a - 2 * a * b + b * b) + (b * b - 2 * b * c + c * c) + (a * a - 2 * a * c + c * c)) := by ring
      _ = (1 / 2) * ((a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2) := by ring
      _ ≥ 0 := by linarith [pow_two_nonneg (a - b), pow_two_nonneg (b - c), pow_two_nonneg (a - c)]
  linarith

example {x y ε : ℝ} (epos : 0 < ε) (ele1 : ε ≤ 1) (xlt : |x| < ε) (ylt : |y| < ε) : |x * y| < ε := by
  calc
    |x * y| = |x| * |y| := by apply abs_mul
    _ ≤ |x| * ε := by
        apply mul_le_mul
        linarith
        linarith
        apply abs_nonneg
        apply abs_nonneg
    _ < 1 * ε := by
      rw [mul_lt_mul_right epos]
      linarith
    _ = ε := by apply one_mul
