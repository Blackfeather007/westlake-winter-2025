import Mathlib.Tactic

section ext

/- `@[ext]` attribute automatically create ext lemmas-/
@[ext]
structure myPoint : Type where
  x : Nat
  y : Nat

#check myPoint.ext
#check myPoint.ext_iff

example {a b : myPoint} (h1 : a.x = b.x) (h2 : a.y = b.y) : a = b := by
  ext <;> assumption

example (G H : Type) [Group G] [Group H] (φ ψ : G →* H)
    (h : ∀ a, φ a = ψ a) : φ = ψ := by
  ext g
  apply h

example (G H : Type) [Group G] [Group H] (φ ψ : G →* H)
    (h : ∀ a, φ a = ψ a) : φ = ψ := by
  apply MonoidHom.ext h

/- Other extensionality-/
#check Set.ext
#check funext

#check Matrix.ext

def test_matrix (n m : Nat) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of (fun (i : Fin n) (j : Fin m) => i + j)

#check (test_matrix 3 3)
#eval (test_matrix 3 3)

theorem test_matrix_thm : test_matrix 3 3 = !![0, 1, 2; 1, 2, 3; 2, 3, 4] := by
  unfold test_matrix
  ext i j
  fin_cases i, j <;> simp <;> norm_num

end ext

section congr

example (f : ℝ → ℝ) {x y : ℝ} (h : x = y) : f x = f y := by
  congr

example (f : ℝ → ℝ) {x y : ℝ} : f (x + y) = f (y + x) := by
  congr 1
  sorry

example (f g : ℝ → ℝ) {x y : ℝ} : f (g (x + y)) = f (g (y + x)) := by
  congr 2
  sorry

#check congr
#check congrArg
#check congrFun

-- @[congr]
#check Finset.sum_congr

#check List.zipWith
theorem ofDigits_eq_sum_map_with_index_aux (b : ℕ) (l : List ℕ) :
    ((List.range l.length).zipWith ((fun i a : ℕ => a * b ^ (i + 1))) l).sum =
      b * ((List.range l.length).zipWith (fun i a => a * b ^ i) l).sum := by
  suffices
    (List.range l.length).zipWith (fun i a : ℕ => a * b ^ (i + 1)) l =
      (List.range l.length).zipWith (fun i a => b * (a * b ^ i)) l
    by simp [this]
  congr; ext; simp [pow_succ]; ring

end congr

section symm

example {a b : Nat} (h : a = b) : b = a := by
  symm
  assumption

example {a b : Type*} (h : a ≃ b) : b ≃ a := by
  symm at h
  assumption

end symm

section trans

example {a b c : Nat} (h1 : a = b) (h2 : b = c) : a = c := by
  trans b
  · exact h1
  · exact h2

-- you can try this for `⊆` and lattice of Subgroup
example {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  trans
  · exact h1
  · exact h2

example {p q r : Prop} (h1 : p → q) (h2 : q → r) : p → r := by
  transitivity
  · exact h1
  · exact h2

end trans

section Repeat

example {x : ℝ} (h1 : (x - 1) * (x - 2) * (x - 3) = 0) :
  x = 1 ∨ x = 2 ∨ x = 3
:= by
  obtain h2 | _ := mul_eq_zero.mp h1
  · obtain _ | _ := mul_eq_zero.mp h2
    · left
      linarith
    · right
      left
      linarith
  · right
    right
    linarith

example {x : ℝ} (h1 : (x - 1) * (x - 2) * (x - 3) = 0) :
    x = 1 ∨ x = 2 ∨ x = 3 := by
  rwa [mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero, or_assoc] at h1

example {x : ℝ} (h1 : (x - 1) * (x - 2) * (x - 3) = 0) :
    x = 1 ∨ x = 2 ∨ x = 3 := by
  repeat rw [mul_eq_zero] at h1
  repeat rw [sub_eq_zero] at h1
  tauto

example {p : Prop} : p ∨ p ∨ p ∨ p ∨ p → p := by
  intro h
  cases h with
  | inl h => assumption
  | inr h => cases h with
    | inl h => assumption
    | inr h => cases h with
      | inl h => assumption
      | inr h => cases h with
        | inl h => assumption
        | inr h => assumption

example {p : Prop} : p ∨ p ∨ p ∨ p ∨ p → p := by
  intro h
  repeat cases h with
  | inl h => assumption
  | inr h => _
  assumption

def l1 := [1, 2, 3, 4]
def l2 := [5, 6, 7, 8]
example (x y : Nat) (hx : x ∈ l1) (hy : y ∈ l2) : x < y := by
  rw [l1, l2] at *
  simp at *
  rcases hx with rfl | rfl | rfl | rfl <;>
  rcases hy with rfl | rfl | rfl | rfl
  all_goals norm_num

end Repeat

section conv

/-
Find more information about `conv` tactic at
https://leanprover-community.github.io/extras/conv.html
-/

example (a b c : ℕ) : a * (b * c) = a * (c * b) := by
  sorry

example (b c : ℕ) : (b * c) * (b * c) * (b * c) = (b * c) * (c * b) * (c * b) := by
  conv =>
    enter [1, 1, 2]
    rw [mul_comm]
  conv =>
    enter [2, 2]
    rw [mul_comm]

example (b c : ℕ) : (b * c) * (b * c) * (b * c) = (b * c) * (c * b) * (c * b) := by
  conv in (occs := 2 3) (b * c) =>
    · rw [mul_comm]
    · rw [mul_comm]

example {P : Prop} {Q : Prop → Prop} {x : Nat}
    (h1 : Q (P ∧ x = 3)) : Q (P ∧ 3 = x) := by
  conv at h1 =>
    enter [1, 2]
    rw [Eq.comm]
  apply h1

end conv
