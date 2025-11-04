import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases abs_cases x with ⟨h1,h2⟩ | ⟨h1,h2⟩
  . rw [h1]
  . linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases abs_cases x with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> linarith

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases abs_cases x with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
  rcases abs_cases y with ⟨h3,h4⟩ | ⟨h3,h4⟩ <;>
  rcases abs_cases (x + y) with ⟨h5,h6⟩ | ⟨h5,h6⟩ <;>
  linarith

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  . intro h
    rcases abs_cases x with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
    . rcases abs_cases y with ⟨h3,h4⟩ | ⟨h3,h4⟩
      left
      linarith
      right
      linarith
  . intro h
    rcases h with h | h <;>
    rcases abs_cases y with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
    linarith

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  . intro h
    rcases abs_cases x with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> constructor <;> linarith
  . intro ⟨h1, h2⟩
    rcases abs_cases x with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨a, b, h1, h2⟩ <;> linarith [pow_two_nonneg a, pow_two_nonneg b]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x + 1) * (x - 1) = 0 := by
    calc
      (x + 1) * (x - 1)
      _ = x * x - 1     := by linarith
      _ = 0             := by
        rw [← pow_two, sub_eq_zero]
        exact h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  right
  linarith
  left
  linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x + y) * (x - y) = 0 := by
    calc
      (x + y) * (x - y)
      _ = x * x - y * y := by linarith
      _ = 0 := by
        rw [← pow_two, ← pow_two, sub_eq_zero]
        exact h

  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  right
  linarith
  left
  linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x + 1) * (x - 1) = 0 := by
    calc
      (x + 1) * (x - 1)
      _ = x * x - 1     := by ring
      _ = 0             := by
        rw [← pow_two, sub_eq_zero]
        assumption
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  right
  apply add_eq_zero_iff_eq_neg.mp at h
  assumption
  left
  rw [sub_eq_zero] at h
  assumption

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have := by calc
    (x + y) * (x - y)
    _ = x * x - y * y := by ring
    _ = 0 := by
      rw [pow_two, pow_two, ← sub_eq_zero] at h
      assumption

  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  . right
    exact add_eq_zero_iff_eq_neg.mp h
  . left
    exact sub_eq_zero.mp h

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  . intro h
    by_cases p: P
    . right
      exact h p
    . left
      assumption
  . intro h p
    cases h
    . contradiction
    . assumption
