import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply inf_comm

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply inf_assoc

example : x ⊔ y = y ⊔ x := by
  apply sup_comm

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply sup_assoc

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm inf_le_left (le_inf (le_refl x) le_sup_left)

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm (sup_le (le_refl x) inf_le_left) le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  calc
    a ⊔ b ⊓ c = a ⊔ a ⊓ c ⊔ b ⊓ c         := by rw [sup_inf_self]
    _         = a ⊔ (a ⊔ b) ⊓ c           := by rw [inf_comm a c, inf_comm b c, sup_assoc, ← h, inf_comm]
    _         = (a ⊔ b) ⊓ a ⊔ (a ⊔ b) ⊓ c := by rw [← inf_comm a, inf_sup_self]
    _         = (a ⊔ b) ⊓ (a ⊔ c)         := by rw [← h]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  calc
    a ⊓ (b ⊔ c) = a ⊓ (a ⊔ c) ⊓ (b ⊔ c)     := by rw [inf_sup_self]
    _           = a ⊓ (a ⊓ b ⊔ c)           := by rw [sup_comm a c, sup_comm b c, inf_assoc, ← h, ← sup_comm]
    _           = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by rw [← sup_comm a, sup_inf_self]
    _           = a ⊓ b ⊔ a ⊓ c             := by rw [← h]

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  have h₁ := add_le_add_right h (-a)
  rw [add_neg_cancel, ← sub_eq_add_neg] at h₁
  exact h₁

example (h: 0 ≤ b - a) : a ≤ b := by
  have h₁ := add_le_add_right h a
  rw [zero_add, sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero] at h₁
  exact h₁

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  rw [← add_zero (a * c)]
  apply add_le_of_le_sub_left
  rw [← mul_sub_right_distrib]
  apply mul_nonneg
  . apply le_sub_right_of_add_le
    rw [zero_add]
    exact h
  . exact h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ dist x y * 2 := by
    rw [mul_two, ← dist_self x]
    nth_rewrite 3 [dist_comm]
    exact dist_triangle x y x
  apply nonneg_of_mul_nonneg_left h zero_lt_two

end
